(ns lang.compile.struct
  "Compiles struct type ASTs into parser closures (spec 5.2-5.5, 5.8).

  A parser is (fn [ctx cur env] -> Res | nil). `cur` is a Cur: the byte source,
  the current offset, and the end of the current window. Offsets are absolute
  within the source, which is also the frame: `:decode` (Task 16) opens a new
  frame by parsing over a new source. env maps field, param and position ids
  to values. Expressions are evaluated directly, never through eval-code: the
  outermost caller owns the call budget.

  The struct table is one atom {qname compiled} shared by structs and
  deftypes. An entry is {:qname :arity :kind (:struct|:deftype)
  :parse* (fn [ctx cur args] -> Res | nil)}; structs also carry :parse.
  Callers register entries with swap!; references resolve at parse time, so
  recursive structs work."
  (:require [clojure.walk :as walk]
            [lang.analyze.struct :as as]
            [lang.builtins.bytes :as bb]
            [lang.compile.code :as cc]
            [lang.errors :refer [error!]]
            [lang.resource :as res]
            [lang.runtime :as rt]
            [lang.values :as v])
  (:import (java.math BigInteger)
           (lang.values Bytes)))

(set! *warn-on-reflection* true)

(defrecord Cur [src ^long off ^long lim ^long bit-left ^long bit-buf])
(defrecord Res [value cur])

(defn- mk-cur ^Cur [src ^long off ^long lim] (->Cur src off lim 0 0))

(defn- realign
  "Drops the unread bits of a partially consumed byte (spec 5.4 bit fields)."
  ^Cur [^Cur cur]
  (if (zero? (.-bit-left cur)) cur (->Cur (.-src cur) (.-off cur) (.-lim cur) 0 0)))

(def ^:private none ::none)
(defn- none? [x] (identical? x none))
(defn- present [x] (if (none? x) nil x))

;; ---------------------------------------------------------------- explain

(def ^:dynamic *explain*
  "Bound only during explain-parse to {:path volatile :fail volatile}."
  nil)

(defn- fail!
  "Records a parse failure (when explaining) and returns nil."
  [reason ^long off]
  (when-let [e *explain*]
    (vreset! (:fail e) {:reason reason :offset off :path @(:path e)}))
  nil)

(defn- push-path! [k]
  (when-let [e *explain*] (vswap! (:path e) conj k)))

(defn- pop-path! []
  (when-let [e *explain*] (vswap! (:path e) pop)))

;; ---------------------------------------------------------------- reading

(defn- fail-read [ctx cur]
  (when *explain*
    (let [{:keys [src off lim]} cur]
      (fail! (if (< (long lim) (long (res/src-size src ctx))) :window :eof) off))))

(defn- read-n
  "n bytes at the cursor, or nil (recording :eof/:window) when they do not fit
  in the window."
  ^Bytes [ctx cur ^long n]
  (let [{:keys [src ^long off ^long lim]} cur]
    (if (and (>= n 0) (<= n (- lim off)))
      (or (res/src-read src ctx off n) (fail-read ctx cur))
      (fail-read ctx cur))))

(defn- advance ^Cur [^Cur cur ^long n]
  (mk-cur (.-src cur) (+ (.-off cur) n) (.-lim cur)))

(defn- size!
  "Size/count/offset expression result: a non-negative long, or nil for a nil,
  negative or out-of-range value (a parse failure). Non-integers are program
  errors."
  [x]
  (cond
    (nil? x) nil
    (not (integer? x)) (error! :type-error :run "Expected an integer size, count or offset"
                               {:value x})
    (and (instance? Long x) (>= (long x) 0)) x
    :else nil))

(defn- bad-size [^Cur cur] (fail! :bad-size (.-off cur)))

(defn- sign-extend ^long [^long x ^long n]
  (let [s (- 64 (* 8 n))]
    (bit-shift-right (bit-shift-left x s) s)))

(defn- raw-int
  "Unsigned n-byte value of b as a (possibly wrapped) long."
  ^long [^Bytes b ^long n be?]
  (loop [i 0 acc 0]
    (if (< i n)
      (recur (inc i)
             (bit-or (bit-shift-left acc 8)
                     (long (v/bget b (if be? i (- n 1 i))))))
      acc)))

(def ^:private prim-widths
  {:u8 1 :i8 1 :u16 2 :i16 2 :u32 4 :i32 4 :u64 8 :i64 8 :f32 4 :f64 8})

(defn- decode-prim [prim ^long x]
  (case prim
    (:u8 :u16 :u32) x
    :i8 (sign-extend x 1)
    :i16 (sign-extend x 2)
    :i32 (sign-extend x 4)
    :i64 x
    :u64 (if (neg? x) (v/canon-num (BigInteger. (Long/toUnsignedString x))) x)
    :f32 (v/canon-num (double (Float/intBitsToFloat (unchecked-int x))))
    :f64 (v/canon-num (Double/longBitsToDouble x))))

(defn- compile-prim [{:keys [prim endian]}]
  (let [n (long (prim-widths prim))
        be? (= endian :be)]
    (fn [ctx ^Cur cur _]
      (when-let [b (read-n ctx cur n)]
        (->Res (decode-prim prim (raw-int b n be?)) (advance cur n))))))

(defn- unit [enc] (if (#{:utf16le :utf16be} enc) 2 1))

(defn- trim-nuls ^String [^String s]
  (loop [n (.length s)]
    (if (and (pos? n) (== 0 (int (.charAt s (dec n)))))
      (recur (dec n))
      (.substring s 0 n))))

(def ^:private cstring-chunk 256)

(defn- find-nul
  "Offset (from the cursor) of the first NUL code unit within the first max
  bytes of the window, or nil."
  [ctx ^Cur cur ^long max-len enc]
  (let [u (long (unit enc))
        avail (min max-len (- (.-lim cur) (.-off cur)))]
    (loop [pos 0]
      (let [n (min (long cstring-chunk) (- avail pos))
            n (- n (rem n u))]
        (when (pos? n)
          (let [^Bytes chunk (res/src-read (.-src cur) ctx (+ (.-off cur) pos) n)
                hit (when chunk
                      (loop [i 0]
                        (when (<= (+ i u) n)
                          (if (loop [j 0]
                                (or (== j u) (and (zero? (long (v/bget chunk (+ i j)))) (recur (inc j)))))
                            i
                            (recur (+ i u))))))]
            (cond (nil? chunk) nil
                  hit (+ pos (long hit))
                  :else (recur (+ pos n)))))))))

;; ---------------------------------------------------------------- types

(declare compile-type)

(defn- compile-bytes [{:keys [n]} fn-table]
  (if (= :rest n)
    (fn [ctx ^Cur cur _]
      (when-let [b (read-n ctx cur (- (.-lim cur) (.-off cur)))]
        (->Res b (mk-cur (.-src cur) (.-lim cur) (.-lim cur)))))
    (let [ne (cc/compile-node n fn-table)]
      (fn [ctx ^Cur cur env]
        (if-some [k (size! (ne ctx env))]
          (when-let [b (read-n ctx cur k)]
            (->Res b (advance cur k)))
          (bad-size cur))))))

(defn- compile-string [{:keys [n enc]} fn-table]
  (let [ne (cc/compile-node n fn-table)]
    (fn [ctx ^Cur cur env]
      (if-some [k (size! (ne ctx env))]
        (when-let [b (read-n ctx cur k)]
          (rt/check-size! ctx k)
          (if-some [s (bb/decode-bytes enc b)]
            (->Res (trim-nuls s) (advance cur k))
            (fail! :encoding (.-off cur))))
        (bad-size cur)))))

(defn- compile-cstring [{:keys [enc max]}]
  (let [u (long (unit enc))]
    (fn [ctx ^Cur cur _]
      (if-some [i (find-nul ctx cur max enc)]
        (let [i (long i)]
          (if-some [s (bb/decode-bytes enc (res/src-read (.-src cur) ctx (.-off cur) i))]
            (->Res s (advance cur (+ i u)))
            (fail! :encoding (.-off cur))))
        (fail! :cstring (.-off cur))))))

(defn- compile-const [{:keys [bytes val]}]
  (let [expected (vec bytes)
        n (count expected)]
    (fn [ctx ^Cur cur _]
      (when-let [b (read-n ctx cur n)]
        (if (loop [i 0]
              (or (== i n) (and (== (long (v/bget b i)) (long (expected i))) (recur (inc i)))))
          (->Res val (advance cur n))
          (fail! :const (.-off cur)))))))

(defn- compile-array [{:keys [elem n]} struct-table fn-table]
  (let [ep (compile-type elem struct-table fn-table)
        ne (cc/compile-node n fn-table)]
    (fn [ctx cur env]
      (if-some [k (size! (ne ctx env))]
        (loop [i 0 cur cur out (transient [])]
          (if (< i (long k))
            (do
              (rt/charge! ctx 1)
              (push-path! i)
              (let [r (ep ctx cur env)]
                (pop-path!)
                (when r
                  (recur (inc i) (:cur r) (conj! out (present (:value r)))))))
            (->Res (persistent! out) cur)))
        (bad-size cur)))))

(defn- compile-repeat [{:keys [elem mode pred max]} struct-table fn-table]
  (let [ep (compile-type elem struct-table fn-table)
        pe (when pred (cc/compile-node pred fn-table))
        max (long max)]
    (fn [ctx cur env]
      (let [pf (when pe (pe ctx env))]
        (loop [i 0 cur cur out (transient [])]
          (if (and (= :eos mode) (>= (long (:off cur)) (long (:lim cur))))
            (->Res (persistent! out) cur)
            (if (>= i (if (= :sentinel mode) (inc max) max))
              (fail! :repeat-max (:off cur))
              (do
              (rt/charge! ctx 1)
              (push-path! i)
              (let [r (ep ctx cur env)]
                (pop-path!)
                (when r
                  (let [nxt (:cur r)
                        x (present (:value r))]
                    (if (== (long (:off nxt)) (long (:off cur)))
                      (fail! :zero-progress (:off cur))
                      (let [done? (and pf (v/apply-fn ctx pf [x]))
                            kept (if (and done? (= :sentinel mode)) i (inc i))]
                        (cond
                          (> kept max) (fail! :repeat-max (:off cur))
                          done? (->Res (persistent! (if (= :sentinel mode) out (conj! out x))) nxt)
                          :else (recur (inc i) nxt (conj! out x))))))))))))))))

(defn- compile-if [{:keys [test then]} struct-table fn-table]
  (let [te (cc/compile-node test fn-table)
        tp (compile-type then struct-table fn-table)]
    (fn [ctx cur env]
      (if (te ctx env) (tp ctx cur env) (->Res none cur)))))

(defn- compile-switch [{:keys [test cases default]} struct-table fn-table]
  (let [te (cc/compile-node test fn-table)
        table (into {} (map (fn [[k t]] [k (compile-type t struct-table fn-table)])) cases)
        dp (when default (compile-type default struct-table fn-table))]
    (fn [ctx cur env]
      (let [p (or (get table (te ctx env)) dp)]
        (if p (p ctx cur env) (fail! :switch (:off cur)))))))

(defn- compile-enum [{:keys [elem map]} struct-table fn-table]
  (let [ep (compile-type elem struct-table fn-table)]
    (fn [ctx cur env]
      (when-let [r (ep ctx cur env)]
        (let [x (:value r)]
          (->Res (get map x x) (:cur r)))))))

(defn- compile-align [{:keys [n]} fn-table]
  (let [ne (cc/compile-node n fn-table)]
    (fn [ctx ^Cur cur env]
      (let [k (size! (ne ctx env))]
        (if (and k (pos? (long k)))
          (let [k (long k)
                off (.-off cur)
                pad (mod (- k (mod off k)) k)]
            (when (read-n ctx cur pad)
              (->Res nil (advance cur pad))))
          (bad-size cur))))))

(defn- compile-skip [{:keys [n]} fn-table]
  (let [ne (cc/compile-node n fn-table)]
    (fn [ctx ^Cur cur env]
      (if-some [k (size! (ne ctx env))]
        (when (read-n ctx cur k)
          (->Res nil (advance cur k)))
        (bad-size cur)))))

(defn- compile-at [{:keys [off elem]} struct-table fn-table]
  (let [oe (cc/compile-node off fn-table)
        ep (compile-type elem struct-table fn-table)]
    (fn [ctx ^Cur cur env]
      (if-some [o (size! (oe ctx env))]
        (let [size (long (res/src-size (.-src cur) ctx))]
          (if (> (long o) size)
            (fail! :eof o)
            (when-let [r (ep ctx (mk-cur (.-src cur) o size) env)]
              (->Res (:value r) cur))))
        (bad-size cur)))))

(defn- compile-sized [{:keys [n elem]} struct-table fn-table]
  (let [ne (cc/compile-node n fn-table)
        ep (compile-type elem struct-table fn-table)]
    (fn [ctx ^Cur cur env]
      (if-some [k (size! (ne ctx env))]
        (if (<= (long k) (- (.-lim cur) (.-off cur)))
          (when-let [r (ep ctx (mk-cur (.-src cur) (.-off cur) (+ (.-off cur) (long k))) env)]
            (->Res (:value r) (advance cur k)))
          (fail! :window (.-off cur)))
        (bad-size cur)))))

(defn- compile-try [{:keys [elem]} struct-table fn-table]
  (let [ep (compile-type elem struct-table fn-table)]
    (fn [ctx cur env]
      (or (ep ctx cur env) (->Res none cur)))))

(defn- compile-ref
  "A struct reference or deftype alias: evaluates args in the caller env and
  runs the target's :parse* over the current cursor."
  [{:keys [qname args]} struct-table fn-table]
  (let [arg-fns (mapv #(cc/compile-node % fn-table) args)]
    (fn [ctx cur env]
      (let [target (or (get @struct-table qname)
                       (error! :internal-error :run "Undefined struct" {:struct qname}))]
        ((:parse* target) ctx cur (mapv #(% ctx env) arg-fns))))))


(defn- compile-bits
  "Reads n bits from the shared bit cursor. The cursor sits just past the byte
  being consumed, with bit-left unread bits of it held in bit-buf.
  Policy: only types that read whole bytes realign (see compile-type).
  Transparent wrappers (:if, :switch, :array, :repeat, :try, :enum, :ref,
  :alias) do not, so bit fields continue through conditionals and arrays."
  [{:keys [n order]}]
  (let [n (long n)
        msb? (= order :msb)]
    (fn [ctx ^Cur cur _]
      (loop [need n got 0 acc 0 ^Cur cur cur]
        (if (zero? need)
          (->Res (if (neg? acc) (decode-prim :u64 acc) acc) cur)
          (let [left (.-bit-left cur)
                buf (.-bit-buf cur)]
            (if (zero? left)
              (when-let [b (read-n ctx cur 1)]
                (recur need got acc
                       (->Cur (.-src cur) (inc (.-off cur)) (.-lim cur) 8 (long (v/bget b 0)))))
              (let [k (min need left)
                    mask (dec (bit-shift-left 1 k))
                    chunk (if msb?
                            (bit-and (bit-shift-right buf (- left k)) mask)
                            (bit-and (bit-shift-right buf (- 8 left)) mask))]
                (recur (- need k) (+ got k)
                       (if msb?
                         (bit-or (bit-shift-left acc k) chunk)
                         (bit-or acc (bit-shift-left chunk got)))
                       (->Cur (.-src cur) (.-off cur) (.-lim cur) (- left k) buf))))))))))

(defn- size-or-rest-fn
  "(fn [ctx cur env]) -> non-negative size, or nil, for an n expression or :rest."
  [n fn-table]
  (if (= :rest n)
    (fn [_ ^Cur cur _] (- (.-lim cur) (.-off cur)))
    (let [ne (cc/compile-node n fn-table)]
      (fn [ctx _ env] (size! (ne ctx env))))))

(defn- compile-decode [{:keys [n f elem]} struct-table fn-table]
  (let [nf (size-or-rest-fn n fn-table)
        fe (cc/compile-node f fn-table)
        ep (compile-type elem struct-table fn-table)]
    (fn [ctx ^Cur cur env]
      (if-some [k (nf ctx cur env)]
        (when-let [b (read-n ctx cur k)]
          (let [out (v/apply-fn ctx (fe ctx env) [b])]
            (if (v/bytes-val? out)
              (let [size (v/bsize out)]
                (rt/alloc-bytes! ctx size)
                (when-let [r (ep ctx (mk-cur out 0 size) env)]
                  (->Res (:value r) (advance cur k))))
              (fail! :decode (.-off cur)))))
        (bad-size cur)))))

(defn- type-id-of
  "Stable identity of a type AST: the qname of a named type, else the AST
  itself with function values blanked."
  [T]
  (or (:qname T)
      (walk/postwalk #(if (fn? %) :fn %) T)))

(defn- local-ids
  "Ids of every local referenced anywhere in an AST."
  [T]
  (vec (distinct (keep #(when (and (map? %) (= :local (:op %))) (:id %))
                       (tree-seq coll? seq T)))))

(defn- compile-defer [{:keys [n elem] :as T} struct-table fn-table]
  (let [nf (size-or-rest-fn n fn-table)
        ep (compile-type elem struct-table fn-table)
        arg-fns (mapv #(cc/compile-node % fn-table) (:args elem))
        qname (:qname elem)
        tid (type-id-of elem)
        ids (if (:qname elem) [] (local-ids elem))]
    (fn [ctx ^Cur cur env]
      (if-some [k (nf ctx cur env)]
        (let [k (long k)]
          (if (<= k (- (.-lim cur) (.-off cur)))
            (let [src (.-src cur)
                  off (.-off cur)
                  args (into (mapv #(% ctx env) arg-fns) (map env) ids)
                  force-fn (fn [ctx]
                             (rt/trace! ctx {:event :parse :type qname :off off})
                             (when-let [r (ep ctx (mk-cur src off (+ off k)) env)]
                               (present (:value r))))]
              (->Res (v/->Deferred (res/src-id src) src off k [tid args] force-fn args)
                     (advance cur k)))
            (fail-read ctx cur)))
        (bad-size cur)))))

(defn- compile-type*
  [T struct-table fn-table]
  (case (:t T)
    :prim (compile-prim T)
    :bytes (compile-bytes T fn-table)
    :string (compile-string T fn-table)
    :cstring (compile-cstring T)
    :const (compile-const T)
    :array (compile-array T struct-table fn-table)
    :repeat (compile-repeat T struct-table fn-table)
    :if (compile-if T struct-table fn-table)
    :switch (compile-switch T struct-table fn-table)
    :enum (compile-enum T struct-table fn-table)
    :calc (let [e (cc/compile-node (:expr T) fn-table)]
            (fn [ctx cur env] (->Res (e ctx env) cur)))
    :assert (let [e (cc/compile-node (:expr T) fn-table)]
              (fn [ctx cur env]
                (if (e ctx env) (->Res true cur) (fail! :assert (:off cur)))))
    :skip (compile-skip T fn-table)
    :align (compile-align T fn-table)
    :at (compile-at T struct-table fn-table)
    :sized (compile-sized T struct-table fn-table)
    :try (compile-try T struct-table fn-table)
    (:ref :alias) (compile-ref T struct-table fn-table)
        :bits (compile-bits T)
    :decode (compile-decode T struct-table fn-table)
    :defer (compile-defer T struct-table fn-table)))

(def ^:private transparent
  "Types that pass the cursor through to their children (or are bit fields
  themselves) and so must not realign before running."
  #{:bits :array :repeat :enum :try :ref :alias :if :switch})

(defn compile-type
  "Compiles a type AST into a parser (fn [ctx cur env] -> Res | nil). Every
  type but :bits realigns a partially consumed byte first."
  [T struct-table fn-table]
  (let [p (compile-type* T struct-table fn-table)]
    (if (transparent (:t T))
      p
      (fn [ctx cur env] (p ctx (realign cur) env)))))

;; ---------------------------------------------------------------- definitions

(defn- check-arity! [qname expected args]
  (when-not (= expected (count args))
    (error! :internal-error :run "Wrong number of struct arguments" {:struct qname})))

(defn- compile-field [field struct-table fn-table]
  (assoc field
         :parser (compile-type (:type field) struct-table fn-table)
         :path-key (keyword (name (:sym field)))
         :emit? (boolean (and (:key field) (not (:hidden? field))))))

(defn- top-parse
  "Runs (parse-cur cur) -> Res | nil over src from off. Returns
  {:value :end} or nil; a bad offset is an :eof failure."
  [ctx src off qname parse-cur]
  (let [size (long (res/src-size src ctx))]
    (if (and (instance? Long off) (<= 0 (long off) size))
      (do
        (rt/trace! ctx {:event :parse :type qname :off off})
        (when-let [r (parse-cur (mk-cur src off size))]
          {:value (present (:value r)) :end (:off (:cur r))}))
      (fail! :eof (if (instance? Long off) off 0)))))

(defn compile-struct
  "Compiles an analyzed struct. Returns {:qname :arity :kind :parse* :parse};
  :parse is (fn [ctx src off args] -> {:value :end} | nil)."
  [{:keys [qname params fields pos-ids]} struct-table fn-table]
  (let [arity (count params)
        param-ids (mapv :id params)
        fields (mapv #(compile-field % struct-table fn-table) fields)
        {pos-id :pos start-id :start rem-id :remaining} pos-ids
        parse*
        (fn [ctx cur args]
          (check-arity! qname arity args)
          (rt/with-depth ctx
            (fn []
              (let [cur (realign cur)
                    start (:off cur)
                    lim (long (:lim cur))]
                (loop [[f & more :as fs] (seq fields)
                       cur cur
                       env (zipmap param-ids args)
                       out {}]
                  (if (nil? fs)
                    (->Res out (realign cur))
                    (do
                      (rt/charge! ctx 1)
                      (let [off (:off cur)
                            env (assoc env pos-id off start-id start rem-id (- lim (long off)))]
                        (push-path! (:path-key f))
                        (let [r ((:parser f) ctx cur env)]
                          (pop-path!)
                          (when r
                            (let [x (:value r)]
                              (recur more (:cur r)
                                     (assoc env (:id f) (present x))
                                     (if (and (:emit? f) (not (none? x)))
                                       (assoc out (:key f) x)
                                       out)))))))))))))]
    {:qname qname
     :arity arity
     :kind :struct
     :parse* parse*
     :parse (fn [ctx src off args]
              (top-parse ctx src off qname #(parse* ctx % args)))}))

(defn compile-deftype
  "Compiles an analyzed deftype alias. Returns {:qname :arity :kind :parse*}.
  Its params are bound in a fresh env, so the aliased type sees only them."
  [{:keys [qname params type]} struct-table fn-table]
  (let [arity (count params)
        param-ids (mapv :id params)
        p (compile-type type struct-table fn-table)]
    {:qname qname
     :arity arity
     :kind :deftype
     :parse* (fn [ctx cur args]
               (check-arity! qname arity args)
               (rt/with-depth ctx #(p ctx cur (zipmap param-ids args))))}))

;; ---------------------------------------------------------------- explain / relation

(defn explain-parse
  "Parses and reports why it failed: {:ok true :value :end} or
  {:ok false :path [...] :offset n :reason kw}."
  [ctx compiled src off args]
  (let [e {:path (volatile! []) :fail (volatile! nil)}
        r (binding [*explain* e]
            ((:parse compiled) ctx src off args))]
    (if r
      (assoc r :ok true)
      (merge {:ok false :path [] :offset off :reason :eof} @(:fail e)))))

(defn struct-relation
  "A computed relation entry for a named struct: [src off arg… value end].
  The single mode binds every input; its :impl is
  (fn [ctx in-vals]) with in-vals [src off & args], returning [[value end]]
  or []. A nil src or off yields no tuples. Results are memoized per run."
  [compiled]
  (let [{:keys [qname arity]} compiled
        total (+ 4 arity)]
    {:qname qname
     :arity total
     :memo? false
     :modes [{:in (vec (range (- total 2)))
              :out [(- total 2) (- total 1)]
              :impl (fn [ctx [src off & args]]
                      (cond
                        (or (nil? src) (nil? off)) []
                        (not (satisfies? res/ByteSource src))
                        (error! :type-error :run "Expected bytes or a handle" {:value src})
                        (not (integer? off))
                        (error! :type-error :run "Expected an integer offset" {:value off})
                        :else
                        (let [args (vec args)
                              k [qname (res/src-id src) off args]
                              hit (rt/memo-get ctx k)]
                          (if (identical? hit :lang.runtime/miss)
                            (rt/memo-put! ctx k
                                          (if-let [r ((:parse compiled) ctx src off args)]
                                            [[(:value r) (:end r)]]
                                            []))
                            hit))))}]}))

;; ---------------------------------------------------------------- parse in code

(defn compile-parse-node
  "Compiles a code :parse node (spec 5.8). The raw type form is analyzed here,
  in the scope captured by the analyzer, using the program from env
  ({:prog :struct-table}, see parse-env). Returns (fn [ctx code-env] ->
  {:value :end} | explain map | nil)."
  [{:keys [explain? type ns scope args]} {:keys [prog struct-table]} fn-table]
  (let [attrs (get-in prog [:namespaces ns :attrs])
        T (as/analyze-type prog ns type scope
                           (or (:endian attrs) :le) (or (:bit-order attrs) :msb))
        parser (compile-type T struct-table fn-table)
        [src-n off-n] (mapv #(cc/compile-node % fn-table) args)]
    (fn [ctx env]
      (let [src (src-n ctx env)
            off (if off-n (off-n ctx env) 0)]
        (cond
          (nil? src) nil
          (not (satisfies? res/ByteSource src))
          (error! :type-error :run "Expected bytes or a handle" {:value src})
          (nil? off) nil
          (not (integer? off))
          (error! :type-error :run "Expected an integer offset" {:value off})
          :else
          (let [compiled {:parse (fn [ctx src off _]
                                   (top-parse ctx src off (:qname T) #(parser ctx % env)))}]
            (if explain?
              (explain-parse ctx compiled src off [])
              ((:parse compiled) ctx src off []))))))))

(defn parse-env
  "The value to bind lang.compile.code/*compile-env* to while compiling code
  that may contain `parse` forms."
  [prog struct-table]
  {:prog prog :struct-table struct-table :compile-parse compile-parse-node})
