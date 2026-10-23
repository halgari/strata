(ns lang.analyze.code-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.walk :as walk]
            [lang.analyze.code :as c]
            [lang.builtins :as b]
            [lang.ns :as ns]))

(defn- err [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (ex-data e))))

(defn- prog []
  (-> (ns/empty-program @b/registry {})
      (ns/add-namespace {:name 'a :attrs {} :requires []})
      (ns/add-def 'a 'f {:kinds #{:fn} :sub :defn :qname 'a/f :form '(defn f [x] x)})
      (ns/add-def 'a 'g {:kinds #{:fn} :sub :defn :qname 'a/g
                         :form '(defn g ([x] x) ([x y] x) ([x y & zs] x))})
      (ns/add-def 'a 'r {:kinds #{:relation} :sub :defrel :qname 'a/r
                         :form '(defrel r ...)})))

(defn- an
  ([form] (an form []))
  ([form local-syms]
   (let [scope (c/new-scope)
         scope (reduce (fn [s sym] (first (c/bind-local s sym))) scope local-syms)]
     (c/analyze (prog) 'a form scope))))

(defn- ops [n]
  (let [acc (atom #{})]
    (walk/postwalk (fn [x] (when (and (map? x) (:op x)) (swap! acc conj (:op x))) x) n)
    @acc))

(defn- kind [form & [locals]] (:lang/error (err #(an form (or locals [])))))

(deftest basic-ops
  (let [n (an '(if (pos? x) (inc x) 0) '[x])]
    (is (= :if (:op n)))
    (is (= :call-builtin (:op (:test n))))
    (is (= 'lang.core/pos? (:name (:test n))))
    (is (= :local (:op (first (:args (:test n))))))
    (is (= {:op :const :val 0} (select-keys (:else n) [:op :val]))))
  (is (= :call-defn (:op (an '(f 1)))))
  (is (= :fn-ref (:op (first (:args (an '(map inc [1])))))))
  (is (= :const (:op (an '[1 2 {:a "x"}]))))
  (is (= :vector (:op (an '[x 1] '[x]))))
  (is (= :const (:op (an '(quote (a b))))))
  (is (= :invoke (:op (an '(h 1) '[h]))))
  (is (= :and (:op (an '(and x y) '[x y]))))
  (is (= :case (:op (an '(case x 1 :a (2 3) :b :c) '[x])))))

(deftest canonical-consts
  (is (= 0.0 (:val (an -0.0))))
  (is (= lang.values/nan (:val (an ##NaN)))))

(deftest loc-on-nodes
  (let [form (with-meta '(inc x) {:line 3 :column 5})
        n (an form '[x])]
    (is (= {:line 3 :column 5} (:loc n)))
    (is (= {:line 3 :column 5} (:loc (first (:args n)))))))

(deftest desugar
  (let [n (an '(when-let [y (f x)] y) '[x])]
    (is (= #{:let :if :call-defn :local :const} (ops n))))
  (is (= #{:if :const :local} (ops (an '(cond x 1 y 2 :else 3) '[x y]))))
  (is (= #{:call-builtin :local :const} (ops (an '(-> x inc (+ 2)) '[x]))))
  (is (= 'lang.core/+ (:name (an '(-> x inc (+ 2)) '[x])))))

(deftest threading-last
  (let [n (an '(->> x (map inc)) '[x])]
    (is (= :local (:op (second (:args n)))))))

(deftest destructuring
  (let [n (an '(let [[a b & r] v {:keys [k]} m] [a k]) '[v m])
        impls (set (map :name (filter #(= :call-builtin (:op %))
                                      (tree-seq coll? seq n))))]
    (is (contains? impls 'lang.core/nth))
    (is (contains? impls 'lang.core/get))
    (is (contains? impls 'lang.core/subvec))
    (is (= :vector (:op (:body n)))))
  (is (some? (an '((fn [[a b] {:keys [c] :or {c 1}}] (+ a b c)) [1 2] {}))))
  (is (some? (an '(loop [[a & more] [1 2]] (if a (recur more) a))))))

(deftest fn-and-loop
  (let [n (an '(fn self [x & more] (recur x more)))]
    (is (= :fn (:op n)))
    (is (some? (:self n)))
    (is (some? (:rest (first (:arities n))))))
  (is (= :loop (:op (an '(loop [i 0] (if (< i 3) (recur (inc i)) i)))))))

(deftest tail-check
  (is (= :recur-not-tail (kind '(loop [i 0] (inc (recur i))))))
  (is (= :recur-not-tail (kind '(recur 1))))
  (is (= :recur-arity (kind '(loop [i 0] (recur i i)))))
  (is (= :recur-arity (kind '(fn [x] (recur)))))
  (is (some? (an '(loop [i 0] (let [j i] (if j (recur j) (do 1 (recur 0)))))))))

(deftest illegal-symbols
  (doseq [f '[(System/exit 0) (.length "x") (new Object) (clojure.core/eval 1)
              (def x 1) (throw 1) (set! x 1) Object]]
    (is (= :unresolved-symbol (kind f)) (pr-str f)))
  (is (= :unresolved-symbol (kind 'nope)))
  (is (= :unresolved-symbol (kind '(?x 1))))
  (is (some? (an '(inc ?x) '[?x]))))

(deftest relation-in-code
  (let [e (err #(an '(r 1)))]
    (is (= :relation-in-code (:lang/error e)))
    (is (= :analyze (:lang/phase e))))
  (is (= :relation-in-code (kind '(inc r)))))

(deftest kw-invoke
  (is (= :kw-invoke (:op (an '(:k m) '[m]))))
  (is (= :kw-invoke (:op (an '(:k m 0) '[m]))))
  (is (= :arity-error (kind '(:k)))))

(deftest static-arity
  (is (= :arity-error (kind '(f 1 2))))
  (is (= :arity-error (kind '(f))))
  (is (= :arity-error (kind '(inc 1 2))))
  (is (= :arity-error (kind '(g))))
  (is (some? (an '(g 1 2 3 4))))
  (is (= [[1 1]] (c/defn-arities '(defn f "doc" [x] x))))
  (is (= [[1 1] [2 2] [1 nil]] (c/defn-arities '(defn g ([x] 1) ([x y] 2) ([x & r] 3))))))

(deftest parse-node
  (let [n (an '(parse [:cstring :ascii] src 0) '[src])]
    (is (= :parse (:op n)))
    (is (= [:cstring :ascii] (:type n)))
    (is (= 'a (:ns n)))
    (is (= 2 (count (:args n))))
    (is (false? (:explain? n))))
  (is (true? (:explain? (an '(parse-explain T src) '[src])))))

(deftest unique-ids
  (let [n (an '(let [a 1 b 2] (fn [x] (let [y x] y))))
        ids (->> (tree-seq coll? seq n) (filter vector?) (keep #(when (integer? (first %)) (first %))))]
    (is (= (count ids) (count (set ids))))))
