# Design: A Datalog + Code Language for Declarative Parsing (working name `lang`)

Status: revision 2. It incorporates the adversarial review. Date: 2026-10-22

The language has no name yet. `lang` is a placeholder used in namespace names (`lang.core`, `lang.string`, …), and every occurrence will be renamed once a name is chosen. Candidates are listed in §11.

---

## 1. Purpose and scope

### 1.1 Intent

The language lets an application accept **parsers and rules as data**. A program is EDN, it is shipped alongside the application or to it, and the application runs it inside a sandbox. Programs are mostly declarative. They drop into imperative code only where a declarative formulation would be awkward, and the two styles interleave inside one source file.

The main workload is **parsing data formats, text and especially binary**, and then reasoning over the parsed results with rules. The design was validated against three real binary formats (§9): PE import tables, Skyrim plugin files (ESP, ESM, ESL), and Cyberpunk 2077 `.archive` (RDAR) headers.

### 1.2 Decisions made

| Topic | Decision |
|---|---|
| Host | Runs on the Clojure JVM (Clojure 1.12.x, JDK 27) and is embedded as a library. |
| Syntax | Read with `clojure.tools.reader/read` after a pre-scan that rejects Clojure-only syntax, so EDN-like rules apply: no `#(`, `#"`, `#'`, `#=`, `#?`, `#:`, `#!`, no `@`, backquote, `~`, `^` or `::`, no `'x` (write `(quote x)`), and no tagged literals. A leaf whitelist then rejects any other value in the read forms. |
| Evaluation model | A hybrid. **Rules** are evaluated bottom-up as Datalog: semi-naive fixpoint with stratified negation and aggregation. **Code relations** are mode-dispatched code, called from rule bodies once their inputs are bound. |
| Direction of calls | One way. Relations call code, and code never queries relations. |
| Code sublanguage | Interpreted, Clojure-like, with `loop`/`recur`, local `fn`s and `defn`. Values are immutable and there is no mutation. Fuel, size and depth budgets bound execution. |
| I/O | I/O exists **only in code**, as built-ins that resolve names against resources the host supplies. Rules never perform I/O themselves; users build relations on top of code that does. |
| Rule features in v1 | Joins, recursion, stratified `not`, and the aggregates `count`, `count-distinct`, `sum`, `min`, `max`, `collect`, `collect-by` and `collect-map`. |
| Namespaces | Clojure-style `ns`/`:require`. Built-in namespaces are reserved. Sources come from the host, never from the filesystem. |
| Binary parsing | `defstruct`, a declarative struct DSL in the spirit of Kaitai Struct. It compiles to parsers that can be used from code and as relations. |
| Implementation | Our own interpreter: forms are analyzed into an AST and the AST is compiled to Clojure closures. **No `eval`, and no core.logic.** `eval` may come later as an optimization behind the same AST. |
| Bad data vs bugs | Bad input data never aborts a run. It produces "no match" plus diagnostics. Only program bugs and exhausted limits abort. |

### 1.3 Non-goals (v1)

The following are out of scope for v1:

- Encoding structs back into bytes (the reverse mode).
- Mutation, atoms, transients and host interop.
- User-defined macros.
- Private definitions.
- Code that queries relations.
- Top-down or magic-set evaluation.
- Incremental maintenance (re-running after small fact changes).
- Parallel evaluation.
- Loading sources from the filesystem.
- Compiling via `eval`.
- BigDecimal.
- Why-provenance.
- Host-native built-in namespaces (open question 2).

---

## 2. Program structure and namespaces

### 2.1 Source units

A source unit is a sequence of EDN forms whose first form must be `ns`:

```clojure
(ns acme.parsers.png
  {:endian :be}                                   ; optional attr map: namespace defaults
  (:require [lang.string :as str]
            [lang.bytes :as b]
            [lang.io :as io]
            [host.input :as in]
            [acme.parsers.common :as common :refer [indexed-split]]))
```

The optional attribute map supports `:endian` (`:le` or `:be`) and `:bit-order` (`:msb` or `:lsb`), which set the namespace's defaults for structs (§5.1).

After the `ns` form there are five top-level forms:

- `defn`: a plain function, callable from code.
- `defrel`: a code relation, usable in rule bodies.
- `defrule`: a rule clause, or a fact when it has no body.
- `defstruct`: a binary struct, usable from code and as a relation.
- `deftype`: a struct type alias.

### 2.2 Kinds and name resolution

Every top-level name in a user namespace has exactly **one kind**: function, relation (meaning a rule, `defrel` or struct) or type (struct or `deftype`). A struct is the one name that is both a relation and a type. Defining the same name twice with conflicting kinds is a load error.

**All top-level names in a namespace are visible to each other regardless of order.** Forward references work, and so do mutually recursive `defn`s and structs.

Symbols resolve **by position**, and each position accepts only certain kinds:

| Position | Accepts |
|---|---|
| Rule body literal head (`(x …)`) | relations |
| Rule head aggregate (`(count ?x)`) | aggregates (built-in only) |
| Code call position, or an argument naming a function | functions |
| Struct type position | types |

For a symbol in a given position, resolution proceeds in this order:

1. Locals (code only).
2. The current namespace.
3. Names brought in with `:refer`.
4. `lang.core`, which is auto-referred.

A qualified symbol `a/x` resolves `a` as an alias first, then as a full namespace name. The alias `core` is predefined for `lang.core`. A name defined in the current namespace shadows a `lang.core` name of the same kind, and the loader warns when it does. Because resolution is by position, `lang.core` may legitimately use one name for several kinds: `force` is a function and a relation, and `count` is a function and an aggregate.

### 2.3 Sources come from the host

The host passes a map of `ns-symbol → source`, where a source is either a string or a sequence of already-read forms. `:require` resolves only against that map, the built-in namespaces, and the extern namespaces the host has declared (§7.2).

The loader orders namespaces topologically by their requires. Each of the following is a load error carrying the require chain:

- a cycle;
- an unknown namespace;
- a namespace whose `ns` name differs from its map key;
- a name that collides between a source, an extern and a built-in.

### 2.4 Rule extension and global evaluation

A namespace may only define clauses for its **own** rules. It cannot add clauses to `other.ns/foo`.

Namespaces scope names only. Stratification and the fixpoint span the whole loaded program.

### 2.5 Built-in namespaces

These names are reserved, and user sources may not define them:

- `lang.core`: auto-referred; special forms, core functions, the collection relations and the aggregates.
- `lang.string`: string functions.
- `lang.bytes`: byte access, decoding and checksums.
- `lang.io`: resource access.

The host chooses which built-in namespaces a program may require (`lang.core` is always available). Requiring a withheld namespace is a load error.

---

## 3. Rules

### 3.1 Forms

```clojure
(defrule name {opts}? [head-params…] body-literal…)
```

Several `defrule`s with the same name are a union of clauses, and this is how both disjunction and recursion are expressed. A `defrule` with no body and a fully ground head is a **fact**. All clauses of a relation must have the same arity.

The only rule option is `{:ordered true}`. It turns off planner reordering for that clause, so literals run in the order written; the clause must still pass the readiness check (§6.2).

```clojure
(defrule magic-number ["png" 0x89])                       ; fact
(defrule ancestor [?a ?b] (parent ?a ?b))
(defrule ancestor [?a ?c] (parent ?a ?b) (ancestor ?b ?c))
```

### 3.2 Terms

A term is one of the following:

- A **variable**: a symbol starting with `?`.
- The **wildcard** `_`: a fresh, anonymous variable every time it appears. It is allowed in bodies only.
- A **constant**: any ground EDN literal, including collection literals made only of constants.
- An **expression**: any other form, such as `(:descs ?tbl)` or `[?a 1]`. It is code-sublanguage.

**Where expressions may appear.** Expressions are allowed in the input positions of code relations (`defrel`), struct relations and core relations. They are evaluated once every variable they mention is bound, so range restriction is preserved, and the planner treats them as inputs. An expression at an **output** position of such a relation is also allowed when all of its variables are bound: it acts as an equality post-filter on the produced value. Expressions are **not** allowed in stored-relation (rule or fact) literals or in heads; use `bind` there.

**Distinguishing a constant from an expression.** A vector, map or set literal is a constant if it is ground and an expression otherwise. A list is always an expression; write a literal list as `(quote …)`.

### 3.3 Body literals

| Literal | Meaning |
|---|---|
| `(rel t…)` | Matches a stored relation (facts or rules), a `defrel`, a struct relation, or a core relation. |
| `(not (rel t…))` | Stratified negation. Every variable in it must be bound by an earlier positive literal. A `_` inside it means "any". `rel` may be a stored relation or a computed (code, struct or core) relation, provided all of its arguments are bound; the literal then succeeds when the call yields no matching tuple. |
| `(when expr)` | A guard. `expr` is code-sublanguage and may refer to bound `?vars`. The literal succeeds if `expr` is truthy. |
| `(bind pat expr)` | Evaluates `expr` and matches the result against `pat`. **It fails if the value, or any value pattern-matched within it, is `nil`.** |
| `(bind-nil pat expr)` | The same as `bind`, except that `nil` is an ordinary value. |

**Patterns for `bind`.** A pattern is one of:

- a variable or `_`;
- a constant, which acts as an equality filter;
- a vector pattern, `[?a ?b & ?rest]`, which matches sequentially;
- a map pattern, `{:version ?v :num-records ?n}`, which looks up each key.

For both pattern kinds, a missing key or element counts as `nil`.

A variable in a pattern binds if it is unbound. If it is already bound, it acts as an equality filter.

Inside expressions, `?vars` are ordinary readable locals, and only bound variables may be referenced. The planner checks this (§6.2).

### 3.4 Heads and aggregates

A head param is a variable, a constant, or an aggregate form:

| Aggregate | Result |
|---|---|
| `(count ?x)` | The number of solutions in the group. |
| `(count-distinct ?x)` | The number of distinct values of `?x`. |
| `(sum ?x)` | The sum. Doubles are summed in total order (§5.7), so the result is deterministic. |
| `(min ?x)`, `(max ?x)` | The minimum or maximum under the total order. |
| `(collect ?x)` | The set of values. |
| `(collect-by ?k ?v)` | A vector of the `?v` values ordered by `?k` under the total order. Ties are broken by `?v`. |
| `(collect-map ?k ?v)` | A map from `?k` to `?v`. A duplicate key with a different value is a **run error** (it indicates a program bug). |

**How aggregate input is counted.** The input is the set of distinct **full body assignments**. Every `_` counts as its own distinct hidden variable, so renaming `_` to `?id` never changes a result. Each aggregate is applied to the multiset of its argument's values projected from those assignments. For example, `(sum ?amt)` over `(payment _ ?amt)` sums every payment.

The non-aggregate head params are the group key. A head may contain several aggregates.

**One clause per aggregate relation.** An aggregate relation has exactly one clause. Express disjunction through a helper rule.

**Empty groups.** A group exists only if it has at least one solution, so no aggregate (including `count`) ever yields a tuple for an empty group.

**Range restriction:** every variable in the head must be bound by the body.

### 3.5 Core relations (`lang.core`)

Each of these requires its first argument (or its first two, for `between`) to be bound, and a first argument may be an expression. When the collection or deferred value is `nil`, the relation yields no solutions.

| Relation | Behavior |
|---|---|
| `(elem coll ?x)` | One solution per element of a vector, list or set, or per `[k v]` entry of a map. |
| `(indexed coll ?i ?x)` | Vector or list elements together with their index. |
| `(entry map ?k ?v)` | Map entries. |
| `(force deferred ?v)` | Parses a deferred struct value (§5.6). |
| `(between lo hi ?i)` | Integers in `[lo, hi)`. Each generated integer charges fuel. |

---

## 4. Code relations, functions, and the code sublanguage

### 4.1 `defn`: plain functions

```clojure
(defn rva->offset [pe rva] …)
(defn f ([x] …) ([x y] …))          ; multi-arity, as in Clojure
```

A `defn` is callable from code: function bodies, expressions in rule bodies, and struct expressions. Using a `defn` as a rule literal is a load error, and the message suggests `defrel` or `bind`. A `defn` may be recursive, including mutually recursive with other `defn`s, up to `:max-depth` (§8).

### 4.2 `defrel`: code relations

```clojure
(defrel name [p1 p2 …]
  ([in… -> out…] body)
  …)
```

Each clause declares a **mode**: the parameters listed before `->` are inputs and those after it are outputs. Together, the inputs and outputs of a clause must be exactly the relation's parameters. The body is code-sublanguage with the inputs bound as locals.

**The body returns a collection of output tuples.** Each tuple is a vector of the outputs in declaration order:

- an empty collection (or `nil`) means no solutions;
- several tuples mean several solutions;
- a mode with no outputs (`[a b ->]`) returns a truthy value for success and a falsy value for failure.

Returning anything else is a run error.

```clojure
(defrel hex [bs s]
  ([bs -> s] [[(b/hex-encode bs)]])
  ([s -> bs] (when-let [x (b/hex-decode s)] [[x]])))
```

**Contract: modes denote the same relation.** For any tuple, every mode must agree on whether it belongs to the relation. Results may otherwise depend on the plan the planner chose. `lang.test/check-modes` (§10.2) checks this property on sample inputs.

**How the planner selects a mode:** at a given point in a rule body, a mode is applicable when all of its inputs are bound. If several modes are applicable, the planner picks the one with the most inputs bound, and on a tie the first one declared. If arguments that a mode treats as outputs are already bound, the planner runs that mode and filters the results by equality. If no mode is ever applicable, the program fails at load time (§6.2).

Calling a `defrel` from code is a load error.

**Purity and memoization:** every `defrel` call is treated as pure. Results may be cached per `(relation, mode, inputs)` in a bounded per-run cache (`:max-memo-entries`). Correctness never depends on the cache.

### 4.3 Special forms

The special forms are:

- binding: `let` and `fn` (with an optional self-name for recursion);
- conditionals: `if`, `if-let`, `when`, `when-let`, `when-not`, `cond` and `case`;
- `do`, `loop`/`recur`, `and`/`or`, `quote`;
- threading: `->` and `->>`;
- parsing: `parse` and `parse-explain` (§5.8).

`let`, `fn` and `loop` accept sequential destructuring (`[a b & more]`) and map destructuring (`{:keys [a b] :as m}`, plus `:or`).

`recur` must be in tail position, and this is checked at analysis time. Truthiness follows Clojure: only `nil` and `false` are falsy. Keywords can be called as functions (`(:k m)`, `(:k m default)`). Maps, sets and vectors are **not** callable.

### 4.4 Values

Code can work with the following kinds of values:

- **Scalars:** `nil`, booleans, `long`, `BigInt`, `double`, strings, chars, keywords and symbols (via `quote`).
- **Collections:** vectors, lists, maps and sets.
- **Opaque values:**
  - **bytes**: an immutable, zero-copy slice whose equality and hash are by content, with the hash cached;
  - **handle**: an open resource whose identity is the resource name;
  - **deferred**: an unparsed struct region (§5.6);
  - **function**: the value of a `fn` form.

**Where opaque values can go.** Functions may **not** be stored in tuples or inside values that end up in tuples; attempting it is a run error. Bytes, handles and deferred values may be stored, and each has a defined equality, hash and order (§5.7).

**Numbers:**

- **Arithmetic promotes on overflow** (`+'` semantics), so mixing `u64` values that are `BigInt`s with `long`s is always correct.
- Results are bounded by `:max-int-bits` (§8).
- `u64+`, `u64-` and `u64*` wrap modulo 2⁶⁴. Bit operations accept `u64` values held as `BigInt`.
- `f32` values are widened to `double`.
- **NaN is canonicalized to a single NaN value, and `-0.0` to `0.0`.** This happens at every point a double enters the system: parsing, arithmetic results and host facts. Canonical NaN is equal to itself, both in relations and under `=`.
- Equality and hashing follow Clojure for the remaining values, so `5` and `5N` are equal and hash the same, while `5` and `5.0` are not equal.

### 4.5 Built-ins: eager, and charged by size

Sequence functions return vectors and are never lazy, and `range` always requires an explicit bound.

Every built-in charges fuel **in proportion to the size of its operands and its result, before it allocates**. Sizes are measured as follows:

- elements, for collections;
- characters, for strings;
- KB, for bytes (struct string, bytes, const and cstring decoding charge one unit per KB, at least 1);
- bit length, for big integers.

Beyond fuel, a result is checked against `:max-value-size` and `:max-int-bits`, and allocations of bytes count against `:max-bytes`. Before any operation that may hash or compare a language value (`=`, `compare`, set and map construction or lookup, tuple insertion, memo keys), the value's **deep weight** is computed: scalars weigh 1, strings their length, bytes `len/1024` (at least 1), and collections 1 plus the sum of their children. The walk is memoized by object identity, so structurally shared values cost O(distinct nodes), and it stops as soon as the total exceeds `:max-value-size`, which is a `:value-too-large` error. The deep weight is also charged as fuel.

Built-ins that consume external data return **`nil` on bad data** and never throw:

- out-of-range reads: `b/u32-le` and its siblings, `b/slice`;
- decoders on malformed input: `b/utf8`, `b/hex-decode`;
- `b/inflate` on a corrupt stream or when the output limit is exceeded;
- `io/read-bytes` on a short read;
- the parsers `parse-long` and `parse-double`.

They throw (a run error) only when they are called with the wrong *types*, which indicates a program bug.

### 4.6 Standard library (summary)

**`lang.core`** (auto-referred) provides:

- **Arithmetic and comparison:** `+ - * / quot rem mod inc dec min max abs`, `u64+ u64- u64*`, `= not= < <= > >= compare`, `zero? pos? neg? even? odd?`.
- **Bits:** `bit-and bit-or bit-xor bit-not bit-shift-left bit-shift-right unsigned-bit-shift-right bit-test`. A negative shift count is an `:arithmetic-error`.
- **Collections:** `get get-in assoc assoc-in dissoc update conj into count nth first second last rest next peek subvec keys vals contains? empty? not-empty vec set hash-map vector list merge select-keys zipmap frequencies`.
- **Sequences:** `map map-indexed mapcat filter remove keep reduce reduce-kv range take drop take-while drop-while concat reverse sort sort-by group-by partition partition-all distinct some every? interleave apply`.
- **Predicates and misc:** `nil? some? string? number? integer? keyword? map? vector? set? coll? bytes? deferred? identity not str name keyword parse-long parse-double`.
- **Deferred values:** `force`, plus the accessors `deferred-offset` and `deferred-length`.
- **Special forms:** `parse` and `parse-explain`.

**`lang.string`** provides:

- splitting and joining: `split` (literal separator), `split-lines`, `join`;
- trimming and padding: `trim triml trimr pad-left pad-right`;
- searching and tests: `blank? starts-with? ends-with? includes? index-of last-index-of`;
- other: `subs`, `replace` (literal), `lower-case upper-case` (both with `Locale/ROOT`), `chars`;
- regex functions, `re-find re-matches re-seq re-split`, which take patterns as strings.

Regex matching runs on the run's dedicated big-stack thread (§7.4) over a `CharSequence` that charges fuel and checks interrupts. A regex `StackOverflowError` becomes a `:stack-exhausted` run error. Patterns are capped at `:max-regex-length`.

**`lang.bytes`** provides:

- `size`, `slice`, `index-of` (a byte or a byte sequence);
- fixed-width reads: `u8 i8`, `u16-le u16-be i16-le i16-be`, `u32-*`, `i32-*`, `u64-*` (long or BigInt), `i64-*`, `f32-*`, `f64-*`;
- decoding: `utf8 ascii latin1 cp1252 utf16le utf16be` (each takes bytes, or bytes plus start/end), `encode-utf8` (which returns `nil` for a string with malformed surrogates), `hex-encode hex-decode`;
- `inflate`, which takes a mandatory maximum output size and returns `nil` when that size is exceeded. This is the zip-bomb guard. It handles zlib (RFC 1950), with a `:raw` option for raw DEFLATE;
- checksums and hashes: `crc32`, `fnv1a64`, `sha1`.

**`lang.io`** provides:

- `(open name)`, which returns a handle, or `nil` if the host supplied no resource by that name;
- `(size h)`;
- `(read-bytes h off len)`, which returns bytes, or `nil` on a short read;
- `(read-all h)`, which is subject to `:max-read`.

---

## 5. Struct DSL (`defstruct`)

### 5.1 Forms

```clojure
(defstruct name {opts}? [field-name type, …])
(defstruct name [params…] {opts}? [field-name type, …])   ; parameterized
(deftype   name type-form)                                 ; alias
(deftype   name [params…] type-form)                       ; parameterized alias
```

The forms are distinguished by shape. A parameterized struct has two vectors, and the params vector comes first. A `deftype` whose second element is a vector is parameterized.

A parameterized struct or `deftype` must be used as `[name args…]` with the correct number of arguments. A non-parameterized one is used as a bare symbol. Any mismatch is a load error.

**Options:** `{:endian :le|:be, :bit-order :msb|:lsb}`. **Both are lexical.** For each, the struct's own option is used if present, then the namespace default, then `:le` or `:msb`. A struct always parses the same way wherever it is used, so its identity fully determines its byte interpretation. A primitive's endianness can also be overridden per field, for example `[:u32 :be]`.

### 5.2 Fields

A field is a `name type` pair. The value of a struct is a map from the keyword of each field name to that field's value, with these exceptions:

- A field named `_` is parsed and then discarded. `_` may appear more than once.
- A field whose name starts with `_` (for example `_size`) can be referenced by later expressions but is **left out** of the value map.
- A field that produces **no value** has its key left out. That happens when an `:if` condition is false or a `:try` fails.

### 5.3 Expressions and positional frames

Size, count, offset, condition and predicate positions all take code-sublanguage expressions. Those expressions can see:

- struct parameters;
- **earlier** fields of the same struct (hidden `_x` fields included), by symbol;
- the positional symbols:
  - `$pos`, the current offset;
  - `$start`, the offset where this struct starts;
  - `$remaining`, the number of bytes left in the current window;
- any function that is in scope (`defn`s and built-ins).

Positions are measured within the current **frame**. A frame is either the top-level source or a buffer produced by `:decode`, which opens a new frame starting at 0. `:at`, `:align` and every positional symbol refer to the current frame.

### 5.4 Types

A type is written in one of four ways:

- a **primitive keyword** such as `:u32`;
- a type name symbol (a struct or a zero-param `deftype`), resolved through the namespace;
- a vector headed by a symbol, `[name args…]`, which instantiates a parameterized struct or `deftype`;
- a vector headed by a keyword, which is one of the built-in constructors below.

**Primitives**

| Type | Value |
|---|---|
| `:u8 :i8 :u16 :i16 :u32 :i32 :i64` | long |
| `:u64` | long when it fits, otherwise BigInt |
| `:f32 :f64` | double, canonicalized (§4.4) |

**Built-in constructors**

| Constructor | Semantics |
|---|---|
| `[:bytes n]`, `[:bytes :rest]` | `n` bytes, or the rest of the current window, as a bytes value. |
| `[:string n enc]` | `n` bytes decoded with `enc`, with trailing NULs trimmed. |
| `[:cstring enc :max n]` | Bytes up to a NUL, which is consumed. Fails if no NUL appears within `:max` (default 65536) or within the window. |
| `[:const v]` | `v` is a string (its ASCII bytes) or a vector of byte values. The bytes must match or the parse fails. The value is `v`. |
| `[:array t n]` | Exactly `n` elements, returned as a vector. |
| `[:repeat t :eos]` | Elements until the end of the window. |
| `[:repeat t :until pred]` | Elements up to and including the first one that satisfies `pred`. |
| `[:repeat t :sentinel pred]` | Like `:until`, but the matching element is consumed and **dropped**. |
| `:max n` (on any `:repeat`) | A guard: the parse fails if more than `n` elements would be read. The default is 1,000,000. |
| `[:if expr t]` | Parses `t` when `expr` is truthy. Otherwise it produces no value and consumes nothing. |
| `[:switch expr {case t …} default-t?]` | Dispatches on `expr` with `=`. The optional fourth element is the default branch. With no match and no default, the parse fails. |
| `[:enum t {raw kw …}]` | Maps the raw value to a keyword. An unknown raw value is kept as is. |
| `[:bits n]` | An unsigned `n`-bit integer (n ≤ 64). |
| `[:calc expr]` | Consumes zero bytes. The value is `expr`. |
| `[:assert expr]` | Consumes zero bytes. Fails the parse when `expr` is falsy. The value is `true`. |
| `[:skip n]` | Skips `n` bytes and has no meaningful value. Name it `_`. |
| `[:align n]` | Skips to the next multiple of `n`, measured from the start of the current frame. |
| `[:at off t]` | Parses `t` at absolute offset `off` in the current frame, then returns the cursor, so the field consumes zero bytes. Window bounds do **not** apply to the target, whose window is the whole frame. If `off` is nil or negative, the parse fails. |
| `[:sized n t]` | Confines `t` to an `n`-byte window, and **always** advances exactly `n` bytes. If `t` would read past the window, the parse fails. Unconsumed bytes inside the window are skipped. |
| `[:decode n f t]` | Takes `n` bytes (or `:rest`), applies the function `f` to get new bytes, and parses `t` over them in a **new frame**. If `f` returns nil, the parse fails. |
| `[:try t]` | Parses `t`. If that fails, the field has no value, zero bytes are consumed, and the parent continues. |
| `[:defer n t]` | Consumes `n` bytes (or `:rest`) without parsing them. The value is a deferred value (§5.6). |

**Bit fields.**
- Consecutive `:bits` fields read from a shared bit cursor. The cursor passes through the transparent wrappers `:if`, `:switch`, `:array`, `:repeat`, `:try`, `:enum` and `:ref`/`:alias`, so bit fields continue inside them. Any other type, which reads whole bytes, first realigns to the next byte boundary.
- With `:msb` bit order, bits are taken from the high end of each byte first, and earlier bits are more significant.
- With `:lsb` order, bits are taken from the low end of each byte first, and earlier bits are *less* significant. This is the layout of little-endian C bitfields, and it matches Kaitai's `bit-endian: le`.

Encodings are `:ascii`, `:utf8`, `:latin1`, `:cp1252`, `:utf16le` and `:utf16be`. Malformed input fails the parse; with `:ascii`, any byte above 127 counts as malformed.

Struct nesting (struct within struct, including through `force`) counts toward `:max-depth`.

### 5.5 Failure semantics

A parse fails when the data doesn't fit the description. A failed parse yields `nil` from `parse`, no tuple from a struct relation, and propagates upward until it meets a `:try`. The failure cases are:

- short reads;
- `:const` mismatches;
- `:assert` failures;
- an unmatched `:switch`;
- a missing NUL in a `:cstring`;
- malformed encodings;
- a window overrun;
- a negative or nil size or offset;
- exceeding a `:repeat` element's `:max`;
- a `:decode` function that returns nil;
- a **zero-progress** element inside an `:eos`, `:until` or `:sentinel` repeat, which would otherwise loop forever.

Bad data is never a run error.

Some failures are program errors instead, and they abort the run (§8):

- a size or offset expression that returns a non-integer that isn't `nil`;
- a type error inside an expression;
- an exhausted limit.

### 5.6 Deferred values

A deferred value is opaque. Internally it holds `(source, frame, off, len, type, args)`. Its equality and hash are defined by the source identity (the resource name for a handle, or the Bytes value itself, compared by content, for a bytes source), together with `off`, `len`, the resolved type identity and `args`.

A deferred value is forced with `(force d)` in code or `(force d ?v)` in rules, and forcing is memoized per run. The accessors `deferred-offset` and `deferred-length` let rules key on location without forcing. Deferred values are what make it possible to drill into large files, such as a 250 MB `Skyrim.esm`, without parsing them eagerly.

### 5.7 Total order

`compare`, `sort`, `min`/`max`, `collect-by` and double summation all use one total order over storable values:

1. Values are ordered first by type rank: nil < booleans < numbers < chars < strings < keywords < symbols < vectors and lists < maps < sets < bytes < handles < deferred values.
2. Within numbers, values compare numerically. Numerically equal values of different types are ordered long < BigInt < double, so `(compare 5 5.0)` is non-zero and `compare` agrees with `=`. Canonical NaN sorts after all other numbers.
3. Collections compare lexicographically, with maps and sets compared by their sorted entries. Comparison charges fuel in proportion to the elements it visits.
4. Bytes compare lexicographically, handles by name, and deferred values by their identity tuple.

Functions are not storable, so they are not ordered. Comparing them is a run error.

### 5.8 Using structs

`parse` and `parse-explain` are **special forms**. Their first argument is a type, written in a static type position and resolved at load time; it is never evaluated. The remaining arguments are evaluated.

- **`(parse t src)` and `(parse t src off)`.** `t` may be any type form: a struct name, `[name args…]` with evaluated args, or an inline type like `[:cstring :ascii]`. `src` is a bytes value or a handle. The result is `{:value v :end n}` or `nil`.
- **`(parse-explain t src off?)`.** On failure it returns `{:ok false :path [:chunks 3 :crc] :offset 1234 :reason :eof}`.
- **As a relation.** Every **named** struct is a relation with the single mode `[src off arg… -> value end]`, for example `(import-table ?src ?off ?pe ?tbl _)`. Its results are memoized like `defrel` calls.

When the source is a handle, reads go through the run's bounded page cache (§7.3).

---

## 6. Evaluation

### 6.1 Pipeline

```
sources ─► read ─► resolve ─► analyze ─► check ─► plan ─► stratify ─► compile ─► run
```

Loading (read through compile) and each run execute on a dedicated thread with a large, fixed stack (§7.4).

**Read.** Sources are read with `clojure.tools.reader/read` through an indexing reader, so forms carry `:line`/`:column`. A pre-scan first rejects Clojure-only syntax (`#(`, `#"`, `#'`, `#=`, `#?`, `#:`, `#!`, `@`, backquote, `~`, `^`, `::` and the `'` quote shorthand; write `(quote x)`), and a leaf whitelist rejects any other value in the result. The reader also rejects:

- all tagged literals;
- sources larger than `:max-source-bytes`;
- forms nested deeper than `:max-form-depth`.

**Resolve.** This orders namespaces and resolves every symbol by position (§2.2). **Anything unresolved is a load error.** No symbol can name a Java class or a host Clojure var: only the analyzer's tables are consulted.

**Analyze.** Forms are turned into AST nodes.

**Check.** The checker verifies:

- arities;
- that each name's kind is used in the right position;
- that `recur` is in tail position;
- range restriction;
- that variables in `not`, `when`, `bind` and expressions are bound;
- that aggregates are well formed, with one clause per aggregate relation;
- that every head of a relation has the same arity;
- that parameterized types are given the right number of arguments.

**Plan.** The planner chooses an order for each rule body (§6.2).

**Stratify.** The stratifier builds the relation dependency graph and assigns strata (§6.3).

**Compile.** Each AST is turned into Clojure closures. Code becomes closures over an environment array. Struct types become parser closures. Rule plans become join pipelines.

**Run.** Strata are evaluated in order, each with a semi-naive fixpoint (§6.4).

### 6.2 Body planning

Literals are ordered greedily, and the plan is deterministic. A literal is *ready* under the following conditions:

- **stored relation:** always;
- **`defrel`:** some mode has all of its inputs bound, and all of its input expressions' variables are bound;
- **struct relation:** `src`, `off` and its args are bound or are ready expressions;
- **core relation:** its required inputs are bound or are ready expressions;
- **`when`:** all of its variables are bound;
- **`bind`/`bind-nil`:** all of its expression's variables are bound;
- **`not`:** all of its variables are bound. It may name a stored or a computed relation.

At each step the planner picks a ready literal in this order of preference:

1. filters: `when`, `not`, and `bind` patterns whose variables are all bound;
2. `bind` and `bind-nil`, which yield at most one solution;
3. stored relations, with the most bound arguments first;
4. code, struct and core relations.

Ties are broken by textual order. A rule with `{:ordered true}` skips reordering.

If no literal is ready while some remain, the program fails **at load time**. The error names the literal that could not be placed and the variables it is missing.

For recursive rules, semi-naive evaluation produces one *delta variant* per recursive literal, and each variant is planned with its delta literal pinned first. Because the plans are fixed at load time, the set of indexes each stored relation needs is known statically.

### 6.3 Stratification

The dependency graph has one node per stored relation. Edges run from a rule's head relation to every stored relation in its body. An edge is **negative** when it comes from `not`, and also from any body relation of a rule whose head contains an aggregate.

Code relations, struct relations and core relations are not nodes, because they are pure functions of their inputs.

A cycle that contains a negative edge is a load error, and the error reports the cycle path. Otherwise, the strongly connected components, taken in topological order, become the strata.

### 6.4 Run semantics

**Storage.** Every stored relation is a set of tuples (vectors) together with the indexes its plans require, each one mapping a bound-column mask to `key-tuple → set of tuples`.

**Facts.** EDB facts are the host-supplied facts plus the ground `defrule` facts. Host facts are validated and converted into language values at `run`:

- `byte[]` becomes a bytes value;
- doubles are canonicalized;
- any other non-EDN Java object is a run error.

**Fixpoint.** Each stratum runs a semi-naive fixpoint: the `delta` and `new` sets alternate until `delta` is empty.

**The engine is metered.** Every candidate binding a join step produces charges fuel, and so does every tuple insert. Every derived or inserted tuple, and every expression result and computed-relation output tuple, is checked and charged by its deep weight (§4.5) before it is hashed or compared. Engine work is charged to total `:fuel` only; `:call-fuel` bounds a single code invocation. The timeout is checked whenever fuel is charged across the clock interval, and on any single charge of 65536 or more.

**Aggregation.** Aggregates are computed as described in §3.4, after the strata below them have completed.

**Termination.** Pure Datalog terminates. Code relations can manufacture new values, so a recursive rule that calls code may not terminate; a counter is the obvious example. Such runs are stopped by the fuel, iteration and tuple limits (§8), and the error reports which relation kept growing.

**Determinism.** The same program, facts and resources always produce the same database:

- relations are sets;
- host maps and sets are canonicalized to hash maps and hash sets, and iteration over a map or set (`keys`, `vals`, `first`, `map`, `reduce`, `str`, …) follows the total order;
- all orderings that matter (`collect-by`, `sort`, `min`/`max` and double sums) use the total order;
- doubles are canonicalized;
- functions cannot be stored.

**Identity guidance.** Relations have set semantics, and large values are expensive to hash and join. Store small identity keys, such as `(file, offset)` via `[:calc $start]` or `deferred-offset`, together with deferred values. Avoid storing whole parsed trees in relations.

---

## 7. Host API and the sandbox

### 7.1 Clojure API (`lang.api`)

```clojure
(def prog (lang/load {:sources  {'formats.pe "(ns formats.pe …) …"}
                      :builtins #{'lang.string 'lang.bytes 'lang.io}
                      :externs  {'host.input {'file 1}}     ; relation → arity
                      :limits   {:max-source-bytes 10000000}}))

(def db (lang/run prog {:facts     {'host.input/file [["a.dll"] ["b.dll"]]}
                        :resources {"a.dll" (lang/file-resource (io/file "/x/a.dll"))
                                    "b.dll" (lang/bytes-resource some-byte-array)}
                        :limits    {:fuel 100000000}
                        :trace     (fn [event] …)}))          ; optional

(lang/query db '(formats.pe/missing-dll ?f ?dll))   ; → #{{?f "a.dll" ?dll "c.dll"} …}
(lang/relation db 'formats.pe/imported-dll)          ; → set of tuples
(lang/stats db)        ; per relation: {:tuples n :iterations n}
(lang/diagnostics db)  ; skipped code errors (first 1000 entries, plus counts per kind)
(lang/tainted db)      ; relations affected by skipped errors
(lang/warnings prog)   ; load warnings, such as shadowed names

(lang/parse prog 'formats.pe/pe-file resource)          ; host-side parse
(lang/parse-explain prog 'formats.pe/pe-file resource)  ;   for testing parsers
```

`load` accepts only `:sources :builtins :externs :limits`; any other key, or an unknown `:limits` key, is a `:bad-option` error. `run` likewise whitelists `:facts :resources :limits :trace :on-code-error`. `load` either returns a program or throws a load error (§8). The program can be reused across runs, and **a program is immutable and safe to use from several threads at once**. All per-run state lives in a run context and is never global or thread-local.

`run` is a pure function of `(program, facts, resources, limits)` and returns an immutable database. **The database holds no open handles, page cache or run context**; both are released when `run` returns. Handle and Deferred values stored in tuples may still reference the host Resource objects. A nil fact collection for a declared extern counts as empty, and `relation` of an unknown or computed relation returns `#{}`.

Diagnostics record skipped code errors and tainted relations; in v1 data failures (parse mismatches, nil-returning built-ins) are not recorded. `query` takes a single pattern over a **stored** relation, with constants and variables, and returns a set of binding maps.

`:trace` receives one event map for each rule firing (`:rule-fired`) and parse (`:parse`). A trace sink that throws aborts the run.

### 7.2 Externs

The host declares extern namespaces of fact relations, with an arity for each relation. Programs `:require` them like any other namespace. At `run`, the facts supplied must match the declared relations and arities. Extern relations are EDB, and programs cannot add clauses to them.

### 7.3 Resources and the page cache

A resource implements a protocol:

```clojure
(defprotocol Resource
  (size [r])
  (read-range [r off len]))
```

The implementations provided are `bytes-resource` and `file-resource`, which wraps a read-only `FileChannel`. `(io/open name)` looks the name up in the run's `:resources` map, and nothing else is reachable.

Every read goes through a per-run, bounded LRU page cache (`:page-size`, `:page-cache-bytes`). Parsing many small fields therefore costs a few large reads rather than one read per field. Reads are charged to `:max-bytes` when assembled or copied: a single-page read shorter than a quarter page is copied out of the page (so it cannot pin it), and a longer single-page read stays zero-copy but is still charged. `:max-read` applies to every handle read, including struct reads. A `file-resource` opens the file for each read.

**The host guarantees resources are immutable for the duration of a run**, and the purity of code relations rests on that guarantee.

### 7.4 Sandbox guarantees

The following hold by construction:

- No interop, reflection or `eval`. The only callable things are AST closures and built-ins on the allow-list.
- No file, network, environment, clock or randomness access. The only I/O is through `lang.io` over host-supplied resources.
- Every unit of work is charged fuel: code, built-ins (by size), struct fields, repeat elements, join bindings, tuple inserts and hashing.
- Memory is bounded through:
  - `:max-bytes`, a cumulative budget covering reads, inflate output, decoded buffers and byte allocation;
  - `:max-value-size` and `:max-int-bits`;
  - `:max-tuples`;
  - `:max-memo-entries` and `:page-cache-bytes`.
- The JVM stack is bounded. Load and run execute on a dedicated thread with a fixed stack size, `:max-form-depth` and `:max-depth` bound nesting, and any `StackOverflowError` becomes a `:stack-exhausted` error.
- Errors don't leak host details (§8.2).

---

## 8. Limits and errors

### 8.1 Limits

Each limit can be overridden through `:limits`. The load-time limits are set when the program is loaded, and the run limits on each run.

| Limit | Default | Phase |
|---|---|---|
| `:max-source-bytes` | 10 MB per namespace | load |
| `:max-form-depth` | 256 | load |
| `:fuel` | 10⁹ units per run | run |
| `:call-fuel` | 10⁸ units per top-level code invocation; engine work charges total `:fuel` only | run |
| `:max-depth` | 512 nested calls and struct levels | run |
| `:max-tuples` | 10⁷ in total, also per relation | run |
| `:max-iterations` | 10⁴ per stratum | run |
| `:max-bytes` | 1 GB cumulative | run |
| `:max-read` | 256 MB per single read | run |
| `:max-inflate` | 256 MB, which caps any `inflate` call's maximum | run |
| `:max-value-size` | 10⁷ elements or characters | run |
| `:max-int-bits` | 4096 | run |
| `:max-regex-length` | 1000 characters | run |
| `:max-memo-entries` | 10⁶ | run |
| `:page-size` | 64 KB | run |
| `:page-cache-bytes` | 64 MB | run |
| `:timeout-ms` | none | run |

### 8.2 Errors are data

Every error is an `ex-info` with:

```clojure
{:lang/error  :unresolved-symbol      ; stable keyword per error kind
 :lang/phase  :resolve                ; :read :resolve :analyze :check :plan :stratify :run
 :ns 'formats.pe  :line 42  :column 7
 :form "…"  :message "…"  :data {…}}  ; kind-specific details
```

Run-phase errors carry `:line`/`:column` only where the failing site has them. Every value in `:data` is converted with the same bounded printer, so `:data` values are strings.

**Every JVM throwable is mapped to a language error kind,** such as `:type-error`, `:arity-error` or `:stack-exhausted`. Raw exception messages and host stack traces are never passed through, because they can contain host paths or class names. Forms and values inside errors are printed with a print-length of 20 and a print-level of 4, and the result is truncated to 2 KB.

### 8.3 Error classes

There are three classes:

1. **Load errors** cover every phase before `run`. The program never starts.
2. **Run errors** are program bugs found during the run, such as a type error in code, a duplicate `collect-map` key or a bad `defrel` return value, plus **exhausted limits**. They abort the run by default.
   - If the host sets `:on-code-error :skip`, a **program-bug** error in a single code invocation yields no tuples for that call and is recorded in diagnostics.
   - The skippable kinds are `:type-error`, `:arity-error`, `:bad-relation-result`, `:arithmetic-error`, `:collect-map-conflict`, `:no-matching-clause` and `:bad-regex`.
   - Limit errors are never skipped.
   - Every relation that depends on a skipped call, directly or transitively, is marked **tainted**. If a tainted relation is used under `not` or an aggregate, the run aborts with `:tainted-negation`, because a missing tuple there could produce false conclusions.
3. **Bad data** is not an error. Parse mismatches and nil-returning built-ins yield no match. `parse-explain` can diagnose individual parses; v1 does not record data failures in diagnostics.

---

## 9. Validation against real formats

Subagents researched each format from primary sources and then wrote a parser for it in this DSL. The sources were:

- **PE:** the Microsoft PE/COFF specification.
- **Skyrim plugins:** UESP *Mod File Format* and *TES4*. The xEdit details are from memory and still need verifying.
- **RDAR:** the WolvenKit sources (`ArchiveReader.cs`, `Header.cs`, `Index.cs`, `FileEntry.cs`) and the RED modding wiki.

An adversarial review then independently checked the layout offsets: PE32 `NumberOfRvaAndSizes` is at 92 and PE32+ at 108, record and GRUP headers are 24 bytes, and the RDAR header is 40 bytes with 56-byte entries.

### 9.1 PE: DLLs a DLL imports (complete)

```clojure
(ns formats.pe
  {:endian :le}
  (:require [lang.bytes :as b] [lang.string :as str] [lang.io :as io] [host.input :as in]))

(defstruct dos-header
  [_ [:const "MZ"]  _ [:skip 58]  e-lfanew :u32])                 ; e_lfanew @0x3C

(defstruct coff-header
  [machine :u16  nsections :u16  timestamp :u32  _ [:skip 8]
   opt-size :u16  characteristics :u16])

(defstruct data-dir [rva :u32  size :u32])

(deftype word [wide?] [:switch wide? {true :u64} :u32])

(defstruct optional-header
  [magic        [:enum :u16 {0x10b :pe32 0x20b :pe32+}]
   _            [:assert (keyword? magic)]
   _wide        [:calc (= magic :pe32+)]
   _            [:skip 14]
   entry-point  :u32  base-of-code :u32
   base-of-data [:if (not _wide) :u32]
   image-base   [word _wide]
   section-alignment :u32  file-alignment :u32
   _            [:skip 16]
   size-of-image :u32  size-of-headers :u32  checksum :u32
   subsystem :u16  dll-characteristics :u16
   _            [:array [word _wide] 4]
   loader-flags :u32
   n-dirs       :u32
   dirs         [:array data-dir (min n-dirs 16)]])

(defstruct section-header
  [name [:string 8 :ascii]  virtual-size :u32  virtual-address :u32
   raw-size :u32  raw-ptr :u32  _ [:skip 16]])

(defstruct pe-headers
  [_        [:const [0x50 0x45 0 0]]
   coff     coff-header
   opt      [:sized (:opt-size coff) optional-header]   ; sections follow SizeOfOptionalHeader
   sections [:array section-header (:nsections coff)]])

(defstruct pe-file
  [dos dos-header
   pe  [:at (:e-lfanew dos) pe-headers]])

(defn rva->offset [pe rva]
  (if (< rva (get-in pe [:opt :size-of-headers]))
    rva
    (when-let [s (first (filter (fn [s]
                                  (let [va (:virtual-address s)]
                                    (and (<= va rva) (< rva (+ va (:raw-size s))))))
                                (:sections pe)))]
      (+ (- rva (:virtual-address s)) (:raw-ptr s)))))

(defstruct import-descriptor [pe]
  [ilt :u32  _ [:skip 8]  name-rva :u32  iat :u32
   dll [:if (pos? name-rva)
         [:try [:at (rva->offset pe name-rva) [:cstring :ascii :max 260]]]]])

(defstruct delay-descriptor [pe]
  [attributes :u32  name-addr :u32  _ [:skip 24]
   _rva [:calc (if (bit-test attributes 0)            ; RvaBased; else a VA
                 name-addr
                 (- name-addr (get-in pe [:opt :image-base])))]
   dll  [:if (pos? name-addr)
          [:try [:at (rva->offset pe _rva) [:cstring :ascii :max 260]]]]])

(defstruct import-table [pe]
  [descs [:repeat [import-descriptor pe] :sentinel (fn [d] (zero? (:name-rva d))) :max 4096]])

(defstruct delay-table [pe]
  [descs [:repeat [delay-descriptor pe] :sentinel (fn [d] (zero? (:name-addr d))) :max 4096]])

(defrel open-src [name src]
  ([name -> src] (when-let [h (io/open name)] [[h]])))

(defrel dir-offset [pe idx off]
  ([pe idx -> off]
    (let [d (get-in pe [:opt :dirs idx])]
      (when (and d (pos? (:rva d)))
        (when-let [o (rva->offset pe (:rva d))] [[o]])))))

(defrule file-key [?f ?k] (in/file ?f) (bind ?k (str/lower-case ?f)))

(defrule headers [?f ?src ?pe]
  (in/file ?f)  (open-src ?f ?src)  (pe-file ?src 0 ?parsed _)  (bind {:pe ?pe} ?parsed))

(defrule imported-dll [?f ?dll :import]
  (headers ?f ?src ?pe)  (dir-offset ?pe 1 ?off)  (import-table ?src ?off ?pe ?tbl _)
  (elem (:descs ?tbl) ?d)  (bind ?dll (:dll ?d)))

(defrule imported-dll [?f ?dll :delay]
  (headers ?f ?src ?pe)  (dir-offset ?pe 13 ?off)  (delay-table ?src ?off ?pe ?tbl _)
  (elem (:descs ?tbl) ?d)  (bind ?dll (:dll ?d)))

(defrule depends-on [?f ?dll] (imported-dll ?f ?dll _))
(defrule depends-on [?f ?d2]
  (depends-on ?f ?d1)  (bind ?k (str/lower-case ?d1))
  (file-key ?g ?k)     (imported-dll ?g ?d2 _))

(defrule missing-dll [?f ?dll]
  (depends-on ?f ?dll)  (bind ?k (str/lower-case ?dll))  (not (file-key _ ?k)))
```

### 9.2 Skyrim ESP/ESM/ESL: header, masters, lazy record walk

```clojure
(ns formats.tes4
  {:endian :le}
  (:require [lang.bytes :as b] [lang.string :as str] [lang.io :as io] [host.input :as in]))

(defstruct field                                  ; XXXX folds into the following subrecord
  [_tag  [:string 4 :ascii]  _size :u16
   _big  [:if (= _tag "XXXX") :u32]
   _real [:if _big [:string 4 :ascii]]
   _     [:if _big :u16]
   type  [:calc (or _real _tag)]
   data  [:bytes (or _big _size)]])

(defn inflate-record [bs]                         ; nil on short or corrupt input
  (when-let [n (b/u32-le bs 0)]
    (b/inflate (b/slice bs 4) n)))

(defstruct record-fields [flags]
  [fs [:switch (bit-test flags 18)                ; 0x40000 compressed
        {false [:repeat field :eos]
         true  [:decode :rest inflate-record [:repeat field :eos]]}]])

(defstruct record [size]
  [flags :u32  form-id :u32  timestamp :u16  vc-info :u16  form-version :u16  _ :u16
   fields [:defer size [record-fields flags]]])   ; lazy: parsed only when forced

(defstruct group [size]
  [label [:bytes 4]  group-type :i32  timestamp :u16  vc-info :u16  _ :u32
   children [:defer (- size 24) [:repeat item :eos]]])   ; GRUP size includes its header

(defstruct item                                   ; a record or a group
  [at   [:calc $start]
   type [:string 4 :ascii]
   size :u32
   body [:switch type {"GRUP" [group size]} [record size]]])

(defstruct plugin
  [header item
   _      [:assert (= (:type header) "TES4")]
   groups [:defer :rest [:repeat item :eos]]])

(defstruct hedr-data [version :f32  num-records :u32  next-object-id :u32])

(defrel load-plugin [name p]
  ([name -> p] (when-let [h (io/open name)]
                 (when-let [r (parse plugin h 0)] [[(:value r)]]))))

(defrule loaded [?f ?p] (in/file ?f) (load-plugin ?f ?p))

(defrule header-field [?f ?i ?type ?data]
  (loaded ?f ?p)
  (force (get-in ?p [:header :body :fields]) ?hf)
  (indexed (:fs ?hf) ?i ?fld)
  (bind {:type ?type :data ?data} ?fld))

(defrule hedr [?f ?version ?num-records]
  (header-field ?f _ "HEDR" ?data)
  (bind {:version ?version :num-records ?num-records} (:value (parse hedr-data ?data))))

(defrule master [?f ?i ?name]
  (header-field ?f ?i "MAST" ?data)
  (bind ?name (:value (parse [:cstring :cp1252] ?data))))

(defrule masters [?f (collect-by ?i ?name)] (master ?f ?i ?name))   ; load order

(defrule light [?f]
  (loaded ?f ?p)
  (when (or (bit-test (get-in ?p [:header :body :flags]) 9)        ; 0x200
            (str/ends-with? (str/lower-case ?f) ".esl"))))

(defrule file-key [?f ?k] (in/file ?f) (bind ?k (str/lower-case ?f)))
(defrule missing-master [?f ?m]
  (master ?f _ ?m)  (bind ?k (str/lower-case ?m))  (not (file-key _ ?k)))

;; Nodes are keyed by (file, offset). Bodies hold only headers and deferred values.
(defrule node [?f ?at ?type ?body]
  (loaded ?f ?p)  (force (:groups ?p) ?es)  (elem ?es ?e)
  (bind {:at ?at :type ?type :body ?body} ?e))
(defrule node [?f ?at ?type ?body]
  (node ?f _ "GRUP" ?g)  (force (:children ?g) ?es)  (elem ?es ?e)
  (bind {:at ?at :type ?type :body ?body} ?e))

(defrule record-count [?f ?type (count ?at)]
  (node ?f ?at ?type _)  (when (not= ?type "GRUP")))
```

Forcing a group parses only the 24-byte header of each child. Record fields stay deferred until a rule forces them, and only then is a compressed record inflated.

### 9.3 Cyberpunk 2077 `.archive` (RDAR): header and index

```clojure
(ns formats.rdar
  {:endian :le}
  (:require [lang.io :as io] [host.input :as in]))

(defstruct rdar-header
  [_ [:const "RDAR"]  version :u32  index-pos :u64  index-size :u32
   debug-pos :u64  debug-size :u32  file-size :u64])

(defstruct file-entry                       ; 56 bytes
  [name-hash :u64                           ; FNV1a64 of the path; needs the full u64 range
   timestamp :i64                           ; FILETIME
   inline-buffers :u32
   seg-start :u32  seg-end :u32             ; end is exclusive
   dep-start :u32  dep-end :u32
   sha1 [:bytes 20]])

(defstruct file-segment [offset :u64  zsize :u32  size :u32])

(defstruct rdar-index
  [file-table-offset :u32  file-table-size :u32  crc :u64
   entry-count :u32  segment-count :u32  dep-count :u32
   entries      [:array file-entry entry-count]
   segments     [:array file-segment segment-count]
   dependencies [:array :u64 dep-count]])

(defstruct rdar-archive
  [header rdar-header
   _      [:assert (= 12 (:version header))]
   index  [:at (:index-pos header) rdar-index]])    ; not [:sized]: tolerate trailing bytes

(defrel open-src [name src] ([name -> src] (when-let [h (io/open name)] [[h]])))

(defrule archive [?f ?a] (in/file ?f) (open-src ?f ?src) (rdar-archive ?src 0 ?a _))

(defrule archive-file [?f ?i ?hash]
  (archive ?f ?a)  (indexed (get-in ?a [:index :entries]) ?i ?e)  (bind ?hash (:name-hash ?e)))

(defrule file-segment-of [?f ?i ?seg]                ; entry → its segments, by index range
  (archive ?f ?a)  (indexed (get-in ?a [:index :entries]) ?i ?e)
  (between (:seg-start ?e) (:seg-end ?e) ?j)
  (bind ?seg (get-in ?a [:index :segments ?j])))
```

`between` turns the index-range link into a direct lookup rather than a cross product. Segment data is Oodle-compressed (`KARK` magic), and so is the optional LXRS path list. Decompressing either one needs a native built-in (open question 2).

### 9.4 Findings that shaped the DSL

- **Parameterized structs.** Import descriptors need the section table, and records need their size and flags.
- **`deftype`.** The PE32 and PE32+ word width would otherwise be a `:switch` repeated five times.
- **`[:calc]`, `[:assert]`, `_hidden` fields, `$start`/`$pos`, `[:bytes :rest]`.** All of these came up in every format.
- **`:sentinel` repeat with `:max`.** The PE import table ends with an all-zero descriptor.
- **XXXX without sibling state.** One `field` element covers XXXX together with the subrecord that follows it.
- **`[:decode n f t]` plus `b/inflate`.** Compressed Skyrim records need both.
- **`[:defer]` and `force`.** Plugin files run to hundreds of MB.
- **u64 as long or BigInt, plus wrapping u64 arithmetic.** RDAR hashes and the CRC use the full 64 bits.
- **`[:try]`.** One bad name RVA shouldn't sink the whole PE.
- **Exact `:sized` and window semantics.** GRUP sizes include their header, and PE's `SizeOfOptionalHeader` can disagree with the fields actually present.
- **Expressions in input positions, `bind` destructuring, `between`.** These removed most of the boilerplate in the first draft of the examples.

---

## 10. Implementation layout and testing

### 10.1 Project layout

```
deps.edn  mise.toml
src/lang/
  api.clj          load / run / query / parse, resources, externs, stats, tainted, warnings
  program.clj      load pipeline (read → compile) and run-program
  reader.clj       tools.reader reading, syntax pre-scan, size/depth limits, locations
  ns.clj           namespace graph, positional resolution, reserved names
  analyze/code.clj analyze/rule.clj analyze/struct.clj   forms → AST, rule checks
  plan.clj         body ordering, delta variants, index requirements
  stratify.clj     dependency graph, SCCs, negative-cycle detection
  runtime.clj      run context: fuel, limits, memo, diagnostics, big-stack thread
  resource.clj     resources, byte sources, page cache
  values.clj       bytes, handle, deferred types; NaN/-0.0 canonicalization; deep weights
  order.clj        total order / compare
  compile/code.clj   code AST → closures; fuel/depth accounting
  compile/struct.clj type AST → parser closures; frames, windows, bits, deferred, decode
  engine.clj       relations, indexes, metered semi-naive fixpoint, aggregates, taint
  errors.clj       error constructors, throwable mapping, safe printing
  builtins.clj     registry
  builtins/core.clj  builtins/coll.clj  builtins/string.clj  builtins/bytes.clj  builtins/io.clj
  test.clj         check-modes and parser-testing helpers (lang.test)
test/lang/…        mirrors src
test/lang/fixtures/  synthetic binary builders (PE32/PE32+, TES4, RDAR)
```

### 10.2 Testing strategy

Implementation follows TDD.

- **Unit tests per component:**
  - the reader's limits and tag policy;
  - positional resolution, including every reserved or illegal symbol;
  - each special form and each built-in, including its fuel and size charges;
  - each struct type, plus every failure case in §5.5;
  - bit orders;
  - frames inside `:decode`;
  - the planner's orderings and its rejections;
  - stratification cycles;
  - each aggregate's semantics, including the `_` counting rule;
  - taint propagation.
- **Property tests** (test.check):
  - on randomly generated positive and stratified programs, semi-naive results equal naive results;
  - the total order is transitive and antisymmetric, and agrees with `=`;
  - struct primitives round-trip against a reference encoder written in the tests;
  - results are independent of the order in which facts are inserted.
- **Format tests:** synthetic fixtures for PE (PE32 and PE32+), TES4 (with XXXX and compressed records) and RDAR, built by small binary writers in the test code. Real game files and DLLs can't be committed, so optional local tests run against real files when an environment variable points to them.
- **Sandbox tests:**
  - none of these resolve: `java.lang.System/exit`, `(.foo x)`, `(new X)`, `clojure.core/eval`;
  - tagged literals are rejected;
  - `(loop [] (recur))` ends in `:fuel-exhausted`;
  - an inflate bomb is capped by `inflate`'s maximum output size;
  - `(bit-shift-left 1 100000)` hits `:max-int-bits`;
  - a big cross-product join exhausts fuel;
  - a regex on an alternation over long input fails cleanly;
  - deeply nested source is rejected;
  - deep recursion hits `:max-depth`;
  - error messages contain no host paths.
- **Error tests:** each error kind carries its phase and location.

---

## 11. Open questions

1. **Name.** The language needs a name, which replaces the `lang.` prefix. The candidates so far are Lode, Quarry, Strata, Assay, Glean and Weft.
2. **Host-native built-in namespaces.** Should a later version let the host register native pure functions as extra built-in namespaces, under the same allow-list as `lang.io`? An example would be `host.oodle` for RDAR segment data. v1 does not include them.
