# Strata Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build a sandboxed, EDN-syntax language for Clojure. It pairs bottom-up Datalog rules with mode-dispatched code relations, an interpreted Clojure-like code language, and a binary struct DSL.

**Architecture:** Sources go through these stages: an EDN reader, then namespace resolution, an analyzer that produces AST maps, checks, a planner and a stratifier. A closure compiler then turns every AST into Clojure closures; there is no `eval`. A metered semi-naive engine evaluates the rules. Everything runs with an explicit run context (`ctx`) that carries fuel, limits, memo tables, the page cache and diagnostics.

**Tech Stack:**
- Clojure 1.12.6 on JDK 27 (temurin-27.0.0+35, pinned in `mise.toml`)
- `org.clojure/tools.reader` 1.6.0
- `org.clojure/test.check` 1.1.3
- `io.github.cognitect-labs/test-runner` v0.5.1

**Spec:** `docs/superpowers/specs/2026-10-22-logic-language-design.md`. Every task cites its spec sections (§N), and the implementer must read those sections before starting.

## Global Constraints

- **Namespace prefix:** all source namespaces are `strata.*`, and built-in language namespaces are `strata.core`, `strata.string`, `strata.bytes` and `strata.io`. Renaming happens later, so don't hard-code the prefix anywhere beyond the ns names and the registry.
- **No `eval`:** never call `eval`, `load-string`, `resolve`, `ns-resolve`, `requiring-resolve`, `Class/forName` or reflection on language input. Language symbols resolve only through `strata.ns`/`strata.builtins` tables.
- **Language values:**
  - Doubles are canonicalized: NaN becomes the `strata.values/nan` singleton, and `-0.0` becomes `0.0`.
  - Integers are `long` or `clojure.lang.BigInt`. There are no Ratios and no BigDecimal.
  - `f32` is widened to `double`.
- **Bad data never throws:** it returns `nil` or fails the parse. Program bugs throw `strata.errors/error!`. Limit exhaustion throws a limit error kind.
- **Errors:** every thrown error is an `ex-info` whose data contains `:strata/error` (a keyword) and `:strata/phase`. Host exception messages are never included.
- **Default limits** (§8.1, exact values in bytes): `:max-source-bytes 10485760`, `:max-form-depth 256`, `:fuel 1000000000`, `:call-fuel 100000000`, `:max-depth 512`, `:max-tuples 10000000`, `:max-iterations 10000`, `:max-bytes 1073741824`, `:max-read 268435456`, `:max-inflate 268435456`, `:max-value-size 10000000`, `:max-int-bits 4096`, `:max-regex-length 1000`, `:max-memo-entries 1000000`, `:page-size 65536`, `:page-cache-bytes 67108864`, `:timeout-ms nil`.
- **Built-in sequence functions are eager:** they return vectors.
- **Test commands:**
  - all tests: `clojure -X:test`;
  - one test namespace: `clojure -X:test :nses '[strata.foo-test]'`;
  - one test var: `clojure -X:test :vars '[strata.foo-test/bar]'`.
- **Commits:** one commit per task, with a message of the form `feat(<area>): …`.

## Review Focus

1. **Reads at or past end of input:** empty resources, offsets exactly at EOF, and 0-length `:bytes`. These should fail the parse or yield an empty value, never throw. *Test: Task 15, `eof-edges`.*
2. **cp1252 and non-ASCII bytes:** the bytes 0x80–0x9F decode to the Windows-1252 characters (0x80 decodes to `€`), and invalid UTF-8 gives `nil`. *Test: Task 10, `cp1252-high-range`.*
3. **A reference to an undefined relation, or one with no clauses:** this is a load error naming the symbol, not an empty result. *Test: Task 17, `undefined-relation`.*
4. **Malformed host facts:** a wrong arity, an undeclared relation, or a Java object inside a fact gives a clean `:bad-fact` error. *Test: Task 22, `bad-host-facts`.*
5. **A fact supplied by both the host and a ground `defrule`, or derived twice:** it is stored as a single tuple, and aggregates see it once. *Test: Task 20, `duplicate-facts-collapse`.*

---

## File Structure

```
deps.edn  mise.toml  .gitignore
src/lang/errors.clj        error!, safe-str, map-throwable, loc-of
src/lang/values.clj        Bytes, Handle, Deferred, LangFn, nan, canon, weight, apply-fn
src/lang/runtime.clj       default-limits, RunCtx, charge!, depth, bytes, memo, diag, trace, run-isolated
src/lang/resource.clj      Resource protocol, bytes/file resources, page cache, ByteSource
src/lang/order.clj         compare-values (total order)
src/lang/reader.clj        read-forms (tools.reader edn + limits)
src/lang/ns.clj            parse-ns-form, order-namespaces, program symbol table, resolve-name
src/lang/builtins.clj      registry assembly + special-form names
src/lang/builtins/core.clj      scalar/arith/bits/u64/predicates
src/lang/builtins/coll.clj      collections + seqs (also exported as strata.core)
src/lang/builtins/string.clj    strata.string
src/lang/builtins/bytes.clj     strata.bytes
src/lang/builtins/io.clj        strata.io
src/lang/analyze/code.clj       code forms → code AST (desugaring, destructuring, tail check)
src/lang/compile/code.clj       code AST → closures; defn table
src/lang/analyze/struct.clj     defstruct/deftype → type AST
src/lang/compile/struct.clj     type AST → parser closures; parse/parse-explain/force
src/lang/analyze/rule.clj       defrule/defrel → rule AST; checks
src/lang/plan.clj               body planning, delta variants, index requirements
src/lang/stratify.clj           dependency graph, strata
src/lang/engine.clj             storage, metered semi-naive eval, aggregates, taint; naive eval
src/lang/program.clj            whole-program load pipeline (sources → compiled program)
src/lang/api.clj                public host API
src/lang/test.clj               strata.test helpers (check-modes)
test/lang/*_test.clj            mirrors src (analyze/compile subdirs mirrored)
test/lang/fixtures/{pe,tes4,rdar}.clj   binary builders
test/lang/formats/{pe,tes4,rdar}_test.clj
test/lang/sandbox_test.clj  test/lang/property_test.clj
```

### Shared data shapes

Tasks reference these shapes by name.

- **Computed relation entry**, used for built-in relations, `defrel` and structs: `{:qname sym :arity n :modes [{:in [idx…] :out [idx…] :impl (fn [ctx in-vals-vector] → coll-of-out-tuples)}]}`. A mode with no outputs returns a truthy or falsy value; the engine turns that into `[[]]` or `[]`.
- **Builtin fn entry:** `{:impl (fn [ctx & args]) :arity [min max-or-nil]}`. The `:impl` receives the run ctx first.
- **Registry:** `{ns-sym {:fn {sym fn-entry} :relation {sym computed-relation-entry} :aggregate #{sym}}}`.
- **Code closure:** `(fn [ctx env] value)`, where `env` is a persistent map from local-id (a long) to value.
- **Parser closure:** `(fn [ctx cur env] → (Res. value cur') or nil)`, with `cur = {:frame src :pos long :end long :bit-pos int :bit-buf long}`.

---

## Milestone 0–1: Foundations

### Task 1: Project scaffold and `strata.errors`

**Spec:** §8.2, §8.3

**Files:**
- Create: `deps.edn`, `.gitignore`, `src/lang/errors.clj`
- Test: `test/lang/errors_test.clj`

**Interfaces:**
- Produces:
  - `(error! kind phase msg data)` throws an ex-info with data `(merge {:strata/error kind :strata/phase phase :message msg} (select-keys data [:ns :line :column]) {:form (safe-str (:form data)) :data (dissoc data :ns :line :column :form)})`.
  - `(lang-error? x)` returns a boolean.
  - `(safe-str x)` returns a string printed with `*print-length* 20` and `*print-level* 4`, truncated to 2048 characters with a trailing `…`.
  - `(loc-of form)` returns `{:line :column}` from the form's metadata, or `{}`.
  - `(map-throwable t phase)` returns a lang ex-info. A lang error passes through unchanged. Otherwise:

    | Throwable | Kind |
    |---|---|
    | `StackOverflowError` | `:stack-exhausted` |
    | `ClassCastException` | `:type-error` |
    | `clojure.lang.ArityException` | `:arity-error` |
    | `ArithmeticException` | `:arithmetic-error` |
    | `OutOfMemoryError` | `:out-of-memory` |
    | anything else | `:internal-error` |

    The message is a fixed string per kind, and the original `.getMessage` is never included.

- [ ] **Step 1: Initialize the repository**

  Run `git init` and add a `.gitignore` containing `.cpcache/`, `.nrepl-port` and `target/`. Then create `deps.edn`:

```clojure
{:paths ["src"]
 :deps {org.clojure/clojure {:mvn/version "1.12.6"}
        org.clojure/tools.reader {:mvn/version "1.6.0"}}
 :aliases
 {:test {:extra-paths ["test"]
         :extra-deps {org.clojure/test.check {:mvn/version "1.1.3"}
                      io.github.cognitect-labs/test-runner {:git/tag "v0.5.1" :git/sha "dfb30dd"}}
         :exec-fn cognitect.test-runner.api/test
         :exec-args {:dirs ["test"]}}}}
```

- [ ] **Step 2: Write failing tests** in `test/lang/errors_test.clj`:
  - `error-shape`: `(try (error! :unresolved-symbol :resolve "Unknown symbol foo" {:ns 'a.b :line 3 :column 5 :form '(foo 1) :sym 'foo}) (catch Exception e (ex-data e)))` contains `:strata/error :unresolved-symbol`, `:strata/phase :resolve`, `:line 3`, `:form "(foo 1)"` and `:data {:sym foo}`.
  - `safe-str-truncates`: `(count (safe-str (range 100000)))` is ≤ 2049, and `(safe-str (vec (range 30)))` contains `"..."`.
  - `map-throwable-hides-messages`: `(map-throwable (ClassCastException. "/secret/path") :run)` has `:strata/error :type-error`, and `(ex-message …)` does not contain `"secret"`. Test the same for `StackOverflowError` → `:stack-exhausted`.
  - `lang-error-passthrough`: an existing lang error is returned as the identical object.
- [ ] **Step 3: Run the tests.** `clojure -X:test :nses '[strata.errors-test]'` should FAIL because the namespace is missing.
- [ ] **Step 4: Implement** `src/lang/errors.clj` with the functions listed in Interfaces.
- [ ] **Step 5: Run the tests again.** They should PASS.
- [ ] **Step 6: Commit** with `git add -A && git commit -m "feat(errors): project scaffold and error data"`.

### Task 2: `strata.values`

**Spec:** §4.4, §5.6, §5.7 (identity of opaque values)

**Files:**
- Create: `src/lang/values.clj`
- Test: `test/lang/values_test.clj`

**Interfaces:**

Produces:

- **`Bytes`** (deftype). Fields are `^bytes arr`, `^long off` and `^long len`, plus a cached hash. `equals` and `hashCode` (and `IHashEq`) are by content.
  - `(wrap-bytes ^bytes a)` wraps an array without copying (internal use).
  - `(copy-bytes ^bytes a)` makes a defensive copy for host input.
  - `(bsize b)` returns the length.
  - `(bget b i)` returns an unsigned 0–255 long, or `nil` when out of range.
  - `(bslice b start end)` returns a Bytes or `nil` when the range is invalid; it is zero-copy.
  - `(barray b)` returns a fresh `byte[]`.
  - `(bytes-val? x)` returns a boolean.
- **`Handle`** (deftype). Fields are `name` and `resource`. `equals` and `hash` are by name.
  - `(->Handle name resource)`.
  - `(handle? x)`.
- **`Deferred`** (deftype). Fields are `src-id`, `src`, `off`, `len`, `type-id`, `force-fn` and `args`. `equals` and `hash` are by `[src-id off len type-id args]`; `force-fn` is `(fn [ctx d] value-or-nil)`.
  - `(deferred? x)`.
  - `(deferred-offset d)`.
  - `(deferred-length d)`.
- **`LangFn`** (deftype). Fields are `name` and `impl`, where `impl` is `(fn [ctx args-vector])`.
  - `(lang-fn? x)`.
  - `(apply-fn ctx f args-vector)` handles three cases. A `LangFn` calls its `impl`. A Keyword with 1–2 args means `(get m k default)`. Anything else raises `error! :type-error :run`.
- **`nan`** is a singleton value. `(nan? x)` tests for it.
- **`(canon-num x)`** canonicalizes a number:
  - Double NaN becomes `nan`, and `-0.0` becomes `0.0`.
  - Float is widened to double and then canonicalized.
  - Byte, Short and Integer become long.
  - BigInteger and BigInt become a long when they fit, otherwise a BigInt.
  - Ratio and BigDecimal raise `error! :unsupported-value`.
- **`(canon x)`** deep-canonicalizes host data. It accepts nil, booleans, String, Character, Keyword, Symbol and numbers (via `canon-num`). It accepts vectors, lists, maps and sets recursively, preserving the collection type. `byte[]` becomes a Bytes; Bytes, Handle and Deferred pass through. Anything else raises `error! :unsupported-value :run`.
- **`(storable? x)`** is a deep check for the absence of `LangFn`.
- **`(weight x)`** gives a shallow size weight:
  - a String: its length;
  - a Bytes: `max(1, len/1024)`;
  - a counted collection: its `count`;
  - a BigInt: `bitLength/64` plus 1;
  - anything else: 1.

- [ ] **Step 1: Write failing tests.**
  - `bytes-equality`: `(= (wrap-bytes (byte-array [1 2 3])) (bslice (wrap-bytes (byte-array [0 1 2 3])) 1 4))` is true, and so is equality of their hashes. They work as keys in `#{}` and `{}`.
  - `bytes-bounds`: `(bget b 99)` is nil, `(bslice b 2 1)` is nil, and `(bget (wrap-bytes (byte-array [-1])) 0)` is 255.
  - `canon-nan`: `(identical? nan (canon-num Double/NaN))`, `(= 0.0 (canon-num -0.0))` with `(Double/compare 0.0 (canon-num -0.0))` equal to 0, `(contains? #{(canon-num Double/NaN)} nan)`, and `(canon-num (float 1.5))` is `1.5`.
  - `canon-ints`: `(canon-num (biginteger 5))` returns a Long; `(canon-num (bigint "18446744073709551615"))` stays a BigInt.
  - `canon-rejects`: `(canon (Object.))` and `(canon 1/3)` throw `:unsupported-value`, while `(canon {:a [(byte-array [1])]})` yields a Bytes inside.
  - `deferred-identity`: two Deferreds with the same `[src-id off len type-id args]` and different `force-fn` are `=`.
  - `apply-fn-keyword`: `(apply-fn nil :a [{:a 1}])` is 1, and `(apply-fn nil :b [{} 7])` is 7. Calling a non-callable value throws `:type-error`.
  - `storable`: `(storable? [1 {:a (->LangFn 'f identity)}])` is false.
- [ ] **Step 2: Run the tests.** `clojure -X:test :nses '[strata.values-test]'` should FAIL.
- [ ] **Step 3: Implement** `src/lang/values.clj`. Give `nan` its own deftype, `NaNValue`, whose `equals` is identity and whose `hashCode` is a constant; `print-method` prints it as `##NaN`.
- [ ] **Step 4: Run the tests again.** They should PASS.
- [ ] **Step 5: Commit** with `feat(values): bytes, handle, deferred, fn values and numeric canonicalization`.

### Task 3: `strata.runtime`

**Spec:** §7.4, §8.1

**Files:**
- Create: `src/lang/runtime.clj`
- Test: `test/lang/runtime_test.clj`

**Interfaces:**

Consumes:
- `strata.errors/error!`
- `strata.errors/map-throwable`

Produces:
- **`default-limits`**: exactly the map given in Global Constraints.
- **`(make-ctx opts)`**: `opts` is `{:limits m :trace f-or-nil :on-code-error :abort|:skip :resources {name resource}}`. It returns a `RunCtx` record. Mutable counters are `long-array` cells: fuel left, call-fuel left, depth, bytes used and the start time. The record also holds the memo, a `LinkedHashMap` in access order with eviction above `:max-memo-entries`; the page cache, a slot that `strata.resource` fills; and the diagnostics, a volatile `{:entries [] :counts {}}`.
- **`(charge! ctx n)`**: subtracts `n` from both fuel and call-fuel. When fuel goes below 0 it throws `:fuel-exhausted`, and when call-fuel does, `:call-fuel-exhausted`; both use phase `:run`. When `:timeout-ms` is set, it checks the clock every 65536 units and throws `:timeout`. When `ctx` is nil it does nothing.
- **`(with-call-budget ctx thunk)`**: resets call-fuel to `:call-fuel` and restores the outer value afterwards.
- **`(with-depth ctx thunk)`**: increments depth and throws `:depth-exceeded` above `:max-depth`.
- **`(alloc-bytes! ctx n)`**: adds to the bytes used, and throws `:bytes-exhausted` above `:max-bytes`.
- **`(check-size! ctx n)`**: throws `:value-too-large` when `n` is above `:max-value-size`.
- **`(check-int! ctx x)`**: for a BigInt whose bitLength is above `:max-int-bits`, throws `:int-too-large`. It returns `x`.
- **Memo:** `(memo-get ctx k)` returns the value or `::miss`; `(memo-put! ctx k v)` stores it.
- **`(diag! ctx kind data)`**: increments `(:counts kind)` and keeps at most 1000 entries.
- **`(diagnostics ctx)`**: returns the diagnostics.
- **`(trace! ctx event)`**: calls the trace function when one is set.
- **`(limit ctx k)`**: returns the value of a limit.
- **`(run-isolated thunk)`**: runs the thunk on a new `Thread` with a 1 GB stack (`(* 1024 1024 1024)`), joins it, and returns the result. A throwable thrown inside is rethrown as `(map-throwable t :run)`, except that lang errors are rethrown unchanged.

- [ ] **Step 1: Write failing tests.**
  - `fuel-exhausts`: `(make-ctx {:limits {:fuel 10}})`, then `(charge! ctx 11)` throws `:fuel-exhausted`.
  - `call-budget`: with `:call-fuel 5`, charging 6 inside `with-call-budget` throws `:call-fuel-exhausted`. Outside it, call-fuel is restored.
  - `depth`: nesting 513 levels of `with-depth` throws `:depth-exceeded`.
  - `memo-lru`: with `:max-memo-entries 2`, put a, b, c; then `(memo-get ctx :a)` is `::miss`.
  - `int-bits`: `(check-int! ctx (.shiftLeft (biginteger 1) 5000))` (as a BigInt) throws `:int-too-large`.
  - `isolated-stack`: `(run-isolated #(letfn [(f [n] (if (zero? n) 0 (inc (f (dec n)))))] (f 100000)))` returns 100000. Unbounded recursion inside `run-isolated` yields `:stack-exhausted`.
  - `timeout`: with `:timeout-ms 1`, a loop calling `(charge! ctx 1)` after `(Thread/sleep 5)` eventually throws `:timeout`.
- [ ] **Step 2: Run the tests.** `clojure -X:test :nses '[strata.runtime-test]'` should FAIL.
- [ ] **Step 3: Implement** `src/lang/runtime.clj`. `make-ctx` merges `opts :limits` over `default-limits`.
- [ ] **Step 4: Run the tests again.** They should PASS.
- [ ] **Step 5: Commit** with `feat(runtime): run context, fuel, limits, memo, isolated thread`.

### Task 4: `strata.resource`: resources, page cache and byte sources

**Spec:** §7.3, §4.6 (`strata.io`), §5.8

**Files:**
- Create: `src/lang/resource.clj`
- Test: `test/lang/resource_test.clj`

**Interfaces:**

Consumes:
- `strata.values` (Bytes, Handle)
- `strata.runtime` (ctx, `limit`, `alloc-bytes!`)

Produces:
- **`(defprotocol Resource (size [r]) (read-range [r off len]))`**. `read-range` returns a `byte[]` of exactly `len` bytes, or `nil` when the range runs past the end or is negative.
- **`(bytes-resource ^bytes a)`**: copies the array defensively.
- **`(file-resource ^java.io.File f)`**: reads with a `RandomAccessFile` opened read-only for each `read-range` call, inside `with-open`.
- **`(open-handle ctx name)`**: returns a Handle, or `nil` when the name isn't in `(:resources ctx)`.
- **`(defprotocol ByteSource (src-size [s ctx]) (src-read [s ctx off len]))`**: returns a Bytes or `nil`. It is implemented for Bytes (a zero-copy slice) and for Handle (through the page cache).
- **The page cache** is keyed by `[name page-idx]` and holds pages of `:page-size` bytes. It is an LRU bounded by `:page-cache-bytes`, stored in the ctx. A read that spans pages assembles a fresh Bytes.
- **`(src-id s)`**: a Handle's id is `[:resource name]`; a Bytes's id is `[:bytes (hash b) (bsize b)]`.

- [ ] **Step 1: Write failing tests.**
  - `bytes-resource-read`: `(read-range r 1 2)` is `[2 3]` for the array `[1 2 3 4]`, and `(read-range r 3 2)` is nil.
  - `file-resource-read`: use a temp file containing 100,000 bytes.
  - `handle-page-cache`: with `:page-size 16`, a read crossing a page boundary returns the correct bytes. Count the resource's reads by wrapping it in a counting `reify`: 10 reads of 1 byte in the same page cause only 1 `read-range`.
  - `cache-bounded`: with `:page-cache-bytes 32` and `:page-size 16`, reading 4 distinct pages and then the first page again causes a fresh `read-range`.
  - `open-handle-missing`: `(open-handle ctx "nope")` is nil.
  - `eof-read`: `(src-read h ctx (size r) 0)` is an empty Bytes, and `(src-read h ctx (size r) 1)` is nil.
- [ ] **Step 2: Run the tests.** `clojure -X:test :nses '[strata.resource-test]'` should FAIL.
- [ ] **Step 3: Implement** `src/lang/resource.clj`.
- [ ] **Step 4: Run the tests again.** They should PASS.
- [ ] **Step 5: Commit** with `feat(resource): resources, page cache, byte sources`.

### Task 5: `strata.order`: the total order

**Spec:** §5.7

**Files:**
- Create: `src/lang/order.clj`
- Test: `test/lang/order_test.clj`

**Interfaces:**

Consumes:
- `strata.values`
- `strata.runtime/charge!`

Produces:
- **`(compare-values ctx a b)`** returns a negative, zero or positive int. `ctx` may be nil.
  - **Type rank:** nil 0, boolean 1, number 2, char 3, string 4, keyword 5, symbol 6, sequential 7, map 8, set 9, Bytes 10, Handle 11, Deferred 12. A LangFn raises `error! :type-error`.
  - **Numbers** compare numerically. On a tie the subtype decides, in the order long < BigInt < double, and `nan` comes after all other numbers.
  - **Sequentials** compare element by element and then by length.
  - **Maps** compare as the sorted vector of their entries, and **sets** as the sorted vector of their elements.
  - **Keywords and symbols** compare by namespace (nil first) and then by name.
  - Comparison charges 1 fuel for each element visited.
- **`(sort-values ctx coll)`** is a stable sort using `compare-values`.

- [ ] **Step 1: Write failing tests.**
  - `ranks`: `(sort-values nil [:k "s" 1 nil true \c 'sym [1] {} #{}])` is `[nil true 1 \c "s" :k sym [1] {} #{}]`.
  - `numeric-ties`: `(compare-values nil 5 5.0)` is negative, `(compare-values nil 5 5N)` is negative, `(compare-values nil 1 2.5)` is negative, and `(compare-values nil nan 1e300)` is positive.
  - `maps`: `(compare-values nil {:a 1} {:a 2})` is negative.
  - Property `antisymmetric-transitive`: use test.check with 200 trials over a generator of nested EDN values (ints, doubles, strings, keywords, vectors, maps). Check that `(sign (cmp a b)) = (- (sign (cmp b a)))`; that `cmp = 0` exactly when `(= a b)`; and transitivity over triples.
- [ ] **Step 2: Run the tests.** They should FAIL.
- [ ] **Step 3: Implement** `src/lang/order.clj`.
- [ ] **Step 4: Run the tests again.** They should PASS.
- [ ] **Step 5: Commit** with `feat(order): total order over language values`.

### Task 6: `strata.reader`

**Spec:** §1.2 (Syntax), §6.1 (Read)

**Files:**
- Create: `src/lang/reader.clj`
- Test: `test/lang/reader_test.clj`

**Interfaces:**

Consumes:
- `strata.errors`

Produces:
- **`(read-forms source opts)`**. `source` is a String or a sequential collection of forms; `opts` holds `{:ns-name sym :max-source-bytes n :max-form-depth n}`. It returns a vector of forms carrying `:line`/`:column` metadata where available.
  - **String input:** the reader first checks the UTF-8 byte length against `:max-source-bytes`. It then runs a pre-scan that counts the nesting depth of `( [ {` and `#{`, ignoring brackets inside strings, character literals and `;` comments. Finally it reads with `clojure.tools.reader.edn/read` through `indexing-push-back-reader`, passing `{:eof sentinel :readers {} :default (fn [tag _] (error! :tagged-literal …))}`. A reader exception becomes `:read-error`, carrying the reader's line and column but not its message text.
  - **Forms input:** the reader walks the forms to check depth and rejects tagged-literal objects.
  - **Errors:** all use phase `:read`. The kinds are `:source-too-large`, `:form-too-deep`, `:tagged-literal` and `:read-error`.

- [ ] **Step 1: Write failing tests.**
  - `reads-with-locations`: `(read-forms "(ns a)\n(defrule x [1])" {})` returns 2 forms, and the second has `(:line (meta f))` equal to 2.
  - `rejects-tags`: `"#inst \"2020\""` and `"#foo 1"` both give `:tagged-literal`.
  - `rejects-clojure-only-syntax`: `"#(inc %)"`, `"@x"`, `` "`x" `` and `"#\"re\""` each throw a lang error with phase `:read`.
  - `depth-limit`: `(apply str (repeat 300 "["))` followed by the matching `"]"`s gives `:form-too-deep` when `:max-form-depth` is 256. A string literal containing 300 `[` characters does not count toward depth.
  - `size-limit`: with `:max-source-bytes 10`, a 20-byte source gives `:source-too-large`.
  - `forms-input`: `(read-forms ['(ns a) '(defn f [x] x)] {})` returns the forms unchanged.
- [ ] **Step 2: Run the tests.** They should FAIL.
- [ ] **Step 3: Implement** `src/lang/reader.clj`. Keep the pre-scan a small state machine of about 40 lines.
- [ ] **Step 4: Run the tests again.** They should PASS.
- [ ] **Step 5: Commit** with `feat(reader): EDN reader with tag policy and limits`.

---

## Milestone 2: Namespaces, built-ins, and the code language

### Task 7: `strata.ns` and the `strata.builtins` registry skeleton

**Spec:** §2 (all subsections)

**Files:**
- Create: `src/lang/ns.clj`, `src/lang/builtins.clj`
- Test: `test/lang/ns_test.clj`

**Interfaces:**

Consumes:
- `strata.errors`
- `strata.reader`

Produces:
- **`strata.builtins/registry`**: a delay that resolves to the Registry shape. It merges `strata.builtins.core/fns`, `strata.builtins.coll/fns` (both under `strata.core`), `strata.builtins.string/fns`, `strata.builtins.bytes/fns`, `strata.builtins.io/fns` and the core relations and aggregates. In this task it holds stubs: `strata.core` with `{:fn {} :relation {} :aggregate #{count count-distinct sum min max collect collect-by collect-map}}`. Later tasks add their maps by `require`, and each later builtin task edits the `merge` here.
- **`strata.builtins/special-forms`**: `#{let fn if if-let when when-let when-not cond case do loop recur and or quote -> ->> parse parse-explain}`.
- **`(parse-ns-form form)`**: returns `{:name sym :attrs {:endian :le|:be :bit-order :msb|:lsb} :requires [{:ns sym :as sym-or-nil :refer [sym…]}]}`. Any other shape is a `:bad-ns-form` error.
- **`(order-namespaces units {:builtins #{allowed-ns} :externs {ns {rel arity}}})`**: `units` is `{ns-sym [forms…]}`, where the first form must be `ns`. It returns a vector of ns syms in dependency order. The errors are `:require-cycle` (with `:data {:chain [...]}`), `:unknown-namespace`, `:ns-name-mismatch`, `:withheld-namespace`, `:reserved-namespace` (a user source named `strata.*`) and `:name-collision` (a namespace defined as two of source, extern and built-in).
- **`(empty-program registry externs)`**: returns `{:registry registry :namespaces {} :externs externs}`.
- **`(add-def prog ns-sym sym def)`**: `def` is `{:kinds #{:fn|:relation|:type} :sub :defn|:defrel|:rule|:struct|:deftype :qname qualified-sym :form f}`. A struct has kinds `#{:relation :type}`. Repeated `defrule`s of the same name merge, appending to `:clauses`. Any other redefinition is `:duplicate-definition`, and conflicting kinds are `:kind-conflict`.
- **`(resolve-name prog cur-ns sym position)`**: `position` is one of `#{:relation :fn :type :aggregate}`. It returns `{:qname qsym :def def-or-builtin-entry :builtin? bool}` or `nil`.
  - An unqualified symbol is looked up in this order: the current namespace's defs with that kind, then `:refer`s, then `strata.core` for that position.
  - A qualified symbol `a/x` resolves `a` as an alias first and then as a full namespace name; extern namespaces provide `:relation` entries.
- **`(shadow-warnings prog)`**: returns a seq of `{:ns :sym :position}` for user definitions that shadow `strata.core` names of the same kind.

- [ ] **Step 1: Write failing tests.**
  - `parse-ns`: `(parse-ns-form '(ns a.b {:endian :be} (:require [strata.string :as str] [c.d :refer [x y]])))` returns the shape described above.
  - `order`: units `{a [(ns a (:require [b]))] b [(ns b)]}` give `[b a]`. A cycle gives `:require-cycle` with the chain. Requiring `strata.io` when the builtins are `#{strata.string}` gives `:withheld-namespace`. A unit named `strata.x` gives `:reserved-namespace`.
  - `positional-resolution`: with a stub registry where `strata.core` has `force` both under `:fn` and under `:relation`, `(resolve-name p 'a 'force :fn)` and `(resolve-name p 'a 'force :relation)` return different entries, and `(resolve-name p 'a 'count :aggregate)` is non-nil.
  - `kinds`: adding `defn foo` and then `defrule foo` gives `:kind-conflict`. Adding `defrule foo` twice merges the clauses. Adding `defstruct s` makes `s` resolvable as both `:relation` and `:type`.
  - `alias-and-refer`: through `[c.d :as cd :refer [x]]`, both `cd/y` and the bare `x` resolve to `c.d`.
  - `shadow-warning`: a user `defrel elem` produces a warning at position `:relation`.
- [ ] **Step 2: Run the tests.** They should FAIL.
- [ ] **Step 3: Implement** `src/lang/ns.clj` and `src/lang/builtins.clj`.
- [ ] **Step 4: Run the tests again.** They should PASS.
- [ ] **Step 5: Commit** with `feat(ns): namespaces, ordering, positional resolution`.

### Task 8: Scalar built-ins (`strata.builtins.core`)

**Spec:** §4.4, §4.5, §4.6 (Arithmetic, Bits, Predicates)

**Files:**
- Create: `src/lang/builtins/core.clj`
- Modify: `src/lang/builtins.clj`, to merge `core/fns`
- Test: `test/lang/builtins/core_test.clj`

**Interfaces:**

Consumes:
- `strata.values`
- `strata.runtime`
- `strata.order/compare-values`

Produces: `fns`, a map of `{sym {:impl (fn [ctx & args]) :arity [min max]}}` covering the following.

**Arithmetic** (`+ - * / quot rem mod inc dec min max abs`):
- These promote on overflow (`+'` semantics). Every result passes through `canon-num` and `check-int!`.
- `/` returns a long when the division is exact and a double otherwise; it never returns a Ratio.
- Division by zero is a run error, `:arithmetic-error`.
- Any `nan` operand yields `nan`.
- `min` and `max` use `compare-values`.
- **Size charge:** each operation charges fuel equal to the sum of its operands' `weight` values, before it computes.
- **Shift guard:** `bit-shift-left` checks `(+ bitlen shift)` against `:max-int-bits` *before* shifting.

**u64 wrapping:** `u64+ u64- u64*` compute modulo 2⁶⁴ and return a long when the result is below 2⁶³, otherwise a BigInt.

**Bits:** `bit-and bit-or bit-xor bit-not bit-shift-left bit-shift-right unsigned-bit-shift-right bit-test`. They accept long or BigInt, through BigInteger operations.

**Comparison and number tests:**
- `=` and `not=` use Clojure `=`, except that `(= nan nan)` is true.
- `< <= > >=` are numeric only. Given `nan` they return false; given a non-number they are a type error.
- `compare` delegates to `compare-values`.
- `zero? pos? neg? even? odd?`.

**Predicates and misc:**
- `nil? some? string? number? integer? keyword? map? vector? set? coll? bytes? deferred? identity not`.
- `str`, `name`, `keyword`.
- `parse-long` and `parse-double` return `nil` on bad input.
- `deferred-offset` and `deferred-length`.

- [ ] **Step 1: Write failing tests.** Call each built-in through a helper `(call 'sym & args)` that looks it up in `fns` and passes `(make-ctx {})`.
  - `promotes`: `(call '+ Long/MAX_VALUE 1)` is `9223372036854775808N`.
  - `division`: `(call '/ 6 3)` is `2` and a Long; `(call '/ 1 2)` is `0.5`.
  - `u64-wrap`: `(call 'u64* 0xcbf29ce484222325 0x100000001b3)` equals `(mod (* 0xcbf29ce484222325N 0x100000001b3N) 18446744073709551616N)`, normalized to a long when it fits.
  - `shift-guard`: `(call 'bit-shift-left 1 100000)` throws `:int-too-large` *without* allocating; time it under 50 ms.
  - `nan`: `(call '+ nan 1)` is `nan`, `(call '= nan nan)` is true, and `(call '< nan 1)` is false.
  - `bit-test`: `(call 'bit-test 0x40000 18)` is true.
  - `bigint-bits`: `(call 'bit-and 18446744073709551615N 0xff)` is `255`.
  - `type-error`: `(call '< "a" 1)` throws `:type-error`.
  - `parse-fns`: `(call 'parse-long "x")` is nil, and `(call 'parse-long "42")` is 42.
- [ ] **Step 2: Run the tests.** They should FAIL.
- [ ] **Step 3: Implement** the built-ins.
- [ ] **Step 4: Run the tests again.** They should PASS.
- [ ] **Step 5: Commit** with `feat(builtins): scalar, arithmetic, bit and u64 built-ins`.

### Task 9: Collection and sequence built-ins (`strata.builtins.coll`)

**Spec:** §4.5, §4.6 (Collections, Sequences)

**Files:**
- Create: `src/lang/builtins/coll.clj`
- Modify: `src/lang/builtins.clj`
- Test: `test/lang/builtins/coll_test.clj`

**Interfaces:**

Consumes:
- `strata.values/apply-fn`
- `strata.runtime`
- `strata.order`

Produces: `fns` covering the collection and sequence built-ins listed in §4.6, plus `apply`.

**Results**
- Every sequence function returns a vector, except `set`, `group-by` and `frequencies`, which return their natural types.
- `range` needs at least one argument. An argument of 1e9 is refused before allocating: the requested count goes through `check-size!`.

**Fuel**
- Charge 1 fuel for each element visited or produced.
- Each produced collection goes through `check-size!`.

**Higher-order functions**
- Function arguments (to `map`, `filter`, `reduce`, `sort-by`, `group-by` and the rest) are invoked with `apply-fn`.
- `sort` and `sort-by` use `sort-values` and `compare-values`.

**`nth` and `get`**
- `nth` returns `nil` when out of range, rather than throwing, and also accepts an explicit default.
- `get` on a non-associative value returns `nil`.

- [ ] **Step 1: Write failing tests.**
  - `eager`: `(call 'map (->LangFn 'inc (fn [ctx [x]] (inc x))) [1 2])` is `[2 3]` and a vector.
  - `range-guard`: `(call 'range 1000000000)` throws `:value-too-large` in under 50 ms.
  - `fuel-per-element`: with `:fuel 100`, `(call 'range 1000)` throws `:fuel-exhausted`.
  - `sort-total-order`: `(call 'sort [3 "a" 1.0 :k nil])` is `[nil 1.0 3 "a" :k]`.
  - `keyword-fns`: `(call 'map :a [{:a 1} {:a 2}])` is `[1 2]`.
  - `apply`: `(call 'apply plus-fn [1 2 3])` returns 6.
  - `nth-safe`: `(call 'nth [1] 5)` is nil.
- [ ] **Step 2: Run the tests.** They should FAIL.
- [ ] **Step 3: Implement** the built-ins.
- [ ] **Step 4: Run the tests again.** They should PASS.
- [ ] **Step 5: Commit** with `feat(builtins): eager collection and sequence built-ins`.

### Task 10: `strata.string`

**Spec:** §4.6 (`strata.string`), §4.5

**Files:**
- Create: `src/lang/builtins/string.clj`
- Modify: `src/lang/builtins.clj`
- Test: `test/lang/builtins/string_test.clj`

**Interfaces:**

Produces: `fns` for every `strata.string` function in §4.6.

**`split`** splits on a **literal** separator, keeps trailing empty strings, and returns a vector.

**Regex functions** (`re-find`, `re-matches`, `re-seq`, `re-split`):
- The pattern is a String no longer than `:max-regex-length`; a longer one throws `:regex-too-long`.
- An invalid pattern is a `:bad-regex` run error.
- The input is wrapped in a `CharSequence` whose `charAt` calls `(charge! ctx 1)` and checks `Thread/interrupted`.

**Results:**
- Every function charges fuel by characters.
- `pad-left` and `pad-right` run `check-size!` on the target length before building the string.

- [ ] **Step 1: Write failing tests.**
  - `split-literal`: `(call 'split "a.b.c" ".")` is `["a" "b" "c"]`; the dot is not a regex.
  - `pad-guard`: `(call 'pad-left "" 1000000000 \x)` throws `:value-too-large` quickly.
  - `regex-fuel`: `(call 're-matches "(a|aa)*b" (apply str (repeat 5000 "a")))` with `:fuel 100000` throws `:fuel-exhausted` or `:stack-exhausted` (the latter inside `run-isolated`), never a raw JVM error.
  - `regex-length`: a 2000-character pattern gives `:regex-too-long`.
- [ ] **Step 2: Run the tests.** They should FAIL.
- [ ] **Step 3: Implement** `strata.string`.
- [ ] **Step 4: Run the tests again.** They should PASS.
- [ ] **Step 5: Commit** with `feat(builtins): strata.string with fuel-metered regex`.

### Task 11: `strata.bytes`

**Spec:** §4.5 (bad data returns nil), §4.6 (`strata.bytes`)

**Files:**
- Create: `src/lang/builtins/bytes.clj`
- Modify: `src/lang/builtins.clj`
- Test: `test/lang/builtins/bytes_test.clj`

**Interfaces:**

Consumes:
- `strata.values` (Bytes)
- `strata.runtime` (`alloc-bytes!`, `limit`)

Produces: `fns` for every `strata.bytes` function in §4.6.

**Returns `nil` on bad data:** out-of-range reads, malformed decodes, `hex-decode` on input that isn't valid hex, and `inflate` given a corrupt stream or output larger than its maximum.

**`(inflate bs max)` and `(inflate bs max :raw)`:**
- The effective maximum is `(min max (limit ctx :max-inflate))`.
- The function decompresses with `java.util.zip.Inflater`, using `nowrap` for `:raw`. It reads in chunks and stops as soon as the output exceeds the maximum.
- The output size counts against `alloc-bytes!`.

**Encodings:** `cp1252` uses `Charset/forName "windows-1252"`. `ascii` returns `nil` when any byte is above 127.

**Checksums and hashes:** `crc32` (java.util.zip.CRC32) returns a long; `fnv1a64` returns a u64 as a long or BigInt; `sha1` returns Bytes.

**Arguments and fuel:**
- Every function returns `nil` on bad data, but a type error (for example a string where Bytes are expected) throws `:type-error`.
- Fuel is charged at `(max 1 (quot n 1024))` per call.

- [ ] **Step 1: Write failing tests.**
  - `reads`: given Bytes `[0x01 0x02 0x03 0x04]`, `u32-le` gives `0x04030201` and `u32-be` gives `0x01020304`. `(u32-le b 1)` is nil, and so is `(u64-le b 0)`.
  - `u64`: the Bytes `[0xff ×8]` give `18446744073709551615N` from `u64-le`.
  - `f32`: the Bytes `[0 0 0xc0 0x7f]` (an f32 NaN, little-endian) give `nan` from `f32-le`.
  - `cp1252-high-range`: `(cp1252 (bytes [0x80 0x9f]))` is `"€Ÿ"`. `(utf8 (bytes [0xc3]))` is nil, and `(ascii (bytes [0x80]))` is nil.
  - `inflate`: a round trip with `java.util.zip.Deflater` on 10 KB of data works. With `max 100` on 10 KB of output the result is nil. A corrupt stream gives nil.
  - `inflate-bomb`: 1 MB of zeros deflated, inflated with `max 1000`, returns nil in under 100 ms and records less than 64 KB in `alloc-bytes!`.
  - `fnv1a64`: `(fnv1a64 (encode-utf8 "a"))` is `0xaf63dc4c8601ec8cN`, normalized.
  - `crc32`: `(crc32 (encode-utf8 "123456789"))` is `0xCBF43926`.
  - `hex`: `(hex-encode (bytes [0xab 1]))` is `"ab01"`, and `(hex-decode "zz")` is nil.
- [ ] **Step 2: Run the tests.** They should FAIL.
- [ ] **Step 3: Implement** `strata.bytes`.
- [ ] **Step 4: Run the tests again.** They should PASS.
- [ ] **Step 5: Commit** with `feat(builtins): strata.bytes decoders, inflate, checksums`.

### Task 12: Code analyzer (`strata.analyze.code`)

**Spec:** §4.1, §4.3, §3.3 (?vars as locals), §5.3 (positional symbols)

**Files:**
- Create: `src/lang/analyze/code.clj`
- Test: `test/lang/analyze/code_test.clj`

**Interfaces:**

Consumes:
- `strata.ns/resolve-name`
- `strata.builtins/special-forms`
- `strata.errors`

Produces:

**`(analyze prog cur-ns form scope)`** returns a code AST node. `scope` is:

```clojure
{:locals {sym local-id}        ; also holds ?vars and $pos/$start/$remaining when provided
 :tail? bool
 :loop {:arity n}              ; or nil
 :next-id (atom long)}         ; fresh-id counter
```

`(new-scope)` creates an empty scope.

**AST node ops:**

```
{:op :const :val v}
{:op :local :id id}
{:op :fn-ref :qname q :builtin? b :impl f-or-nil}       ; a function used as a value
{:op :call-builtin :name q :impl f :args [n…]}
{:op :call-defn :qname q :args [n…]}
{:op :invoke :f n :args [n…]}                           ; dynamic: a LangFn or keyword value
{:op :kw-invoke :kw k :args [n…]}
{:op :if :test :then :else}
{:op :let :bindings [[id n]…] :body n}
{:op :do :exprs [n…]}
{:op :fn :self id-or-nil :arities [{:params [id…] :rest id-or-nil :body n}]}
{:op :loop :bindings [[id n]…] :body n}
{:op :recur :args [n…]}
{:op :and :exprs} {:op :or :exprs}
{:op :case :test n :clauses [[const-set n]…] :default n-or-nil}
{:op :parse :explain? b :type type-form :ns cur-ns :args [n…]}   ; the type is analyzed in Task 14
{:op :vector :items} {:op :map :pairs} {:op :set :items}         ; non-constant literals
```

Every node carries `:loc` (from `loc-of`).

**Desugaring:**
- `when`, `when-not`, `when-let`, `if-let`, `cond`, `->` and `->>` desugar into the core ops above.
- `quote` gives `:const`, and ground literals give `:const`.

**Destructuring** in `let`, `fn` and `loop` params supports:
- vectors with `&` and `:as`;
- maps with `:keys`, `:strs`, `:or` and `:as`.

It expands into `:let` with internal calls to the `nth`, `get` and `subvec` built-ins, resolved from the `strata.core` registry.

**Errors** (phase `:analyze`):
- `:unresolved-symbol` for an unknown symbol;
- `:relation-in-code` for a symbol that resolves only as a relation, with a message suggesting `bind`;
- `:recur-not-tail` for a `recur` that isn't in tail position;
- `:recur-arity` for a `recur` whose argument count doesn't match its loop or fn;
- `:arity-error` when a built-in or `defn` is called with the wrong number of arguments and the arity is statically known.

**Rules for symbols:**
- Symbols naming Java classes, `.method` forms, `new`, `set!`, `def`, `var` and `throw` are rejected as `:unresolved-symbol`.
- No symbol is ever passed to Clojure's own resolution.

- [ ] **Step 1: Write failing tests.** Use a helper that builds a program with an `a` namespace, one `defn` `a/f` (arity 1), and the registry from Tasks 8–11.
  - `basic-ops`: `(analyze p 'a '(if (pos? x) (inc x) 0) scope-with-x)` returns `:op :if` with a `:call-builtin` test.
  - `desugar`: `(when-let [y (f x)] y)` analyzes to an `:let`/`:if` shape that contains no `when-let`.
  - `destructure`: `(let [[a b & r] v {:keys [k]} m] [a k])` analyzes without error; its emitted calls use the `nth`, `get` and `subvec` impls.
  - `tail-check`: `(loop [i 0] (inc (recur i)))` gives `:recur-not-tail`.
  - `illegal-symbols`: `(System/exit 0)`, `(.length "x")`, `(new Object)` and `(clojure.core/eval 1)` each give `:unresolved-symbol`.
  - `relation-in-code`: when `a/r` is a `defrel`, `(r 1)` gives `:relation-in-code`.
  - `kw-invoke`: `(:k m)` gives `:op :kw-invoke`.
  - `static-arity`: `(f 1 2)` gives `:arity-error`.
- [ ] **Step 2: Run the tests.** They should FAIL.
- [ ] **Step 3: Implement** `strata.analyze.code`.
- [ ] **Step 4: Run the tests again.** They should PASS.
- [ ] **Step 5: Commit** with `feat(analyze): code analyzer with desugaring, destructuring, tail checks`.

### Task 13: Code compiler (`strata.compile.code`)

**Spec:** §4.1, §4.3, §4.4, §7.4, §8.1

**Files:**
- Create: `src/lang/compile/code.clj`
- Test: `test/lang/compile/code_test.clj`

**Interfaces:**

Consumes:
- the code AST from Task 12;
- `strata.values` (LangFn, `apply-fn`);
- `strata.runtime` (`charge!`, `with-depth`).

Produces:
- **`(compile-node node fn-table)`** returns `(fn [ctx env] value)`. `fn-table` is an atom holding `{qname LangFn}`, filled after every `defn` compiles so that forward references resolve at call time.
- **`(compile-defn analyzed-defn fn-table)`** returns a LangFn. Its `analyzed-defn` argument is `{:qname :arities [...]}` and comes from `(analyze-defn prog ns form)`, which this task adds to `strata.analyze.code`.
- **`(eval-code ctx compiled env)`** runs a compiled closure inside `with-call-budget`. It is the top-level entry point used by the engine and the struct parsers.

**Charging and depth:**
- Every `:call-*` and `:invoke` charges 1 fuel and runs inside `with-depth`.
- Every `:recur` iteration charges 1 fuel.

**`recur`** returns a private `Recur` sentinel record. The `:loop` node and `fn` bodies check for it in a Clojure `loop`. This works because `recur` is guaranteed to be in tail position.

**Values:**
- A `:fn` node yields a LangFn that captures `env`.
- A `defn` call with the wrong arity at run time throws `:arity-error`.

- [ ] **Step 1: Write failing tests.** Use a helper `(run-code src-forms expr)` that loads a single namespace of `defn`s through Tasks 7, 12 and 13 and evaluates `expr` with a fresh ctx.
  - `factorial`: `(defn fact [n] (if (zero? n) 1 (* n (fact (dec n)))))` gives `(fact 20)` = `2432902008176640000`, and `(fact 25)` is a BigInt.
  - `loop-recur`: `(loop [i 0 acc 0] (if (< i 10) (recur (inc i) (+ acc i)) acc))` is 45.
  - `closures`: `((fn [x] (fn [y] (+ x y))) 1)` applied to 2 through `apply-fn` gives 3.
  - `forward-ref`: `(defn a [] (b))` followed by `(defn b [] 7)` gives 7.
  - `mutual-recursion`: `even2?` and `odd2?` work on 100.
  - `fuel`: `(loop [] (recur))` with `:fuel 10000` throws `:fuel-exhausted`.
  - `depth`: `(defn r [n] (inc (r n)))` throws `:depth-exceeded`, not a StackOverflowError. Run this test inside `run-isolated`.
  - `destructure-runtime`: `(let [{:keys [a] :or {a 5}} {}] a)` is 5.
  - `case`: `(case x 1 :one (2 3) :few :many)` works for 1, 3 and 9.
- [ ] **Step 2: Run the tests.** They should FAIL.
- [ ] **Step 3: Implement** `strata.compile.code`.
- [ ] **Step 4: Run the tests again.** They should PASS.
- [ ] **Step 5: Commit** with `feat(compile): closure compiler for the code language`.

---

## Milestone 3: Structs

### Task 14: Struct analyzer (`strata.analyze.struct`)

**Spec:** §5.1–§5.4, §2.1 (ns attrs)

**Files:**
- Create: `src/lang/analyze/struct.clj`
- Test: `test/lang/analyze/struct_test.clj`

**Interfaces:**

Consumes:
- `strata.ns`
- `strata.analyze.code/analyze`, used for expressions with a scope containing params, earlier fields and `$pos`/`$start`/`$remaining`.

Produces:

**`(analyze-struct prog ns form)`** returns:

```clojure
{:qname q
 :params [{:sym s :id id}…]
 :endian :le|:be                          ; resolved lexically: struct opt > ns attr > :le
 :bit-order :msb|:lsb                     ; struct opt > ns attr > :msb
 :pos-ids {:pos id :start id :remaining id}
 :fields [{:sym s :key kw-or-nil :hidden? b :id id :type type-ast}…]}
```

`:key` is nil for `_`, and `:hidden?` is true for `_x` fields.

**`(analyze-deftype prog ns form)`** returns `{:qname :params [...] :type type-ast}`.

**`(analyze-type prog ns form scope endian bit-order)`** analyzes a single inline type form into a type AST. It is used by `parse` in code (Task 16).

**Type AST** (`:t` is the discriminator):

```
{:t :prim :prim :u8…:f64 :endian e}
{:t :bytes :n expr-or-:rest}
{:t :string :n expr :enc kw}
{:t :cstring :enc kw :max n}
{:t :const :bytes [ints…] :val v}
{:t :array :elem T :n expr}
{:t :repeat :elem T :mode :eos|:until|:sentinel :pred expr-or-nil :max n}
{:t :if :test expr :then T}
{:t :switch :test expr :cases [[const T]…] :default T-or-nil}
{:t :enum :elem T :map {raw kw}}
{:t :bits :n int :order :msb|:lsb}
{:t :calc :expr e}
{:t :assert :expr e}
{:t :skip :n expr}
{:t :align :n expr}
{:t :at :off expr :elem T}
{:t :sized :n expr :elem T}
{:t :decode :n expr-or-:rest :f expr :elem T}
{:t :try :elem T}
{:t :defer :n expr-or-:rest :elem T}
{:t :ref :qname q :args [expr…]}            ; to a struct
{:t :alias :qname q :args [expr…]}          ; to a deftype
```

**Rules:**
- `[:u32 :be]` overrides the endianness for that field.
- Endianness is resolved **at analysis time**, never at parse time.
- `:repeat` defaults to `:max 1000000`, and `:cstring` defaults to `:max 65536`.
- `:const` strings are converted to their ASCII bytes.

**Errors** (phase `:analyze`): `:unknown-type`, `:type-arity` (a parameterized type used bare, or the wrong number of arguments), `:bad-type-form`, and `:unresolved-symbol` inside expressions (including references to *later* fields).

- [ ] **Step 1: Write failing tests.**
  - `endian-lexical`: in `(ns a {:endian :be})`, `(defstruct s [x :u32 y [:u32 :le]])` gives `x` endian `:be` and `y` endian `:le`.
  - `hidden-fields`: in `(defstruct s [_a :u8 _ :u8 b [:calc _a]])`, `_a` has `:hidden? true` and `_` has key nil.
  - `forward-field-ref-rejected`: `(defstruct s [a [:bytes b] b :u8])` gives `:unresolved-symbol`.
  - `params`: `(defstruct p [n] [xs [:array :u8 n]])` analyzes; `[:sized 4 p]` gives `:type-arity`, while `[p 4]` is fine.
  - `switch-default`: `[:switch t {1 :u8} :u16]` gives a `:default` prim of `:u16`.
  - `positional`: `[:calc $start]` resolves `$start` to the `:pos-ids :start` id.
  - `const-string`: `[:const "MZ"]` gives `:bytes [77 90]`.
- [ ] **Step 2: Run the tests.** They should FAIL.
- [ ] **Step 3: Implement** `strata.analyze.struct`.
- [ ] **Step 4: Run the tests again.** They should PASS.
- [ ] **Step 5: Commit** with `feat(analyze): struct and deftype analyzer`.

### Task 15: Struct compiler, core types (`strata.compile.struct`)

**Spec:** §5.2–§5.5, §5.8

**Files:**
- Create: `src/lang/compile/struct.clj`
- Test: `test/lang/compile/struct_test.clj`

**Interfaces:**

Consumes:
- the type AST from Task 14;
- `strata.compile.code/compile-node`;
- `strata.resource` (ByteSource);
- `strata.runtime`.

Produces:
- **`(compile-type T struct-table fn-table)`** returns a parser `(fn [ctx cur env] → Res-or-nil)`. `struct-table` is an atom holding `{qname compiled-struct}`.
- **`(compile-struct analyzed struct-table fn-table)`** returns `{:qname q :arity (count params) :parse (fn [ctx src off args] → {:value v :end n} or nil)}`. The struct's `:parse` charges 1 fuel per field and runs inside `with-depth`.
- **`(explain-parse ctx compiled src off args)`** returns `{:ok true :value :end}` or `{:ok false :path [...] :offset n :reason kw}`, where `:reason` is one of `:eof :const :assert :switch :cstring :encoding :window :bad-size :repeat-max :zero-progress :decode`. The failure path is recorded by a dynamic var bound only during an explain.
- **`(struct-relation compiled)`** returns a computed relation entry. Its arity is `4 + param count` and its single mode is `in [0 1 2…] out [last-1 last]`. The impl returns `[[value end]]` or `[]`, and is memoized through `memo-get`/`memo-put!` on the key `[qname src-id off args]`.

This task covers every type in the §5.4 table **except** `:bits`, `:decode`, `:defer` and handle-source specifics, which Task 16 adds. Bytes sources must work end to end here. The value semantics follow §5.2:
- an `:if` whose test is false and a failed `:try` leave their key out;
- `_` fields are dropped and `_x` fields are hidden;
- the windows of `:sized` and `:at` follow the spec exactly.

- [ ] **Step 1: Write failing tests.** Use a helper `(parse-src forms struct-sym byte-vec)` that loads the namespace and returns `{:value :end}` or nil.
  - `prims-endian`: a `:u16 :u32 :i8 :f64` round-trip against a test encoder, for both `:le` and `:be`.
  - `u64-full`: eight `0xff` bytes give `18446744073709551615N`.
  - `sized-exact`: `[a [:sized 4 [:u8]] b :u8]` on `[1 2 3 4 5]` gives `{:a 1 :b 5}`. An inner type that reads 5 bytes fails.
  - `at-zero-width`: `[o :u8 x [:at o :u8] y :u8]` on `[2 9 7]` gives `x` 7 and `y` 9.
  - `repeat-modes`: test `:eos`; `:until` (includes the terminator); and `:sentinel` (drops it). An `:eos` repeat with a zero-width element fails with reason `:zero-progress`. Exceeding `:max` gives `:repeat-max`.
  - `cstring`: `[s [:cstring :ascii :max 4]]` on `"abcdef\0"` fails, and on `"ab\0"` gives `"ab"` with `:end` 3.
  - `string-trims-nul`: `[:string 8 :ascii]` on `".text\0\0\0"` gives `".text"`.
  - `try-and-if-omit`: `[a [:try [:const "X"]] b [:if false :u8] c :u8]` gives a value of `{:c …}` only.
  - `switch`: no match and no default fails with reason `:switch`.
  - `enum-unknown`: an unknown raw value is kept as the integer.
  - `params`: `(defstruct p [n] [xs [:array :u8 n]])` referenced as `[p 2]` works.
  - `recursion`: a struct that references itself through `:if` parses nested data of depth 3. Nesting 1000 deep gives `:depth-exceeded`.
  - `eof-edges` (Review Focus 1): parsing `:u8` on `[]` gives nil; `[:bytes 0]` on `[]` gives an empty Bytes; `[:bytes :rest]` at EOF gives an empty Bytes; an `:at` offset equal to the source size gives nil for `:u8`. None of these throw.
  - `explain`: `(explain-parse …)` on a failing `:const` gives `{:ok false :reason :const :path [:magic] :offset 0}`.
  - `bad-size-type`: a size expression returning `"x"` throws `:type-error` (a program bug); one returning nil fails the parse.
- [ ] **Step 2: Run the tests.** They should FAIL.
- [ ] **Step 3: Implement** `strata.compile.struct`. Use a `Res` record with fields `value` and `cur`. A struct's field env maps each field id, the param ids and the position ids.
- [ ] **Step 4: Run the tests again.** They should PASS.
- [ ] **Step 5: Commit** with `feat(compile): struct parser compiler (core types)`.

### Task 16: Struct compiler, bits, decode, defer and handles, plus `parse` in code

**Spec:** §5.3 (frames), §5.4 (bit fields, `:decode`, `:defer`), §5.6, §5.8

**Files:**
- Create: `src/lang/builtins/io.clj`
- Modify: `src/lang/compile/struct.clj`, `src/lang/compile/code.clj` (`:parse` op), `src/lang/builtins/core.clj` (`force` fn), `src/lang/builtins.clj` (core relations `force`, `elem`, `indexed`, `entry`, `between`, plus merging `io/fns`)
- Test: `test/lang/compile/struct2_test.clj`

**Interfaces:**

Produces:
- **`:bits`**: a shared bit cursor in `cur`. The two orders follow §5.4 bit fields: `:msb` takes high bits first, earlier bits more significant; `:lsb` takes low bits first, earlier bits less significant. Any non-`:bits` field realigns to the next byte first.
- **`:decode`**: takes `n` bytes, applies the function through `apply-fn`, and parses `elem` in a new frame `{:frame result-bytes :pos 0 :end (bsize result)}`. The result's size counts against `alloc-bytes!`. A nil or non-Bytes result fails with `:decode`.
- **`:defer`**: consumes `n` bytes and yields `(->Deferred src-id src off n type-id force-fn args)`. `type-id` is `[qname-or-inline-hash args]`. The `force-fn` parses within the window `[off, off+n)`, and is memoized under the key `[:force d]`.
- **`(force-value ctx d)`**: forcing the value `nil` returns nil.
- **Handle sources:** every read through `src-read` works with the page cache from Task 4.
- **The `:parse` op in code:** the type form is analyzed with `analyze-type`, which is exported from Task 14 for inline types. Arguments are evaluated. The result is `{:value :end}` or nil, and `parse-explain` returns the explain map.
- **`strata.io` built-ins** (`src/lang/builtins/io.clj`):
  - `(open name)` uses `strata.resource/open-handle` and returns a Handle or nil;
  - `(size h)`;
  - `(read-bytes h off len)` returns nil on a short read or a negative argument. It checks `len` against `:max-read` (`:read-too-large`) and counts it against `alloc-bytes!`;
  - `(read-all h)` is the same as `(read-bytes h 0 (size h))`.
- **Tracing:** every struct `:parse` call emits `(trace! ctx {:event :parse :type qname :off off})`, and so does every force of a deferred value.
- **Core relations** (computed relation entries in `strata.core`):
  - `elem [coll x]`: in `[0]`, out `[1]`;
  - `indexed [coll i x]`: in `[0]`, out `[1 2]`;
  - `entry [m k v]`: in `[0]`, out `[1 2]`;
  - `force [d v]`: in `[0]`, out `[1]`;
  - `between [lo hi i]`: in `[0 1]`, out `[2]`, charging 1 fuel per integer.

  A nil input yields `[]`. A map's `elem` yields `[k v]` vectors.

- [ ] **Step 1: Write failing tests.**
  - `bits-msb`: `[a [:bits 3] b [:bits 5]]` on `[0b10100011]` gives a=5, b=3.
  - `bits-lsb`: the same struct with `{:bit-order :lsb}` gives a=3 (the low 3 bits) and b=20.
  - `bits-realign`: `[a [:bits 4] b :u8]` on `[0xF0 0x07]` gives b=7.
  - `decode-frame`: a `:decode` with a function that reverses the bytes, followed by `[x [:at 0 :u8]]` inside, reads from the *decoded* buffer.
  - `decode-inflate`: a struct using `b/inflate` over a deflated payload parses the inner fields.
  - `defer-lazy`: a struct with `[d [:defer 4 bad-struct]]` succeeds even though `bad-struct` would fail. `(force d)` then gives nil, and `deferred-offset` gives the correct offset.
  - `defer-equality`: deferred values from two parses of the same source are `=`.
  - `handle-source`: parsing through a Handle over a `bytes-resource` gives results identical to parsing the Bytes directly.
  - `parse-in-code`: `(parse [:cstring :ascii] bs)` and `(parse p bs 0)` with a parameterized `[p 2]` work. `(parse-explain …)` returns a map containing `:reason`.
  - `core-relations`: `between` 0 3 gives `[[0] [1] [2]]`, and `elem` over nil gives `[]`.
  - `io`: `(read-bytes h 0 10)` on a 5-byte resource is nil. With `:max-read 4`, `(read-bytes h 0 5)` gives `:read-too-large`. `(open "missing")` is nil.
- [ ] **Step 2: Run the tests.** They should FAIL.
- [ ] **Step 3: Implement** the additions.
- [ ] **Step 4: Run the tests again.** They should PASS.
- [ ] **Step 5: Commit** with `feat(compile): bits, decode frames, deferred values, parse in code`.

---

## Milestone 4: Rules and the engine

### Task 17: Rule and `defrel` analysis and checks (`strata.analyze.rule`)

**Spec:** §3 (all subsections), §4.2, §6.1 (Check)

**Files:**
- Create: `src/lang/analyze/rule.clj`
- Test: `test/lang/analyze/rule_test.clj`

**Interfaces:**

Consumes:
- `strata.ns`
- `strata.analyze.code/analyze`, used for expressions with `?vars` as locals.

Produces:

**`(analyze-rule prog ns form)`** returns:

```clojure
{:rel q
 :ordered? b
 :loc …
 :nvars n                          ; variables are numbered 0..n-1; each `_` gets its own index
 :var-names {sym idx}
 :head [term…]
 :aggs [{:pos i :agg sym :args [var-idx…]}…]
 :body [lit…]}
```

Terms are `{:var i}`, `{:const v}` or `{:expr ast :vars #{i…}}`.

Literals:

```
{:lit :rel :rel q :computed? b :args [term…]}
{:lit :not :rel q :args [term…]}
{:lit :when :expr ast :vars #{…}}
{:lit :bind :pat pat :expr ast :vars #{…} :nil-ok? b}
```

Patterns are `{:pvar i}`, `{:pconst v}`, `{:pvec [pat…] :rest pat-or-nil}` and `{:pmap [[k pat]…]}`.

**`(analyze-defrel prog ns form)`** returns `{:qname q :params [sym…] :modes [{:in [idx…] :out [idx…] :body code-ast :param-ids [id…]}]}`. Compile it with `(compile-defrel analyzed fn-table)`, which returns a computed relation entry. Each mode's impl runs `eval-code` and validates the result:
- a coll of vectors, each with `(count out)` elements; or
- for a mode with no outputs, a truthy or falsy value.

Anything else is `:bad-relation-result`.

**`(check-program prog analyzed-rules)`** reports these errors, all in phase `:check`:

| Error | Condition |
|---|---|
| `:undefined-relation` | A literal names an unknown relation. A relation that is referenced but has no clauses counts as unknown too. |
| `:arity-mismatch` | A literal's argument count doesn't match the relation, or clauses of one relation have different arities. |
| `:fn-as-relation` | A literal names a `defn`; the message suggests `defrel`/`bind`. |
| `:expression-in-stored-literal` | An expression appears in a stored-relation literal, a head, or an output position. |
| `:unsafe-head-var` | A head variable is not bound by the body. |
| `:unbound-in-negation` | A variable in `not` is not bound by an earlier positive literal. |
| `:aggregate-multiple-clauses` | An aggregate relation has more than one clause. |
| `:fact-not-ground` | A fact (a rule with no body) has a non-ground head. |
| `:wildcard-in-head` | A `_` appears in a head. |
| `:foreign-rule` | A namespace defines a clause for another namespace's rule. |
| `:mode-coverage` | A `defrel` mode's `in` plus `out` isn't exactly the param set. |

**Constant vs expression:** a vector, map or set literal that is ground is a constant; a list is always an expression.

- [ ] **Step 1: Write failing tests.**
  - `terms`: `(defrule r [?x] (s ?x _ _))` gives two distinct wildcard indexes.
  - `expr-input`: `(elem (:descs ?t) ?d)` gives an arg 0 that is an `:expr` with `:vars #{t}`.
  - `expr-in-stored`: `(s (inc ?x))`, where `s` is a rule, gives `:expression-in-stored-literal`.
  - `undefined-relation` (Review Focus 3): `(defrule r [?x] (nope ?x))` gives `:undefined-relation` with `:data {:sym nope}`.
  - `fn-as-relation`: with `(defn f [x] x)`, the literal `(f ?x)` gives `:fn-as-relation`.
  - `unsafe-head`: `(defrule r [?x ?y] (s ?x))` gives `:unsafe-head-var`.
  - `bind-patterns`: `(bind {:a ?a :b [?c & ?d]} expr)` produces the nested patterns.
  - `aggregate-one-clause`: two clauses for `(defrule c [?k (count ?x)] …)` give `:aggregate-multiple-clauses`.
  - `facts`: `(defrule m ["png" 1])` becomes a fact with no body, and `(defrule m [?x])` gives `:fact-not-ground`.
  - `defrel-modes`: `hex` with two modes analyzes. A mode `[a -> ]` on params `[a b]` gives `:mode-coverage`.
  - `defrel-bad-result`: a mode returning `5` gives `:bad-relation-result` at run time.
- [ ] **Step 2: Run the tests.** They should FAIL.
- [ ] **Step 3: Implement** `strata.analyze.rule`.
- [ ] **Step 4: Run the tests again.** They should PASS.
- [ ] **Step 5: Commit** with `feat(analyze): rules, defrel, and program checks`.

### Task 18: Planner (`strata.plan`)

**Spec:** §6.2

**Files:**
- Create: `src/lang/plan.clj`
- Test: `test/lang/plan_test.clj`

**Interfaces:**

Consumes:
- the rule AST from Task 17;
- `computed` (a map from qname to computed relation entry);
- `stored?` (a set of qnames).

Produces:
- **`(plan-body rule computed {:pinned lit-idx-or-nil})`** returns `{:steps [step…]}`. Each step is the literal plus `:bound-before #{var-idx}`, and, for a computed literal, `:mode` (the mode index), `:in-terms` and `:out-terms`. For a stored literal it adds `:mask`, a vector of booleans marking the bound argument positions.
- **Readiness and preference** follow §6.2 exactly:
  - **readiness** comes first;
  - **preference** runs filters, then `bind`/`bind-nil`, then stored relations (most bound arguments first), then computed relations;
  - **ties** go to textual order;
  - **`:ordered? true`** keeps textual order but still verifies readiness.
- **Errors:** `:unplannable`, phase `:plan`, with `:data {:literal (safe-str lit) :missing #{var-names}}`.
- **Mode choice:** among the applicable modes, the one with the most inputs bound wins, and the first declared wins a tie. Output terms that are already bound become post-filters.
- **`(delta-variants rule recursive-rels)`** returns one plan per body literal whose relation is in `recursive-rels`, with that literal pinned first and marked `:delta? true`.
- **`(index-requirements plans)`** returns `{qname #{mask…}}`.

- [ ] **Step 1: Write failing tests.**
  - `filters-early`: `(a ?x) (b ?y) (when (pos? ?x))` puts the `when` immediately after `a`.
  - `bind-before-scan` (review I4): `(a ?x) (b ?y) (bind ?k (f ?x)) (c ?k ?y)` yields the order a, bind, then c or b by bound count. Assert that the `bind` step comes before `b`.
  - `mode-choice`: for `hex`, with `?s` bound and `?bs` free, the mode `[s -> bs]` is chosen.
  - `unplannable`: `(defrel g [a b] ([a -> b] …))` used as `(g ?x ?y)` with nothing binding `?x` gives `:unplannable` with `:missing #{?x}`.
  - `ordered`: `{:ordered true}` keeps the textual order, and errors if that order is not ready.
  - `delta`: `ancestor`'s recursive clause gives one variant, whose first step is a `:delta? true` `ancestor` literal.
  - `index-reqs`: `(parent ?a ?b) (ancestor ?b ?c)` with `?b` bound gives mask `[true false]` for `ancestor`.
- [ ] **Step 2: Run the tests.** They should FAIL.
- [ ] **Step 3: Implement** `strata.plan`.
- [ ] **Step 4: Run the tests again.** They should PASS.
- [ ] **Step 5: Commit** with `feat(plan): deterministic body planner and delta variants`.

### Task 19: Stratifier (`strata.stratify`)

**Spec:** §6.3

**Files:**
- Create: `src/lang/stratify.clj`
- Test: `test/lang/stratify_test.clj`

**Interfaces:**

Produces:
- **`(stratify rules stored?)`** returns a vector of strata in evaluation order. Each stratum is `{:rels #{q} :rules [rule…] :recursive? b}`.
  - The graph uses Tarjan's SCC algorithm over the stored relations, with an edge from each head to each body literal relation.
  - An edge is **negative** when it comes from a `not`, and also for every body edge of a rule that has aggregates.
  - Extern and fact-only relations are included.
- **Errors:** `:negative-cycle`, phase `:stratify`, with `:data {:cycle [q…]}`.

- [ ] **Step 1: Write failing tests.**
  - `linear`: `a ← b ← c` gives the strata in the order c, b, a.
  - `recursive-scc`: `ancestor` forms one stratum with `:recursive? true`.
  - `negation-ok`: `p ← q, not r` puts `r`'s stratum before `p`'s.
  - `negative-cycle`: `p ← not q` together with `q ← p` gives `:negative-cycle` with `:cycle` containing p and q.
  - `aggregate-cycle`: an aggregate over itself gives `:negative-cycle`.
- [ ] **Step 2: Run the tests.** They should FAIL.
- [ ] **Step 3: Implement** `strata.stratify`.
- [ ] **Step 4: Run the tests again.** They should PASS.
- [ ] **Step 5: Commit** with `feat(stratify): SCC stratification with negative-cycle detection`.

### Task 20: Engine (`strata.engine`)

**Spec:** §6.4, §3.3–§3.5, §4.2 (memoization)

**Files:**
- Create: `src/lang/engine.clj`
- Test: `test/lang/engine_test.clj`

**Interfaces:**

Consumes:
- plans (Task 18) and strata (Task 19);
- compiled code (`eval-code`);
- computed relation entries;
- `strata.order`, `strata.runtime` and `strata.values`.

Produces:
- **`(evaluate ctx {:strata :plans :computed :edb})`** returns `{qname #{tuple…}}`. `edb` is `{qname #{tuple}}`, holding host facts plus ground `defrule` facts.
- **`(evaluate-naive ctx same-args)`** is a reference implementation. It reruns every rule until nothing changes, uses the same step machinery, and exists for tests.

**Steps** are push-based: `(fn [ctx bindings emit])`, where `bindings` is a persistent vector of length `nvars` holding nil for unbound positions, with bound-ness tracked by the plan.

| Literal | Behavior |
|---|---|
| Stored | Probes the index for its mask. A `:delta?` literal probes the delta set instead. |
| Computed | Evaluates the input terms, which may be expressions, then calls the impl inside `with-call-budget` and with memoization on `[qname mode-idx inputs]`. It binds or filters the outputs. |
| `when` | Evaluates its expression. |
| `bind` | Matches the pattern. Without `:nil-ok?`, it fails when the value or any destructured value is nil. |
| `not` | Probes for existence. |

**Metering:**
- Every candidate binding a step emits charges 1 fuel.
- Every insert charges `(weight tuple)` and runs `storable?`; a non-storable tuple throws `:unstorable-value`.
- Every insert is counted against `:max-tuples`, both in total and per relation, and exceeding it throws `:tuple-limit` with `:data {:rel q}`.
- Iterations are counted against `:max-iterations`, and exceeding it throws `:iteration-limit` with `:data {:rel q}`.

**Aggregates** follow §3.4. Groups are keyed by the non-aggregate head terms, and the input is the distinct full assignments, with wildcards counting as variables.
- `count`: the number of assignments.
- `count-distinct`: the number of distinct argument values.
- `sum`: sums the values sorted by `compare-values`. A non-number is a `:type-error`.
- `min` and `max`: under the total order.
- `collect`: a set.
- `collect-by`: sorts by `[k v]`.
- `collect-map`: a duplicate key with a different value throws `:collect-map-conflict`.

**`stats`:** the engine records per-relation tuple counts and iteration counts in `ctx` diagnostics under `:stats`.

- [ ] **Step 1: Write failing tests.** Use a helper `(run-prog forms edb)` that runs the full pipeline (Tasks 7–19) and calls `evaluate` with a fresh ctx; `strata.program` (Task 21) doesn't exist yet. Write the helper in `test/lang/engine_test.clj` and move it to `strata.program` in Task 21.
  - `transitive-closure`: `ancestor` over a chain of 50 gives 1275 tuples.
  - `negation`: `(defrule orphan [?x] (person ?x) (not (parent _ ?x)))` gives the expected set.
  - `aggregates`: given `payment` tuples `[1 10] [2 10] [3 5]`, `(defrule total [(sum ?a)] (payment _ ?a))` gives `#{[25]}` (review I1). `count-distinct ?a` gives 2. `collect-by` orders correctly. `collect-map` raises its conflict error.
  - `empty-group`: a `count` over an empty body gives no tuples.
  - `bind-nil`: `(bind ?v (:missing ?m))` gives no tuples, and `bind-nil` gives `[nil]`.
  - `computed-and-expr-inputs`: `(elem (:xs ?m) ?x)` works.
  - `defrel-memo`: a `defrel` that increments a host-side counter through a test-only built-in is called once per distinct input across iterations.
  - `fuel-on-joins` (review C1): three relations of 300 tuples each, cross-joined into a 1-tuple result, with `:fuel 1000000` throw `:fuel-exhausted`.
  - `nontermination-guard`: a counter rule `(defrule n [?y] (n ?x) (bind ?y (inc ?x)))` seeded with `[0]` throws `:tuple-limit` or `:iteration-limit`, naming the relation `n`.
  - `nan-terminates` (review C4): a recursive rule deriving `nan` reaches a fixpoint.
  - `duplicate-facts-collapse` (Review Focus 5): the same fact supplied in the edb and by a `defrule` gives 1 tuple, and `count` sees 1.
  - `unstorable`: binding a `fn` into a head gives `:unstorable-value`.
  - Property `semi-naive=naive`: use test.check with 100 trials over random positive programs (2–4 relations, random binary rules, random edges among 6 constants). `evaluate` must equal `evaluate-naive`.
  - Property `fact-order-independent`: shuffling the edb insertion order gives the same result, including a `sum` over doubles.
- [ ] **Step 2: Run the tests.** They should FAIL.
- [ ] **Step 3: Implement** `strata.engine`.
- [ ] **Step 4: Run the tests again.** They should PASS.
- [ ] **Step 5: Commit** with `feat(engine): metered semi-naive evaluation with aggregates`.

### Task 21: Program pipeline, taint and `:on-code-error :skip` (`strata.program`)

**Spec:** §6.1, §8.3

**Files:**
- Create: `src/lang/program.clj`
- Modify: `src/lang/engine.clj` (taint), `test/lang/engine_test.clj` (switch to `strata.program`)
- Test: `test/lang/program_test.clj`

**Interfaces:**

Produces:
- **`(load-program {:sources {ns src} :builtins #{ns} :externs {ns {rel arity}} :limits m})`** returns a compiled program map:

  ```clojure
  {:strata … :plans … :computed … :facts {q #{t}} :fn-table … :struct-table …
   :externs … :warnings […] :limits …}
  ```

  It runs these stages, in this order: read (Task 6) → order (Task 7) → collect defs → analyze → check → plan → stratify → compile. The whole function runs inside `run-isolated`. The returned map is immutable: after loading finishes, the fn and struct atoms are dereferenced into plain maps.
- **`(run-program prog {:facts :resources :limits :trace :on-code-error})`** returns `{:relations {q #{t}} :diagnostics … :stats …}`. It creates the ctx and validates and canonicalizes the host facts. It then runs `evaluate` inside `run-isolated`. Finally it discards the ctx, which releases the page cache.
- **Taint:** when `:on-code-error :skip` is set, a run error whose kind is a **program-bug kind** is caught inside a computed call. The program-bug kinds are `:type-error`, `:arity-error`, `:bad-relation-result`, `:arithmetic-error` and `:collect-map-conflict`; limit kinds are never caught. The call yields `[]`, a diag entry is recorded, and the rule's head relation is marked tainted, with the taint propagating along the graph edges. After each stratum, if a tainted relation is the target of a negative edge, the run throws `:tainted-negation`.

- [ ] **Step 1: Write failing tests.**
  - `load-and-run`: a 2-namespace program with a require, a `defn`, a `defrel`, a struct and rules gives the expected relations.
  - `program-reusable-threads`: run the same loaded program from 4 futures with different facts; each result matches its own facts.
  - `skip-mode`: a `defrel` that throws a type error on one input, under `:skip`, gives results for the other inputs, `(get-in diags [:counts :type-error])` of 1, and the relation in `:tainted`.
  - `tainted-negation`: a skipped call feeding a relation that is used under `not` gives `:tainted-negation`.
  - `limits-never-skipped`: fuel exhaustion under `:skip` still throws.
- [ ] **Step 2: Run the tests.** They should FAIL.
- [ ] **Step 3: Implement** `strata.program`, and switch the engine-test helper over to it.
- [ ] **Step 4: Run the full suite.** `clojure -X:test` should PASS.
- [ ] **Step 5: Commit** with `feat(program): load pipeline, isolated runs, taint tracking`.

---

## Milestone 5: Host API, formats, and the sandbox

### Task 22: Public API (`strata.api`) and `strata.test`

**Spec:** §7.1, §7.2, §8.2, §4.2 (`check-modes`)

**Files:**
- Create: `src/lang/api.clj`, `src/lang/test.clj`
- Test: `test/lang/api_test.clj`

**Interfaces:**

Produces `strata.api`:
- `load`, a thin wrapper over `load-program`.
- `run` returns a db: `{:relations … :diagnostics … :stats …}`.
- `(query db pattern)`. The pattern must name a **stored** relation, either qualified or alias-free. Anything else is a `:not-a-stored-relation` error. The result is a set of maps from `?sym` to value; constants filter.
- `(relation db qsym)` returns a set of tuples.
- `stats` and `diagnostics`.
- `(parse prog qsym resource)` and `(parse-explain prog qsym resource)` run inside a fresh ctx and `run-isolated`.
- `bytes-resource` and `file-resource`, re-exported.

Host facts are validated in `run`. An unknown relation, a wrong arity, a non-collection tuple, or a value that `canon` rejects throws `:bad-fact`, phase `:run`, with `:data {:rel q}`.

**`:trace`:** the function receives event maps of the form `{:event :rule-fired|:code-call|:parse :rel q …}`.

**`strata.test/check-modes`:** `(check-modes prog qsym samples)`. `samples` is a coll of full tuples. For each tuple and each mode, the mode is run on its inputs and the sample's outputs must appear in the result. The return value is a seq of `{:mode i :tuple t}` failures.

- [ ] **Step 1: Write failing tests.**
  - `query-binding-maps`: `(query db '(a/edge "x" ?y))` gives `#{{?y "y"}}`.
  - `query-computed-rejected`: querying a `defrel` gives `:not-a-stored-relation`.
  - `bad-host-facts` (Review Focus 4): three cases each give `:bad-fact`, and none of them is a raw exception:
    - a wrong arity;
    - an undeclared extern relation;
    - `[(Object.)]` as a tuple value.
  - `byte-array-facts`: a `byte[]` inside a fact becomes Bytes.
  - `host-parse`: `(parse prog 'f/png-like (bytes-resource …))` gives `{:value …}`, and `parse-explain` reports the failing path.
  - `check-modes`: a `hex` with mismatched hex-digit case across its modes reports a failure. A consistent `hex` reports none.
  - `trace-events`: the trace function receives at least one `:rule-fired` event.
- [ ] **Step 2: Run the tests.** They should FAIL.
- [ ] **Step 3: Implement** `strata.api` and `strata.test`.
- [ ] **Step 4: Run the tests again.** They should PASS.
- [ ] **Step 5: Commit** with `feat(api): host API, queries, host parse, check-modes`.

### Task 23: PE format end to end

**Spec:** §9.1

**Files:**
- Create: `test/lang/fixtures/pe.clj`, `test/lang/formats/pe_test.clj`, `test/resources/formats/pe.edn`

**Interfaces:**

Consumes: `strata.api`.

The format program `test/resources/formats/pe.edn` is exactly the §9.1 program. Add `"test/resources"` to the `:test` alias's `:extra-paths`.

**Fixture builder:** `(build-pe {:wide? bool :imports ["KERNEL32.dll" …] :delay-imports […] :delay-rva-based? bool})` returns a `byte[]`. The file it builds contains:
- a DOS header with `e_lfanew` set to `0x80`;
- `"PE\0\0"`;
- a COFF header with 1 section;
- an optional header, PE32 or PE32+, with 16 data directories;
- one `.idata` section, at RVA `0x1000` and file offset `0x200`, containing the import descriptors, a zero terminator, the delay descriptors and the ASCII name strings.

Use little-endian `ByteBuffer` writes.

- [ ] **Step 1: Write failing tests.**
  - `pe32-imports`: given files `a.dll` (importing `B.dll` and `kernel32.dll`) and `b.dll` (importing `c.dll`), query `imported-dll` for `a.dll` and get both imports tagged `:import`.
  - `pe32plus`: the same imports with `:wide? true`.
  - `delay-imports`: these come back tagged `:delay` in both modes, RVA-based and VA-based.
  - `closure-and-missing`: `depends-on` for `a.dll` contains `c.dll` through the case-insensitive `B.dll` → `b.dll` link. `missing-dll` contains `kernel32.dll` and `c.dll`, and does **not** contain `B.dll`.
  - `corrupt-name-rva`: a descriptor whose name RVA points outside every section is skipped, and the others are still returned.
  - `not-a-pe`: a resource of random bytes yields no `headers` tuple and no error.
  - Optional local test `real-dll`: when `LANG_TEST_DLL` is set, parse that file and assert that `imported-dll` is non-empty.
- [ ] **Step 2: Run the tests.** They should FAIL.
- [ ] **Step 3: Build the fixtures and fix any interpreter gaps.** Do not change the §9.1 program unless it disagrees with the spec. If it does, stop and report.
- [ ] **Step 4: Run the tests again.** They should PASS.
- [ ] **Step 5: Commit** with `test(formats): PE import parsing end to end`.

### Task 24: TES4 (Skyrim) format end to end

**Spec:** §9.2

**Files:**
- Create: `test/lang/fixtures/tes4.clj`, `test/lang/formats/tes4_test.clj`, `test/resources/formats/tes4.edn` (exactly the §9.2 program)

**Fixture builder:** `(build-plugin {:flags int :masters ["Skyrim.esm" …] :author "x" :groups [{:label "WEAP" :records [{:type "WEAP" :form-id n :fields [["EDID" bytes] …] :compressed? bool}]}] :xxxx? bool})` returns a `byte[]`. The builder:
- writes a TES4 record with HEDR (version 1.71, the record count and the next object id), CNAM, and one MAST followed by DATA (u64 0) per master;
- writes the GRUPs and their records;
- compresses a record with `Deflater` when it is flagged as compressed (flag 0x40000, a u32 raw size, then the zlib data);
- when `:xxxx?` is set, emits an XXXX subrecord ahead of a field of 70,000 bytes.

- [ ] **Step 1: Write failing tests.**
  - `header`: `hedr` returns version ≈1.71 (compare as f32 widened, within 1e-6) and the record count.
  - `masters-order`: `masters` returns the masters vector in file order.
  - `light-flag-and-ext`: flag 0x200 makes the plugin `light`, and so does the `.esl` extension alone.
  - `missing-master`: this finds a master that is absent from `in/file` (the check is case-insensitive).
  - `record-count`: two groups holding three WEAP records and one compressed ARMO record give the correct counts by type.
  - `lazy`: the trace from the `record-count` run contains no parse event for `record-fields`. Record fields stay deferred, and the compressed record is never inflated.
  - `xxxx`: a forced record with an XXXX field gives a `data` of length 70,000 with type `"MODL"`.
  - `corrupt-compressed`: a compressed record with garbage zlib data leaves the rest of the run unaffected, and forcing that record yields nil.
- [ ] **Step 2: Run the tests.** They should FAIL.
- [ ] **Step 3: Build the fixtures and fix any gaps.**
- [ ] **Step 4: Run the tests again.** They should PASS.
- [ ] **Step 5: Commit** with `test(formats): TES4 plugin parsing end to end`.

### Task 25: RDAR (Cyberpunk) format end to end

**Spec:** §9.3

**Files:**
- Create: `test/lang/fixtures/rdar.clj`, `test/lang/formats/rdar_test.clj`, `test/resources/formats/rdar.edn` (exactly the §9.3 program)

**Fixture builder:** `(build-rdar {:entries [{:hash u64 :segments [[off zsize size]…] :deps [u64…]}…]})` returns a `byte[]`. The archive has:
- a 40-byte header, version 12;
- padding up to `0xAC`;
- an index at the end: `file-table-offset 8`, the three counts, then the entries (56 bytes each), the segments (16 each) and the dependencies (8 each).

Use at least one hash ≥ 2⁶³.

- [ ] **Step 1: Write failing tests.**
  - `header-index`: `archive-file` returns every entry, and the hash ≥ 2⁶³ comes back as the expected BigInt.
  - `segments-by-range`: `file-segment-of` links each entry to exactly its segments, in `[seg-start, seg-end)`.
  - `wrong-version`: version 13 gives no `archive` tuple.
  - `between-not-cross-product`: with 2000 entries of 1 segment each, `:fuel 50000000` is enough.
- [ ] **Step 2: Run the tests.** They should FAIL.
- [ ] **Step 3: Build the fixtures and fix any gaps.**
- [ ] **Step 4: Run the tests again.** They should PASS.
- [ ] **Step 5: Commit** with `test(formats): RDAR archive index end to end`.

### Task 26: Sandbox and robustness suite

**Spec:** §7.4, §8, §10.2 (Sandbox tests)

**Files:**
- Create: `test/lang/sandbox_test.clj`

Each test loads a small program through `strata.api` and asserts the resulting error kind. Each one must finish in under 5 seconds.

- [ ] **Step 1: Write the tests.**
  - `no-interop`: `(System/exit 0)`, `(.getRuntime Runtime)`, `(new java.io.File "x")`, `(clojure.core/eval 1)` and `(java.lang.Thread/sleep 1)` each give a load error, `:unresolved-symbol`.
  - `no-tags`: a source containing `#=(+ 1 2)` or `#java.io.File "x"` gives a `:read` phase error.
  - `infinite-loop`: a `defrel` with `(loop [] (recur))` gives `:fuel-exhausted` or `:call-fuel-exhausted`.
  - `bigint-blowup`: `(bit-shift-left 1 100000)` gives `:int-too-large`, and so does repeated squaring in a loop.
  - `inflate-bomb`: 100 MB of zeros, deflated, with `b/inflate` max 1 GB and `:max-inflate` 1 MB, gives nil and no OOM.
  - `deep-source`: 10,000 nested vectors give `:form-too-deep`.
  - `deep-recursion`: a non-tail recursive `defn` gives `:depth-exceeded`.
  - `deep-struct`: a recursive struct over crafted input nested 10,000 deep gives `:depth-exceeded`.
  - `cross-product`: a three-way join gives `:fuel-exhausted`.
  - `error-no-host-paths`: a `file-resource` over a temp file in a directory named `secret-dir`, combined with a type-error program, gives a thrown error whose `pr-str` of its ex-data and message doesn't contain `"secret-dir"`.
  - `timeout`: with `:timeout-ms 50`, a long-running program gives `:timeout`.
- [ ] **Step 2: Run the tests.** `clojure -X:test :nses '[strata.sandbox-test]'` should PASS. A failure exposes a real gap: fix it in the owning source file and note the fix in the commit message.
- [ ] **Step 3: Run the full suite.** `clojure -X:test` should PASS with 0 failures and 0 errors.
- [ ] **Step 4: Commit** with `test(sandbox): resource, interop, and robustness suite`.
