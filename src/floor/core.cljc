(ns floor.core
  (:refer-clojure :exclude [take drop cons or and * + vals iter vec map set str key fn nth])
  (:require [clojure.core :as c]
            [boot.generics :as g :refer [generic generic+ reduction]]
            [boot.named :as n]
            [boot.prelude :as p :refer [is isnt throws clj-only]]
            [floor.utils :as u]
            [floor.compiler]
            [boot.types :as t]))

(do :control

    ;; failure
    (g/generic fail [x])
    (g/deft failure [data] (fail [this] (:data this)))

    (def failure0 (failure ::failure))
    (defn failure? [x] (g/implements? fail x))
    (defn success? [x] (not (failure? x)))

    ;; predicates and guards importation

    ;; predicate is a function that can return true or false
    ;; guard is a function that can return something or nil

    ;; we will bring builtin clojure predicates and guards into our failure based control flow system

    (defn predicate->guard [f]
      (u/fn& [a] (when (f a ...) a)))

    (defn wrap-guard [f fail]
      (u/fn& [a] (c/or (f a ...) (fail a ...))))

    (defn wrap-predicate [f fail]
      (wrap-guard (predicate->guard f) fail))

    (def core-guards

      (reduce
        (c/fn [a s]
          (let [val (eval s)
                fail #(failure {:predicate s :args (c/vec %&)})
                g (wrap-predicate val fail)]
            (assoc a val g s g)))
        {}
        '[decimal? contains? every? qualified-keyword? satisfies? seq? fn? vector? any? isa? boolean?
          char? some? inst? simple-symbol? pos? sequential? neg? float? set? reversible? map? var? empty?
          string? uri? double? map-entry? int? associative? keyword? even? tagged-literal? indexed? counted?
          future? zero? simple-keyword? not-every? class? neg-int? sorted? nil? bytes? record? identical?
          ident? qualified-ident? true? integer? special-symbol? ratio? delay? ifn? nat-int? chunked-seq?
          distinct? pos-int? odd? uuid? false? list? simple-ident? rational? number? not-any? qualified-symbol?
          seqable? symbol? coll? not
          = > >= < <=]))

    (def core-preds

      (reduce
        (c/fn [a s]
          (let [val (eval s)
                fail #(failure {:predicate s :args (c/vec %&)})
                g (wrap-guard val fail)]
            (assoc a val g s g)))
        {}
        '[next seq]))

    (p/defmac import-core-stuff
      []
      `(do ~@(mapcat (c/fn [[s v]]
                       `[(ns-unmap '~(p/ns-sym) '~s) (def ~s ~v)])
                     (filter (comp symbol? c/key)
                             (merge core-guards core-preds)))))

    (import-core-stuff)

    (def eq =) (def neq not=)
    (def gt >) (def gte >=)
    (def lt <) (def lte <=)

    ;; we will create a bunch of things based on the type registry
    ;; for each type
    ;; a generic casting function
    ;; a type checker
    ;; a casting predicate

    ;; along with a type generic that return the type of the given thing

    (p/defmac init-type-generics
      []
      (let [{:keys [prims all]} (t/split-prims)]
        `(do
           (generic ~'type [~'_] ~@(c/interleave (c/keys prims) (c/keys prims)))
           ~@(c/map (c/fn [k] `(declare ~(p/sym k "?"))) (c/keys all))
           ~@(c/map (c/fn [[k xs :as e]]
                      (let [cast-sym (p/sym '-> k)]
                        `(do
                           (generic ~(p/sym k "?") [~'x]
                                    ~@(if (prims k) [k 'x] (c/interleave xs (c/repeat 'x)))
                                    :any (failure {:typecheck ~k :isnt ~'x}))
                           (generic ~cast-sym [~'x])
                           (defn ~(p/sym cast-sym "?") [x#]
                             (c/or (c/when (g/implements? ~cast-sym x#) x#)
                                   (failure {:not-castable {:to ~k :from x#}})))))) all))))

    (init-type-generics)

    )

(do :monoids

    (generic
      pure
      [_]
      :fun identity
      :vec []
      :lst ()
      :map {}
      :set #{}
      :str ""
      :sym (symbol "")
      :key (keyword "")
      #{:nil :any} nil)

    (do :assertions
        (is [] (pure [1 2 3]))
        (is #{} (pure #{:pouet 12}))
        (is {} (pure {:a 1}))
        (is "" (pure "hello")))

    (generic
      pure?
      [x]
      :lst (when-not (c/seq x) ())
      (when (c/= x (pure x)) x))

    (reduction
      sip [a b]
      :lst (c/concat a [b])
      #{:set :vec} (c/conj a b)
      :map (c/assoc a (c/first b) (c/second b))
      :fun (c/partial a b)
      :nil (c/list b))

    (do
      (is (sip [] 1 2) [1 2])
      (is (sip [1] 2 3) [1 2 3])
      (is (sip #{1} 2 3) #{1 2 3})
      (is (sip {:a 1} [:b 2] [:c 3]) {:a 1 :b 2 :c 3})
      (is ((sip c/+ 1) 1) 2))

    ;; declaration (see implementation in titerable section
    (generic iter [x])

    (reduction
      +
      [a b]
      :fun (comp b a)
      :lst (concat a (iter b))
      :str (c/str a b #_(.toString b))
      :sym (symbol (c/str (name a) b #_(.toString b)))
      :key (keyword (c/str (name a) (name b)))
      :num (c/+ a b)
      :nil (iter b)
      :any (reduce sip a (iter b)))

    (def wrap (u/fn& [x] (sip (pure x) ...)))
    (def wrap+ (u/fn& [x] (+ (pure x) ...)))
    (def wrap* (partial apply wrap))
    (def wrap+* (partial apply wrap+))

    (defmacro defwrapped
      ([[n e]]
       (let [n+ (p/sym n "+")
             n* (p/sym n "*")
             n+* (p/sym n "+*")]
         `(do
            (def ~n (u/fn& [] (sip ~e ...)))
            (def ~n+ (u/fn& [] (+ ~e ...)))
            (def ~n* (u/fn& [x#] (apply ~n x# ...)))
            (def ~n+* (u/fn& [x#] (apply ~n+ x# ...))))))
      ([x & xs]
       `(do ~@(c/map #(list `defwrapped %) (c/cons x xs)))))

    (defwrapped
      [lst ()]
      [vec []]
      [set #{}]
      [map {}])

    (def str
      c/str)

    (def str*
      (u/fn& [x] (apply c/str x ...)))
    (def key
      (u/fn& [] (+ (c/keyword "") ...)))
    (def key*
      (u/fn& [x] (apply key x ...)))
    (def sym
      (u/fn& [x] (+ (c/symbol (c/name x)) ...)))
    (def sym*
      (u/fn& [x] (apply sym x ...)))
    )

(do :iterables

    (generic+
      iter
      [a]
      :nil ()
      #{:sym :key} (iter (c/name a))
      :any (c/or (c/seq a) ()))

    (generic
      vals
      [x]
      :map (c/or (c/vals x) ())
      :coll (iter x)
      :any (p/error "vals: no impl for " x))

    (generic
      idxs
      [x]
      :map (c/or (c/keys x) ())
      :set (iter x)
      :coll (range (count x))
      :any (p/error "idxs: no impl for " x))

    (p/defmac defiterg
      "an update to define generic functions for iterables
       hiding the iter/wrap boilerplate"

      [name [a1 :as argv] expr]
      `(g/generic
         ~name
         ~argv
         :lst
         ~expr
         (let [a# ~a1
               ~a1 (iter ~a1)]
           (wrap* a# ~expr))))

    (generic car [x] (c/first (iter x)))
    (generic last [x] (c/last (iter x)))
    (defiterg take [x n] (c/take n x))
    (defiterg drop [x n] (c/drop n x))
    (defiterg takend [x n] (c/take-last n x))
    (defiterg dropend [x n] (c/drop-last n x))
    (defiterg butlast [x] (c/butlast x))
    (defiterg cdr [x] (c/rest x))
    (defiterg rev [x] (c/reverse x))

    ;selection from index to index
    (defiterg section [x from to]
              (-> x
                  (take to)
                  (drop from)))

    (defn splat
      "split at" [x n]
      [(take x n) (drop x n)])

    (defn uncs "uncons"
      [x]
      [(car x) (cdr x)])

    (defn runcs
      "reverse uncons"
      [x]
      [(butlast x) (last x)])

    (defn cons
      "like core.list*
       but preserve collection type"
      [& xs]
      (let [[cars cdr] (runcs xs)]
        (+ (pure cdr) cars cdr)))

    (defn cons? [x]
      (when (c/and (g/implements? iter x)
                   (c/not (pure? x)))
        x))

    (generic nth
             ([x i]
              (nth (iter x) i (failure {:idx-not-found i :in x})))
             ([x i not-found]
              (c/nth x i not-found)))

    ;; vector optimized impls

    (g/type+
      :vec
      (last [x] (get x (dec (count x))))
      (nth [x i not-found] (c/get x i not-found))
      (take [x n] (subvec x 0 (min (count x) n)))
      (drop [x n] (subvec x (min (count x) n)))
      (takend [x n] (let [c (count x)] (subvec x (- c n) c)))
      (dropend [x n] (subvec x 0 (- (count x) n)))
      (butlast [x] (subvec x 0 (dec (count x))))
      (section [x from to] (subvec x (max 0 from) (min (count x) to)))
      (cdr [x] (subvec x 1))))

(do :callables

    (generic invocation
             [x]
             :fun x
             (c/constantly x))

    (generic application
             [x]
             :fun (c/partial apply x)
             (c/partial apply (invocation x)))

    (defmacro callables_wrapper
      [builder]
      (let [[_ [a1 [e1]] & cs]
            (macroexpand-1 `(u/fn& [x#] ((~builder x#) ~'...)))]
        `(c/fn (~a1 (c/partial ~e1)) ~@cs)))

    (def § (callables_wrapper invocation))

    (def * (callables_wrapper application)))








(comment

  (g/generic form [x] x)



  ;; monoids
  (g/generic pure [x])
  (g/generic pure? [x])
  (g/reduction sip [x y])
  (g/reduction + [x y])

  ;; iterables
  (g/generic iter [x])
  (g/generic vals [x])
  (g/generic idxs [x])

  ;;
  (g/generic getter [x] (u/error "no getter impl for " x))
  (g/generic updater [x] (u/error "no updater impl for " x))
  (g/generic swaper [x] (u/error "no swaper impl for " x))
  (g/generic checker [x] (u/error "no checker impl for " x))

  (g/generic rget [x y] ((getter x) y))
  (g/generic rupd [x y f] ((updater x) y f))
  (g/generic rswap [x y] ((swaper x) y))
  (g/generic rcheck [x y] ((checker x) y))

  (comment
    (defn+ check
           ([x y] (rcheck y x))
           ([x y & ys] (and (rcheck y x) (check* x ys))))

    (defn+ get
           ([x y] (rget y x))
           ([x y & ys] (reduce get (rget y x) ys)))

    ;; here reduce is problematic
    ;; because accumulator can turn into ::fail, we have to cut the loop
    ;; also, failure? could be a generic function that returns true if the implementing type represents an error
    ;; potentially holding explanations and usable in spec/explain like things
    ;; the custom shortcircuiting thing has not so much impact on perfs (see control namespace)
    ;; and with a dynamic var we can swipe control-flow macro expansions
    ;; currently it is a row value tested against its arg with = but it can be a predicate instead, more powerful

    (defn+ swap
           ([x y] (rswap y x))
           ([x y & ys] (reduce swap (rswap y x) ys)))

    (defn+ upd
           ([x y f] (rupd y x (swaper f)))
           ([x y f & others] (reduce upd* (rupd y x f) (partition 2 others))))))

