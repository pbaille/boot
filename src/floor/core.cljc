(ns floor.core
  (:refer-clojure :exclude [take drop cons or and + vals iter vec map set str key fn nth])
  (:require [clojure.core :as c]
            [boot.generics :as g :refer [generic generic+ reduction]]
            [boot.named :as n]
            [boot.prelude :as p :refer [is isnt throws clj-only]]
            [floor.utils :as u]
            [floor.compiler :as cpl]
            [floor.composite :as compo]
            [floor.lambda :as lambda]
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

    ;; control flow constructs

    (clj-only

      (declare bindings_unified bindings_optimize)

      (generic bindings
               ([x options])
               ([x y options] [x y]))

      (defn IF_form
        ([test then]
         (if (symbol? test)
           `(if (success? ~test) ~then ~test)
           `(let [t# ~test]
              (if (success? t#) ~then t#))))
        ([test then else]
         (if else
           `(if (success? ~test) ~then ~else)
           (IF_form test then)))
        ([test then test2 then2 & others]
         (IF_form test then (apply IF_form test2 then2 others))))

      (defn IF-expand [env args]
        (apply IF_form (c/map (partial cpl/expand env) args)))

      (defn CS_compile-case [env bs expr options]
        (let [bs (bindings bs options)
              bs (if (:unified options) (bindings_unified bs) bs)
              {:keys [env bindings]} (bindings_optimize env bs)
              expr (cpl/expand env expr)]
          (if-not (c/seq bindings)
            expr
            (loop [ret expr
                   [[p1 e1] & pes :as bs]
                   (reverse (partition 2 bindings))]
              (if-not (c/seq bs)
                ret
                (recur `(let [~p1 ~e1] (if (success? ~p1) ~ret ~p1))
                       pes ))))))

      #_(CS_compile-case {} '[a b c a] '(+ a c) {})

      (defn CS_expand
        [env [b1 e1 & more :as args] options]
        (let [exp (partial cpl/expand env)]
          (condp c/= (count args)
            0 nil
            1 (CS_wrap-return (exp b1) options)
            2 (cond
                (c/not (vector? b1)) (IF-expand env [b1 e1])
                :else (CS_compile-case env b1 e1 options))
            ;else
            `(let [a# ~(CS_expand env [b1 e1] options)]
               (if (success? a#)
                 a# ~(CS_expand env more options))))))

      (defmacro cs [& body]
        (CS_expand {} body {}))

      (defmacro csu [& body]
        (CS_expand {} body {:unified true}))

      (defmacro !cs [& body]
        (CS_expand {} body {:binding-mode :strict}))

      (defmacro !csu [& body]
        (CS_expand {} body {:binding-mode :strict :unified true}))

      (defmacro ?cs [& body]
        (CS_expand {} body {:binding-mode :opt}))

      (defmacro ?csu [& body]
        (CS_expand {} body {:binding-mode :opt :unified true}))

      (defmacro or
        ([] (failure ::empty-or))
        ([x] x)
        ([x & next]
         `(cs [or# ~x] or# (or ~@next))))

      (defmacro and
        ([] true)
        ([x] x)
        ([x & next] `(cs ~x (and ~@next))))

      (defmacro f [& xs]
        (lambda/compile `cs (lambda/parse xs)))

      (defmacro ?f [& xs]
        (lambda/compile `?cs (lambda/parse xs)))

      (defmacro !f [& xs]
        (lambda/compile `!cs (lambda/parse xs)))

      (defmacro fu [& xs]
        (lambda/compile `csu (lambda/parse xs)))

      (defmacro ?fu [& xs]
        (lambda/compile `?csu (lambda/parse xs)))

      (defmacro !fu [& xs]
        (lambda/compile `!csu (lambda/parse xs)))

      (defn f1_parse [xs]
        (if (c/even? (c/count xs))
          {:cases xs}
          {:name (c/first xs)
           :cases (c/rest xs)}))

      (defn f1_expand
        ([{:keys [name cases binding-form]}]
         (let [argsym (gensym "arg_")
               patterns (c/take-nth 2 cases)
               exprs (c/take-nth 2 (c/next cases))]
           `(c/fn ~@(when name [name])
              [~argsym]
              (~binding-form
                ~@(interleave (c/map (c/fn [p] [p argsym]) patterns)
                              exprs))))))

      (defmacro f1 [& xs]
        (let [parsed (f1_parse xs)]
          (f1_expand (assoc parsed :binding-form `cs))))

      #_(p/mx* '(f [a] a [a b] :pouet [1 2] :lop [a b . xs] :varrrr))

      #_(floor.core/cs [a G__26554 b G__26555] :pouet [1 G__26554 2 G__26555] :lop)

      (defn case-expand [{:keys [binding-form seed cases]}]
        (let [patterns (c/take-nth 2 cases)
              exprs (c/take-nth 2 (c/next cases))
              seed-sym (gensym "seed_")]
          `(let [~seed-sym ~seed]
             (~binding-form
               ~@(interleave (c/map (c/fn [p] [p seed-sym]) patterns)
                             exprs)))))

      (defmacro case [seed & cases]
        (case-expand {:cases cases :seed seed :binding-form `cs}))

      (defmacro casu [seed & cases]
        (case-expand {:cases cases :seed seed :binding-form `csu}))

      (comment
        (case 1
          (num? x) x
          y :any))

      (comment :backup

               (defn CS_wrap-return [x options]
                 (if (c/= (:binding-mode options) :strict)
                   `(let [x# ~x]
                      (if (success? x#)
                        x# (p/error "strict binding failure:\n" '~x)))
                   x))

               (defn CS_expand
                 [env [b1 e1 & more :as args] options]
                 (let [exp (partial cpl/expand env)]
                   (condp c/= (count args)
                     0 nil
                     1 (CS_wrap-return (exp b1) options)
                     2 (cond
                         (c/not (vector? b1)) (IF-expand env [b1 e1])
                         (c/not (seq b1))
                         (CS_wrap-return (exp e1) options)
                         :else
                         (let [[pat expr & others] b1
                               {:keys [bindings env]} (bindings_optimize env (bindings pat (exp expr) options))
                               [p1 e1' & bs]
                               (if (:unified options)
                                 (bindings_unified bindings)
                                 bindings)]
                           `(let ~[p1 e1']
                              ~(let [env (cpl/env-shadow env p1)]
                                 (IF-expand
                                   env
                                   [p1
                                    (CS_expand
                                      env
                                      [(c/vec bs)
                                       (if others
                                         (CS_expand env [(c/vec others) e1] options)
                                         e1)]
                                      options)])))))
                     ;else
                     `(let [a# ~(CS_expand env [b1 e1] options)]
                        (if (success? a#)
                          a# ~(CS_expand env more options))))))

               (defn FN-wrap-cases [cs cases]
                 (c/map (c/fn [[argv & body]]
                          (let [body (if (= 1 (count body)) (first body) (list* 'do body))
                                argv' (c/vec (c/take (count argv) (p/gensyms)))]
                            `(~argv' (~cs ~(c/vec (interleave argv argv')) ~body))))
                        cases))

               (defn FN-wrap-cases [cs cases]
                 (let [by-arity (c/group-by (comp c/count car) cases)
                       bodify (c/fn [[argv & body]]
                                (list argv (if (= 1 (count body)) (first body) (list* 'do body))))]
                   (c/map (c/fn [[arity [[argv & body] & others]]]
                            (let [argv' (c/vec (c/take arity (p/gensyms)))]
                              `(~argv' (~cs ~(c/vec (interleave argv argv')) ~body))))
                          by-arity)))

               (defmacro f [& xs]
                 (let [{:keys [cases name]} (p/parse-fn xs)]
                   `(c/fn ~name ~@(FN-wrap-cases `cs cases))))

               (defmacro ?f [& xs]
                 (let [{:keys [cases name]} (p/parse-fn xs)]
                   `(c/fn ~name ~@(FN-wrap-cases `?cs cases))))

               (defmacro !f [& xs]
                 (let [{:keys [cases name]} (p/parse-fn xs)]
                   `(c/fn ~name ~@(FN-wrap-cases `!cs cases))))

               (defmacro fu [& xs]
                 (let [{:keys [cases name]} (p/parse-fn xs)]
                   `(c/fn ~name ~@(FN-wrap-cases `csu cases))))

               (defmacro ?fu [& xs]
                 (let [{:keys [cases name]} (p/parse-fn xs)]
                   `(c/fn ~name ~@(FN-wrap-cases `?csu cases))))

               (defmacro !fu [& xs]
                 (let [{:keys [cases name]} (p/parse-fn xs)]
                   `(c/fn ~name ~@(FN-wrap-cases `!csu cases))))

               (defn case-expand [{:keys [lambda seed cases]}]
                 `((~lambda ~'loop
                     ~@(interleave (c/map c/vector (c/take-nth 2 cases))
                                   (c/take-nth 2 (c/next cases))))
                   ~seed))

               (defmacro case [seed & cases]
                 (case-expand {:cases cases :seed seed :lambda `f}))

               (defmacro casu [seed & cases]
                 (case-expand {:cases cases :seed seed :lambda `fu})))


      (comment

        (p/mx*' (f iop [x] x [(pos? x) [a b c]] (+ x a b c)))

        ((f iop [x] x [(pos? x) [a b c]] (+ x a b c))
         1)

        (p/mx*' (f [1] :one
                   [0] :zero
                   [(num? x)] {:num x}
                   [x] {:any x}))

        (let [f1 (f [1] :one [0] :zero [(num? x)] {:num x} [x] {:any x})]
          [(f1 0) (f1 1) (f1 12) (f1 "iop")])
        )
      )

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

(clj-only :bindings

          (do :vec

              (defn bindings_raw-vec [v seed options]
                (let [cnt (count v)
                      symseed? (symbol? seed)]
                  (p/with-gensyms
                    [vect head tail ¡linecheck ¡size>= ¡size=]
                    (let [vect (if symseed? seed vect)]
                      (+
                        (when-not symseed? [vect seed])
                        (bindings
                          [¡linecheck `(sequential? ~vect)
                           head `(take ~vect ~cnt)
                           ¡size>= `(= (count ~head) ~cnt)
                           tail `(drop ~vec ~cnt)
                           ¡size= `(pure? ~tail)]
                          options)
                        (mapcat
                          (c/fn [e i] (bindings e `(nth ~head ~i) options))
                          (seq v) (range))

                        )))))

              (defn bindings_composite-vec [v seed options]
                (let [doti (p/indexof v '.)
                      cars (take v doti)
                      [eli & queue] (drop v (inc doti))
                      qcnt (count queue)
                      symseed? (symbol? seed)]
                  (p/with-gensyms
                    [ysym qsym cdr']
                    (let [ysym (if symseed? seed ysym)]
                      (+
                        (when-not symseed? [ysym seed])
                        (bindings_raw-vec cars `(take ~ysym ~doti) options)
                        (bindings eli `(drop ~ysym ~doti) options)
                        #_(bind.vec.body cars ysym doti)
                        (when-not (zero? qcnt)
                          (+
                            [cdr' eli]
                            (bindings eli `(dropend ~cdr' ~qcnt) options)
                            [qsym `(takend ~cdr' ~qcnt)]
                            (bindings_raw-vec queue qsym options)))))))))

          (do :map

              (defn bindings_map-keys [x seed options]
                (mapcat
                  (c/fn [[k v]]
                    (bindings v `(get ~seed ~k) options))
                  x))


              (defn bindings_raw-map [x seed options]
                (p/with-gensyms
                  [¡mapcheck ¡seed]
                  (+
                    [¡seed seed
                     ¡mapcheck `(map? ~¡seed)]
                    (bindings_map-keys x ¡seed options))))

              (defn bindings_composite-map [x seed options]
                (let [rs (get x '.)
                      m (dissoc x '.)
                      ks (keys m)]
                  (p/with-gensyms
                    [¡seed]
                    (+
                      [¡seed seed]
                      (bindings_map-keys m ¡seed options)
                      (bindings rs `(dissoc ~¡seed ~@ks) options))))))

          (do :sym

              (defn bindings_symbol-mode [s default]
                (let [default (c/or default :short)]
                  (condp c/= (car s)
                    \¡ default
                    \? :opt
                    \! :strict
                    \_ :short
                    default)))

              (defn bindings_parse-symbol [x options]
                (let [name (name x)
                      prefix (#{\? \! \¡ \_} (first name))]
                  {:prefix prefix
                   :name (if prefix (n/sym (c/or (c/next name) (c/gensym))) x)
                   :mode (bindings_symbol-mode x (:binding-mode options))}))

              (defn bindings_symbol-form [seed mode]
                (condp c/= mode
                  :short seed
                  :opt `(or ~seed nil)
                  :strict `(or ~seed (p/error "strict binding failure:\n" (fail ~seed)))))

              (comment
                (bindings '!a 'x {}))

              )

          (def bindings_operators
            (atom
              {:&
               (c/fn [xs seed options]
                 (p/with-gensyms
                   [seedsym]
                   (apply p/catv
                          [seedsym seed]
                          (c/map #(bindings % seedsym options) xs))))

               :ks
               (c/fn [xs seed options]
                 (bindings (zipmap (c/map (comp keyword :name bindings_parse-symbol) xs) xs)
                           seed options))

               :ks-req
               (c/fn [xs seed options]
                 (bindings (zipmap (c/map keyword xs) xs) seed options))

               :ks-opt
               (c/fn [xs seed options]
                 (let [keys (c/map keyword xs)
                       opt-syms (c/map (partial p/sym "?") xs)]
                   (bindings (zipmap keys opt-syms) seed options)))

               :ks-or
               (c/fn [xs seed options]
                 (let [keys (take-nth 2 xs)
                       or-exprs (c/map (c/fn [[k v]] `(c/or ~k ~v)) (partition 2 xs))]
                   (p/catv
                     ((get @bindings_operators :ks-opt) keys seed options)
                     (interleave keys or-exprs))))

               :cons
               (c/fn [[a b] seed options]
                 (p/with-gensyms
                   [seedsym]
                   (p/catv
                     [seedsym seed]
                     (bindings a `(car ~seedsym) options)
                     (bindings b `(cdr ~seedsym) options))))

               :quote
               (c/fn [[a] seed options]
                 (bindings (gensym "¡") `(= ~seed '~a) options))

               :bind_
               (c/fn [[p expr] seed options]
                 (p/catv
                   ['_ seed]
                   (bindings p expr options)))

               :!
               (c/fn [[f & [p]] seed options]
                 (bindings (c/or p (gensym)) (list f seed) options))

               ::default
               (c/fn [[verb pat & args] seed options]
                 (bindings pat (list* verb seed args) options))}))

          (defn bindings_compile-binding-vector [xs & [options]]
            (c/vec (mapcat (c/fn [[pat seed]]
                             (bindings pat seed (c/or options {})))
                           (partition 2 xs))))

          (defn bindings_unified
            "takes a binding vector (like let) , compile it with 'bindings
             then add unification constraints on symbols that occurs multiple times"
            [xs]
            (loop [ret [] seen #{}
                   [a b & nxt] (bindings_compile-binding-vector xs)]
              (if a
                (if (seen a)
                  (recur (conj ret (gensym) `(= ~a ~b)) seen nxt)
                  (recur (conj ret a b) (conj seen a) nxt))
                ret)))

          (defn bindings_optimize [env bs]
            (reduce
              (c/fn [{:keys [bindings env]} [sym expr]]
                (if (c/symbol? expr)
                  {:bindings bindings :env (assoc-in env [(p/ns-sym) sym] {:substitute expr})}
                  {:bindings (p/catv bindings [sym (cpl/expand env expr)]) :env env}))
              {:env env :bindings []}
              (c/partition 2 bs)))

          #_(bindings_optimize {} '[a b c a])

          (g/generic+ bindings

                      ([xs options]
                       :vec
                       (c/vec (mapcat (c/fn [[pat seed]]
                                        (bindings pat seed options))
                                      (partition 2 xs))))

                      ([x seed options]

                       :sym
                       (let [{:keys [name mode]}
                             (bindings_parse-symbol x options)]
                         [name (bindings_symbol-form seed mode)])

                       :vec
                       (if (compo/single-dotted? x)
                         (bindings_composite-vec x seed options)
                         (bindings_raw-vec x seed options))

                       :map
                       (if (compo/single-dotted? x)
                         (bindings_composite-map x seed options)
                         (bindings_raw-map x seed options))

                       :lst
                       (let [[v & args] x]
                         (p/cs [k (c/and (c/symbol? v) (keyword v))
                                op (get @bindings_operators k)]
                               (op args seed options)
                               ((::default @bindings_operators) (c/cons v args) seed options)))
                       :any
                       (bindings (gensym) `(eq ~x ~seed) options))))








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

