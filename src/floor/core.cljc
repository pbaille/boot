(ns floor.core
  (:refer-clojure
    :exclude
    [get not let chunk case take drop cons or and * + < > vals iter vec map set str key fn nth])
  (:require [clojure.core :as c]
            [boot.generics :as g]
            [boot.named :as n]
            [boot.prelude :as p :refer [is isnt throws clj-only]]
            [floor.compiler.core :as compiler]
            [boot.types :as t]))

(compiler/import-core-macros)

(do :control

    (defrecord Failure [data])
    (def failure ->Failure)
    (defn failure? [x] (instance? Failure x))
    (defn success? [x] (c/not (instance? Failure x))))

(do :importation

    ;; predicates and guards importation

    ;; predicate is a function that can return true or false
    ;; guard is a function that can return something or nil

    ;; we will bring builtin clojure predicates and guards into our failure based control flow system

    (defn predicate->guard [f]
      (p/fn& [a] (when (f a ...) a)))

    (defn wrap-guard [f fail]
      (p/fn& [a] (c/or (f a ...) (fail a ...))))

    (defn wrap-predicate [f fail]
      (wrap-guard (predicate->guard f) fail))

    (def core-predicates

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
          seqable? symbol? coll?
          = #_> >= #_< <=
          ]))

    (defn not [x]
      (if (c/contains? #{false nil} x)
        x (failure ::not-failure)))

    (def core-guards

      (reduce
        (c/fn [a s]
          (let [val (eval s)
                fail #(failure {:predicate s :args (c/vec %&)})
                g (wrap-guard val fail)]
               (assoc a val g s g)))
        {}
        '[next seq]))

    #_(p/pp core-predicates)

    (p/defmac import-core-stuff
      []
      `(do ~@(mapcat (c/fn [[s v]]
                       `[(ns-unmap '~(p/ns-sym) '~s) (def ~s ~v)])
                     (filter (comp symbol? c/key)
                             (merge core-predicates core-guards)))))

    (import-core-stuff)

    (def eq =) (def neq not=)
    ;; TODO bring back < and >
    #_(def gt >) (def gte >=)
    #_(def lt <) (def lte <=)
    (def add c/+) (def sub c/-) (def mul c/*) (def div c//)

    ;; we will create a bunch of things based on the type registry
    ;; for each type
    ;; a generic casting function
    ;; a type checker
    ;; a casting predicate

    ;; along with a type generic that return the type of the given thing

    (p/defmac init-type-generics
      []
      (c/let [{:keys [prims all]} (t/split-prims)]
        `(do
           (defg ~'type [~'_] ~@(c/interleave (c/keys prims) (c/keys prims)))
           ~@(c/map (c/fn [k] `(declare ~(p/sym k "?"))) (c/keys all))
           ~@(c/map (c/fn [[k xs :as e]]
                      (let [cast-sym (p/sym '-> k)]
                           `(do
                              (defg ~(p/sym k "?") [~'x]
                                         ~@(if (prims k) [k 'x] (c/interleave xs (c/repeat 'x)))
                                         :any (failure {:typecheck ~k :isnt ~'x}))
                              (defg ~cast-sym [~'x] ~k ~'x)
                              (defn ~(p/sym cast-sym "?") [x#]
                                (c/or (g/implements? x# ~cast-sym)
                                      (failure {:not-castable {:to ~k :from x#}}))))))
                    all))))

    (init-type-generics)

    (defn argumentation

      "in asparagus, many functions takes what we can call the object as first argument
       I mean, the thing we are working on, for instance, in the expression (assoc mymap :a 1 :b 2), mymap is what we call the object
       the argumentation function will help to turn this kind of function into a one that takes only the arguments (in the previous exemple: :a 1 :b 2)
       and return a function that takes only the target object, and return the result.
       (let [assoc_ (argumentation assoc)
             assoc-a-and-b (assoc_ :a 1 :b 2)]
          (assoc-a-and-b {})) ;=> {:a 1 :b 2}

       many of the asparagus functions of this form, have their subjectified version with the same name suffixed with _
       this is handy, for instance, to create chains of 1 argument functions
       (> myseq (take_ 3) (dropend_ 2)) will thread 'myseq thru 2 functions, the semantics is analog to core/-> but it is a function
       the '> function is defined in the :invocation-application-mapping section (the previous one)
       (>_ (take_ 3) (dropend_ 2)) ;; will return a function that wait for its first argument ('myseq in the previous example)

       the idea behind this is to ease function composition, the preference for guards over predicates is also a step in this direction
       the further 'flow section will introduce some useful functional constructs that go even further (in conjunction with this and guards)"
      [f]
      (p/fn& [] (c/fn [x] (f x ...))))

    (is {:a 1 :b 2 :c 3}
        (((argumentation c/assoc) :a 1 :b 2) {:c 3}))

    )

(do :monoids

    (defg
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

    (defg
      pure?
      [x]
      :lst (if-not (c/seq x) () (failure {:not-pure x}))
      :nil nil
      (cs (eq x (pure x)) x (failure {:not-pure x})))

    (g/reduction
      sip [a b]
      :lst (c/concat a [b])
      #{:set :vec} (c/conj a b)
      :map (c/assoc a (c/first b) (c/second b))
      :fun (c/partial a b)
      :nil (c/list b))

    ;; declaration (see implementation in titerable section
    (defg iter [x])

    (g/reduction
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

    (def wrap (p/fn& [x] (sip (pure x) ...)))
    (def wrap+ (p/fn& [x] (+ (pure x) ...)))
    (def wrap* (partial apply wrap))
    (def wrap+* (partial apply wrap+))

    (defmacro defwrapped
      ([[n e]]
       (let [n+ (p/sym n "+")
             n* (p/sym n "*")
             n+* (p/sym n "+*")]
            `(do
               (def ~n (p/fn& [] (sip ~e ...)))
               (def ~n+ (p/fn& [] (+ ~e ...)))
               (def ~n* (p/fn& [x#] (apply ~n x# ...)))
               (def ~n+* (p/fn& [x#] (apply ~n+ x# ...))))))
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
      (p/fn& [x] (apply c/str x ...)))
    (def key
      (p/fn& [] (+ (c/keyword "") ...)))
    (def key*
      (p/fn& [x] (apply key x ...)))
    (def sym
      (p/fn& [x] (+ (c/symbol (c/name x)) ...)))
    (def sym*
      (p/fn& [x] (apply sym x ...)))
    )

(do :iterables

    (g/generic+
      iter
      [a]
      :nil ()
      #{:sym :key} (iter (c/name a))
      :any (c/or (c/seq a) ()))

    (defg
      vals
      [x]
      :coll (iter x)
      :map (c/or (c/vals x) ())
      :any (p/error "vals: no impl for " x))

    (defg
      idxs
      [x]
      :coll (range (count x))
      :map (c/or (c/keys x) ())
      :set (iter x)
      :any (p/error "idxs: no impl for " x))

    (defg nth
               ([x i]
                (nth (iter x) i (failure {:idx-not-found i :in x})))
               ([x i not-found]
                (c/nth x i not-found)))

    (p/defmac defiterg
      "an update to define generic functions for iterables
       hiding the iter/wrap boilerplate"

      [name [a1 :as argv] expr]
      `(defg
         ~name
         ~argv
         :lst
         ~expr
         (let [a# ~a1
               ~a1 (iter ~a1)]
              (wrap* a# ~expr))))

    (defg car [x] (c/first (iter x)))
    (defg last [x] (c/last (iter x)))
    (defiterg take [x n] (c/take n x))
    (defiterg drop [x n] (c/drop n x))
    (defiterg takend [x n] (c/take-last n x))
    (defiterg dropend [x n] (c/drop-last n x))
    (defiterg butlast [x] (c/butlast x))
    (defiterg cdr [x] (c/rest x))
    (defiterg rev [x] (c/reverse x))

    #_(macroexpand '(floor.core/let [a__16857__auto__ x x (floor.core/iter x)] (floor.core/wrap* a__16857__auto__ (c/rest x))))

    ;selection from index to index
    (defiterg section [x from to]
              (-> x
                  (take to)
                  (drop from)))

    (deff splat
      "split at" [x n]
      [(take x n) (drop x n)])

    (deff uncs "uncons"
      [x]
      [(car x) (cdr x)])

    (deff runcs
      "reverse uncons"
      [x]
      [(butlast x) (last x)])

    (deff cons
      "like core.list*
       but preserve collection type"
      [. xs]
      (let [[cars cdr] (runcs xs)]
           (+ (pure cdr) cars cdr)))

    (deff cons? [x]
      (if (c/and (g/implements? x iter)
                 (failure? (pure? x)))
        x
        (failure {:not-cons x})))

    ;; vector optimized impls

    (g/type+
      :vec
      (last [x] (c/get x (dec (count x))))
      (nth [x i not-found] (c/get x i not-found))
      (take [x n] (subvec x 0 (min (count x) n)))
      (drop [x n] (subvec x (min (count x) n)))
      (takend [x n] (let [c (count x)] (subvec x (- c n) c)))
      (dropend [x n] (subvec x 0 (- (count x) n)))
      (butlast [x] (subvec x 0 (dec (count x))))
      (section [x from to] (subvec x (max 0 from) (min (count x) to)))
      (cdr [x] (subvec x 1))))

(do :callables

    (defg application
               [x]
               :fun (c/partial apply x)
               (c/partial apply (->fun x)))

    (defmacro def-callable
      [name builder]
      (let [[_ [a1 [e1]] . cs]
            (macroexpand-1 `(p/fn& [x#] ((~builder x#) ~'...)))]
           `(c/defn ~name (~a1 (c/partial ~e1)) ~@cs)))

    (def-callable § ->fun)

    (def-callable * application)

    #_((->fun (c/fn [x] x)) 1)
    )

(do :walking

    (g/reduction $
                 [x f]
                 :map (c/into {} (c/map (c/fn [[k v]] [k (§ f v)]) x))
                 :set (c/set (c/map (§ f) x))
                 :vec (c/mapv (§ f) x)
                 :lst (c/map (§ f) x))

    ;; $ indexed
    (g/reduction $i
                 [x f]
                 :map (c/into {} (c/map (c/fn [[k v]] [k (§ f k v)]) x))
                 :set (c/set (c/vals ($i (c/zipmap x x) f)))
                 :vec (c/vec (c/map-indexed (§ f) x))
                 :lst (c/map-indexed (§ f) x))

    (deff walk
          [x in out]
          (cs (coll? x)
              (out ($ x in))
              (out x)))

    (deff dfwalk
          "depth first walk"
          [x f]
          (walk x #(dfwalk % f) f))

    (deff bfwalk
          "breadth first walk"
          [x f]
          (walk (f x) #(bfwalk % f) c/identity))

    (deff walk?
          [x node? f]
          (cs [nxt (node? x)]
              ($ nxt #(walk? % node? f))
              (f x)))

    (deff zip
          "core/map(ish)"
          [f . xs]
          (* c/map f ($ xs iter)))

    (deff red
          "reduce with seed (init) as first argument
          and variadic seq(s) argument (like map does)"
          [x f xs]
          (c/reduce (§ f) x xs)
          [x f y . ys]
          (red x (* f)
               (* zip vec y ys))
          #_(if (c/every? cons? xs)
              (* red
                 (* f x ($ xs car))
                 f ($ xs cdr))
              x))

    (g/reduction $+
                 ; $+ is to $ what c/mapcat is to c/map
                 [x f]
                 :any
                 (* + #_(pure x) ($ x f)))

    (g/reduction $i+
                 ; $i+ is to $i what c/mapcat is to c/map
                 [x f]
                 :any
                 (* + ($i x f)))

    (deff zip+
          "core/mapcat(ish)"
          [f . xs]
          (cs [ret (c/seq (* zip f xs))]
              (* + ret) ()))

    (deff scan
          "similar to core/partition"
          [x size step]
          (let [[pre post] (splat x size)]
               (cs (cons? post)
                   (cons pre (scan (drop x step) size step))
                   (cons? pre)
                   (sip (pure x) pre)
                   (pure x))))

    (deff chunk
          "split an iterable 'x by chunk of size 'size"
          [x size]
          (scan x size size))

    (deff nths
          "like core/take-nths"
          [x n]
          ($ (scan x n n) car))

    (def braid
      (c/partial zip+ (c/partial sip ())))

    )

(do :getters-and-friends
    ;; declarations
    ;; ------------------------------------------------------------------------------

    (defg form [x] x)

    (defg getter [x] (p/error "no getter impl for " x))
    (defg updater [x] (p/error "no updater impl for " x))
    (defg checker [x] (p/error "no checker impl for " x))

    (defg rget [x y] ((getter x) y))
    (defg rupd [x y f] ((updater x) y f))
    (defg rcheck [x y] ((checker x) y))

    ;; core
    ;; ------------------------------------------------------------------------------

    (p/defn+ check
             ([x y] (rcheck y x))
             ([x y & ys] (and (rcheck y x) (check* x ys))))

    (p/defn+ get
             ([x y] (rget y x))
             ([x y & ys] (reduce get (rget y x) ys)))

    (p/defn+ upd
             ([x y f] (rupd y x (->fun f)))
             ([x y f & others] (reduce upd* (rupd y x f) (partition 2 others))))

    ;; extras
    ;; ------------------------------------------------------------------------------

    (p/defn+ put
             ([x l v]
              (upd x l (constantly v)))
             ([x l v & lvs]
              (reduce put*
                      (upd x l v)
                      (partition 2 lvs))))

    (p/defn+ upd<
             "takes a datastructure to transform (x)
              and series of couples of form [lens(able) fn]
              executing the first transformation which associated lens does not focuses on nil"
             ([x couples]
              (when (seq couples)
                (or
                  (and
                    (get x (ffirst couples))
                    (upd* x (first couples)))
                  (upd< x (next couples)))))
             ([x l f & lfs]
              (upd< x (cons [l f] (partition 2 lfs)))))

    ;; impls
    ;; ------------------------------------------------------------------------------

    (g/generic+ checker

                [x]

                :nil
                (constantly true)

                #{:num :key}
                (f [y] (and (contains? y x) true))

                :vec
                (let [get (getter x)]
                     (f [y] (and (get y) true)))
                #_(let [cs (seq (map checker x))]
                       (fn [y]
                           (loop [cs cs]
                             (if-not cs true (and ((first cs) y)
                                                  (recur (next cs)))))))

                :link
                (let [get (getter (c/key x))
                      check (checker (c/val x))]
                     (f [y]
                        (let [v (get y)]
                             (check v))))

                :map
                #_(checker (into [] x))
                (let [checkers ($ (iter x) checker)]
                     (f [y]
                        (loop [checkers checkers]
                          (cs (pure? checkers)
                              true
                              (and ((car checkers) y)
                                   (recur (cdr checkers)))))))

                :fun
                (f [y] (and (x y) true))

                :any
                (f [y] (and (eq x y) true)))

    (do :impl

        (defn vec->fun [v]
          (let [ts ($ v ->fun)]
               (f [y] (c/reduce #(%2 %1) y ts))))

        (defn link->fun [e]
          (f [x]
             (upd x
                  (c/key e)
                  (c/val e))))

        (defn map->fun [m]
          (vec->fun (mapv link->fun m))))

    (g/generic+ ->fun
                [x]
                :nil c/identity
                ;:fun x
                :map (map->fun x)
                :vec (vec->fun x)
                :link (link->fun x)
                :any (c/constantly x))

    (g/generic+ getter
                [x]

                :nil
                identity

                :fun x
                #_(let [f (or (c/core-guards x) x)]
                       (fn [y] (f y)))

                #{:num :key}
                (f [y] (c/get y x (failure [::get x y])))

                :vec
                (let [getters ($ x getter)]
                     (f [y]

                        (loop [y y getters getters]
                          (cs (pure? getters) y
                              [y ((car getters) y)]
                              (recur y (cdr getters))))))

                :map
                (let [m ($ x getter)]
                     (f [y]
                        #_(loop [{} ret m (seq m)]
                            (if-not m
                              ret
                              (c/let? [[k v] (first m)
                                       y' (v y)]
                                      (recur (assoc ret k y') (next m)))))
                        (reduce (f [a e]
                                   (cs [v ((c/val e) y)]
                                       (assoc a (c/key e) v)
                                       (reduced (failure [::get x y]))))
                                {} m)))

                :any
                (getter (c/partial eq x)))

    #_(defn lens+
        "lens composition, don't use directly
         prefer passing a vector to the 'lens function"
        [l m]
        (fn [x f]
            (c/let? [v1 (get x l)
                     v2 (mut v1 m f)]
                    (put x l v2))))

    (do :lenses

        (defn lens
          ([x]
           (lens (getter x)
                 (updater x)
                 (list 'lens x)))
          ([get upd & [form']]
           (g/thing
             (getter [x] (f [y] (get y)))
             (updater [x] (f [y f] (upd y f)))
             (form [_] form'))))

        (defn lens+
          "lens composition, don't use directly
           prefer passing a vector to the 'lens function"
          [l m]
          (lens (f [x]
                   (cs [lx (get x l)
                        lm (get lx m)] lm))
                (f [x f]
                   ;; the idea here is to shortcircuit when encountering an intermediate nil result
                   (cs [v1 (get x l)
                        v2 (upd v1 m f)]
                       (put x l v2)))))

        (declare lenses)

        (def lenses

          {:k
           (lens identity (f [x _] x))

           :id
           (lens identity (f [x f] (f x)))

           :prob
           (lens (c/partial p/prob 'get)
                 (f [x f] (p/prob 'set (f x))))

           :never
           (lens (constantly (failure :never-lens-get))
                 (constantly (failure :never-lens-set)))

           :<
           (f
             "fork lens, tries every given lens(able) in order
              use the first that does not focuses on nil"
             [. xs]
             (let [lenses ($ xs lens)]
                  (lens
                    (f [x]
                       (loop [ls lenses]
                         (cs (pure? ls) (failure :fork-lens-failure)
                             [ret (get x (car ls))]
                             ret (recur (cdr ls)))))
                    (f [x f]
                       (loop [ls lenses]
                         (cs (pure? ls) (failure :fork-lens-failure)
                             (get x (car ls)) (upd x (first ls) f)
                             (recur (cdr ls))))))))

           :path
           (f path
              "a lens representing deep access/update in a map (with keyword keys)
               unlike regular lens composition it does not return nil if the path points to nil
               this way it can be used to introduce new values in a map (unlike lens composition, that would have failed (returning nil))"
              [. xs]
              (let [ks (flatten xs)]
                   (c/assert (every? keyword? ks) "path should only contains keywords")
                   (lens (f [x] (c/get-in x ks (failure [:path-lens-get x ks])))
                         (f [x f] (c/update-in x ks f)))))

           :?
           (f
             "build a lens that when focuses on nil, returns the state unchanged, or behave normally"
             [l] ((:< lenses) (lens l) (:k lenses)))

           :!
           (f
             "a lens that that returns nil when focuses on nil"
             [l] ((:< lenses) (lens l) (:never lenses)))

           :convertion
           (f
             "Given a function from A to B and another in the
              opposite direction, construct a lens that focuses and updates
              a converted value."
             [one->other other->one]
             (lens one->other
                   (f [s f]
                      (other->one (f (one->other s))))))

           :eq
           (f [x]
              (lens (f [y] (eq y x))
                    (f [y f] (cs (eq x y) (f y)))))

           :pass
           (f pass
              "take a datastructure and a series of lenses
               try to forward x thru all given lenses
               can be used to do validation and coercion (with the help of 'lfn)"
              [x . xs]
              (cs (cons? xs)
                  (cs [x' (upd x (car xs) identity)]
                      (* pass x' (cdr xs)))
                  x))}))

    (g/generic+ updater
                [x]

                :nil
                (f [x f] (f x))

                #{:num :key}
                (let [get (getter x)]
                     (f [y f]
                        (cs (get y)
                            (c/update y x f))))
                :vec
                (updater
                  (reduce lens+ (c/map lens x)))

                :fun
                (let [get (getter x)]
                     (f [y f] (cs [y' (get y)] (f y'))))


                :map
                (let [get (getter x)]
                     (f [y f] (cs [z (get y)] (f z))))

                :any
                (updater (partial eq x)))

    (defg combine [x y])

    (defn step [x y]
      (if (c/satisfies? Icombine_2 x)
        (combine x y)
        ((->fun y) x)))

    (deff >
          "thread x thru given transformations (xs) shortcircuiting on first nil result"
          [x] x
          [x y] (and x (step x y))
          [x y . ys]
          (red x
               (f [x y]
                  (let [?x (step x y)]
                       (or x (reduced x))))
               (cons y ys)))

    (deff <
           "try all given transformations over x until the first non nil result"
           [x] (failure ::<)
           [x y] (step x y)
           [x y . ys]
           (red x
                (f [x y]
                   (cs [x (step x y)]
                       (reduced x) x))
                (cons y ys)))

    )


(def df
  (f1 "data function,
       create a function from a data structure that
       apply all functions contained in it (deeply) to further args.
       preserve original structure"
      data
      (f [. xs]
         (walk? data
                (f1 node (or (vec? node) (map? node)))
                (f1 leaf (* leaf xs))))))



