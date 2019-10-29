(ns boot.prelude
  (:refer-clojure
   :exclude [assert not-empty empty or and cat])
  (:require
   [clojure.core :as c]
   [clojure.string :as str]
   [clojure.set :as set]))

(def debug (atom nil))

(do :aliases

    "some really commonly used functions, with shorter names"

    (def p partial)
    (def apl apply)
    (def p* (p p apl))
    (def id identity)
    (def sym? symbol?)
    (def kw? keyword?)
    (def car first)
    (def cdr rest)
    (def lst list)
    (def vec? vector?)
    (def k constantly)
    (def hm* (p* hash-map))
    (def cat concat)
    (def cat* (p* cat))
    (def catv (comp vec concat))
    (def catv* (p* catv))
    (def mrg merge)
    (def str* (p* str)))

(do :symbols

    (defn dot? [x]
      (= '. x))

    (defn double-dot? [x]
      (= '.. x))

    (defn fullname [x]
      (if (string? x) x
          (if-let [ns (namespace x)]
            (str ns "/" (name x))
            (name x))))

    (defn qualified-sym [x]
      (->> (resolve x)
          str
          (drop 2)
          (apply str)
          symbol))

    (defn qualify-sym [x]
      (symbol (str *ns*) (name x)))

    (defn sym [& xs]
      (->> xs
           (remove nil?)
           (map fullname)
           (apply str)
           symbol))

    #_(assert
     (= (symbol "") (sym))
     (= 'foobar
        (sym 'foo 'bar)
        (sym :foo "ba" 'r)
        (sym 'foo :b "ar" (sym))))

    (defn sym-split [x]
      (-> (str x)
          (clojure.string/split #"\.")
          (->> (filter seq)
               (mapv sym))))

    #_(assert
     (= '[a b /] (sym-split (symbol "a.b./")))
     (= [] (sym-split (symbol "")))
     (= '[a z] (sym-split 'a.z)))

    (def sym0 (symbol ""))
    (def sym0? (p = sym0))

    (do :ns-resolution

        (defn class-symbol [^java.lang.Class cls]
          (symbol (.getName cls)))

        (defn class-namespace [^java.lang.Class r]
          (str/join "." (butlast (sym-split (symbol (.getName r))))))

        (defn namespace-name [^clojure.lang.Namespace ns]
          (name (.getName ns)))

        (defn var-namespace [^clojure.lang.Var v]
          (name (.name (.ns v))))

        (defn var-name [^clojure.lang.Var v]
          (name (.sym v)))

        (defn var-symbol [^clojure.lang.Var v]
          (symbol (var-namespace v) (var-name v)))

        (defn ns-resolve-sym [sym]
          (try
            (let [x (ns-resolve *ns* sym)]
              (cond
                (instance? java.lang.Class x) (class-symbol x)
                (instance? clojure.lang.Var x) (var-symbol x)
                :else nil))
            (catch ClassNotFoundException _
              sym)))))

(do :base-macros

    (defrecord Aze [])

    (defn parse-fn [[fst & nxt :as all]]

      (let [[name fst & nxt]
            (if (symbol? fst)
              (cons fst nxt)
              (concat [nil fst] nxt))

            [doc fst & nxt]
            (if (string? fst)
              (cons fst nxt)
              (concat [nil fst] nxt))

            [opts fst & nxt]
            (if (map? fst)
              (cons fst nxt)
              (concat [{} fst] nxt))

            impls
            (if (vector? fst)
              {fst (vec nxt)}
              (into {}
                    (map
                     (c/fn [[args & body]]
                       [args (vec body)])
                     (cons fst nxt))))]

        (assoc opts
               :name name
               :doc doc
               :impls impls
               :cases (mapv (p* list*) impls))))

    (defmacro defmac
      "personal defmacro
       define a regular macro
       but also a function that do the same thing as the macro
       (when receiving quoted args)
       here I hope that it could ease macro composition and later ckish embeddings"
      [& body]
      (let [{:keys [name doc opts cases]} (parse-fn body)
            fname (sym name '-fn)
            fname* (sym fname '*)]
        `(do (defn ~fname ~@cases)
             (def ~fname* (p* ~fname))
             (defmacro ~name ~(c/or doc "")
               ~(assoc opts :fn fname)
               ([& xs#] (apply ~fname xs#))))))

    (defmac marked-fn

      "marked function,
       define an anonymous form (like fn)
       a def form (like defn)
       and a predicate function (like fn?)"

      [name & [doc]]

      `(do

         (defmac ~name
           [& body#]
           (let [parsed# (parse-fn body#)]
             `(with-meta
                (fn ~(c/or (:name parsed#) (gensym)) ~@(:cases parsed#))
                {~~(keyword name) true})))

         (defn ~(sym name "?") [x#]
           (when (-> x# meta ~(keyword name)) x#))

         (defmac ~(sym 'def name) [name'# & body#]
           `(def ~name'# (~'~name ~@body#)))))

    (defmac import-macros [x y & nxt]
      `(do (def ~x (var ~y))
           (.setMacro (var ~x))
           ~(when nxt `(import-macros ~@nxt))))

    (defmac import-fns [x y & nxt]
      `(do (defn ~x [& xs#] (apply ~y xs#))
           ~(when nxt `(import-fns ~@nxt))))

    (defmac _ [& _] nil)

    (defmac cp [x & xs]
      `(condp #(%1 %2) ~x ~@xs))

    (_ :cp+

       (defmac cp' [x & xs]
         (let [[cases default]
               (if (odd? (count xs))
                 ((juxt butlast last) xs)
                 [xs nil])
               cases
               (mapcat
                (fn [[p e]]
                  (cond (vec? p) [`(fn [x#] (every? #(% x#) ~p)) e]
                        (set? p) (recur [(vec p) e])
                        (holymap? p) (recur [(vec (vals p)) e])
                        :else [p e]))
                (partition 2 cases))]
           `(condp #(%1 %2) ~x ~@cases ~default))
         )

       (mx' (cp' "s"
                 [number? pos?] :yeah
                 string? "iop"
                 :nop))
       )

    (defmac error [& xs]
      `(throw (Exception. (str ~@xs))))

    (defmacro let-dbg [bs & bod]
      `(let ~(vec (mapcat (fn [[p e]] [p `(prob '~p ~e)]) (partition 2 bs)))
         (println "\n\n")
         ~@bod))


    (do :assert

        (defn assertions
          [ctx x]
          (cp x
              map-entry? (assertions (conj ctx (key x)) (val x))
              vec? (assertions ctx (zipmap (range) x))
              map? (mapcat (partial assertions ctx) x)
              [[x ctx]]))

        (defmac assert1 [x m]
          (let [s (gensym)
                v (gensym)
                m `(str ~(c/or m "assert fails:") "\n" '~x)]
            `(if-let [~s ~x] ~s
                     (throw (new AssertionError ~m)))))

        (defmac assert
          ([x]
           `(do ~@(map assert1-fn* (assertions [] x))))
          ([x & xs]
           ;; assert-fn is autodefined by defmac
           (assert-fn (vec (cons x xs)))))

        (defmac throws [x]

          (assert {"this should throws"
                   (= ::catched (try ~x (catch Exception e ::catched)))}))

        (do :tuto

            ;; normal 
            (assert 1)

            ;; the initial motivation point for this assert implementation is to return the tested value in case of success

            ;; In order to be able to write:

            (defn my-add [x y]
              ;; neither x or y can be nil, else its an error 
              (+ (assert x)
                 (assert y)))

            (assert (= 3 (my-add 1 2)))

            ;; this one throws

            '(my-add 1 nil)


            ;; with-message (this one throws)
            (throws (assert {"should not be nil" nil}))

            ;; maps can hold several assertions like this
            (let [x 1]
              (assert {"should not be nil" x
                       "should be a number" (number? x)}))

            ;; vectors can represent assertions too

            (assert (= 3 (assert [1 2 3])))

            ;; vectors act like an 'and expression
            ;; returning the last asserted value

            ;; this one throws indicating the index of the failure e.g [2]
            (throws (assert [1 2 nil (u/prob :yeah)]))

            ;; this become handy when we have nested assertions

            (throws (assert
                     {:section1
                      {:test1 [1 2 nil]}
                      :section2
                      [:iop :iop]}))

            ;; in the previous case the error message indicate the path to the failed assertion: [:section1 :test1 2]

            ))

    (defmac is [x & xs]
      (let [xval (gensym)]
        `(let [~xval ~x]
           ~@(mapv (fn [y]
                     `(assert {(str "not equal! \na: " '~x " -> " ~xval "\nb: " '~y " -> " ~y)
                               (= ~xval ~y)}))
                   xs)
           ~xval)))

    (do :or

        (defn flat-collection-literal [x]
          (cp x
              vec? (vec (mapcat flat-collection-literal x))
              map? (flat-collection-literal (vec (vals x)))
              set? (flat-collection-literal (vec x))
              [x]))

        (defmac or
          "a more expressive taste of 'or
           when a literal collection is given to 'or it checks it deeply
           instead of consider it for a truthy value
           (which doesn't make much sense, why would you hardcode a truthy value? for the last argument maybe...
           we always can wrap it in a 'do :) or an 'id call :p
           if all cases fails returns nil (not 'false)"
          [& xs]
          `(c/or
            ~@(map #(cp % seq? %
                        coll? (list* `c/and (flat-collection-literal %))
                        %) xs)
            nil))

        (do
          ;; it can be used normaly
          (is 1 (or 1 2 3))
          (is true (or (not nil) 2 3))

          ;; vectors works like 'and(s)
          '(or [do-you-think? really? absolutly-sure?]
               :too-bad)

          ;; is equivalent to
          '(or (and  do-you-think? really? absolutly-sure?)
               :too-bad)

          ;; with maps we can document our tests
          '(or {:condition1 (tries something)
                :condition2 [do-you-think? really?]})

          ;; as you have seen, we can compose vector and map literals together

          (is 2 (or {:a 1 :b [1 nil]} 2 3))
          (is :yo (or [1 nil] :yo (do (println 45) 1)))
          (nil? (or (pos? -1) false))
          (is :yo
              (or [1 nil]
                  [1 2 [3 5 {:a nil :b 2}]]
                  :yo)))
        )

    (do :and

        (defmac and
          ([x]
           (list* `c/and (flat-collection-literal x)))
          ([x & xs]
           ;; assert-fn is autodefined by defmac
           (and-fn (vec (cons x xs)))))

        (is 2 (and 1 2))

        (is nil (and [1 2 nil] 3))

        ;; as you can see only literal vectors are deeply tested

        (is :yes (let [v [1 2 nil]]
                   (and v :yes))))

    (do :cs

        (defn generated-binding-sym? [x]
          (re-matches #"^((vec)|(seq)|(first)|(map))__[0-9]+$"
                      (name x)))

        (assert
         (nil? (generated-binding-sym? 'aze))
         (nil? (generated-binding-sym? (gensym "yop")))
         (generated-binding-sym? 'vec__1234)
         (generated-binding-sym? 'seq__1234)
         (generated-binding-sym? 'map__1234)
         (generated-binding-sym? 'first__1234))

        (defn cs-case
          [[b1 b2 & bs] e]
          `(~(if (or (generated-binding-sym? b1)
                     (= \_ (first (name b1))))
               `c/let `c/when-let)
            [~b1 ~b2]
            ~(if bs (cs-case bs e)
                 ;; this wrapping is nescessary for the case e eval to nil
                 [e])))

        (defn cs-form [[x e & xs]]
          (let [bs (if (vector? x) x [(gensym) x])
                form (cs-case (destructure bs) e)]
            (cond
              (not (seq xs)) form
              (not (next xs)) `(c/or ~form [~(first xs)]) ;; same thing here
              :else `(c/or ~form ~(cs-form xs)))))

        (defmacro cs [& xs]
          `(first ~(cs-form xs)))

        (_ :flat-cs-emitted-or-form

            (defn or-expr? [x]
              (and (seq? x) (= `c/or (first x))))

            (defn remove-useless-ors [x]
              (cp x
                  or-expr?
                  (cons `c/or
                        (mapcat (fn [y]
                                  (mapv remove-useless-ors
                                        (if (or-expr? y) (rest y) [y])))
                                (rest x)))
                  holycoll?
                  ($ x remove-useless-ors)
                  x))

            (defmacro cs [& xs]
              `(first ~(remove-useless-ors (cs-form xs))))

            (_ (let [a 0] ;; feel free to change the value and reevaluate
                 (macroexpand '(cs
                                (pos? a) :pos
                                (neg? a) :neg
                                :zero)))))

        (_ :cs-tuto

            ;; like a normal let
            (cs [a 1 b 2] (+ a b))

            ;; but shorts on nil bindings
            (cs [a (pos? -1) ;; this line binds 'a to nil,
                 ;; this will shortcircuit the rest of the binding form
                 ;; and jump to the second expression of the body
                 _ (println "never printed")]

                ;; evaluated only in case of successful bindings
                (println "never evaluated")

                ;; evaluated when binding form has been shortcircuited
                (do (println "failure branch taken")
                    :pouet))

            ;; you can bind symbols starting with an underscore to nil without failing
            (cs [a 1 b 2
                 _neg-a (neg? a) ;; this bind _neg-a to nil without shortcirsuiting
                 a (if _neg-a (- a) a)]
                (+ a b)) ;;=> 3

            ;; you can chain several couples of binding-form expression
            (defn cs_1 [a]
              ;; the ? symbol has no special meaning here
              (cs [? (number? a)] {:number a}
                  [? (string? a)] {:string a}
                  [? (coll? a)]
                  (cs [? (empty? a)] :empty
                      [? (seq? a)] {:seq a}
                      {:coll a})))

            (cs_1 1)
            (cs_1 "a")
            (cs_1 ())
            (cs_1 '(1 2))
            (cs_1 [1 2])

            ;; cs_1 works as intended but clearly can be done more concisely with a good old cond
            ;; but wait, cs macro can also be used like cond!

            ;; if you need only to check something but do not need the return value
            ;; like we seen in cs_1,  e.g [? (test? ...)]
            ;; it seems kind of tiring to do so, so we've introduce a shorthand for this case

            (let [a -42]

              (=
               ;; normal syntax
               (cs [? (pos? a)] a :negative)
               ;; shorthand syntax (condishpatible)
               (cs (pos? a) a :negative)))

            ;; as we see it can be use like 'if
            (cs (pos? -1) :pos :not-pos)

            ;; or when (with only one expression body)
            (cs (pos? 1) :pos)

            ;; or cond (without the need for the :else thing)
            (let [a 0] ;; feel free to change the value and reevaluate
              (cs
               (pos? a) :pos
               (neg? a) :neg
               :zero))

            ;; this kind of unification of if and cond came from arc-lisp,
            ;; i cannot find a solid argument against it

            ;; we can redefine cs_1 in a more clean way
            (defn cs_2 [a]
              (cs (number? a) {:number a}
                  (string? a) {:string a}
                  (coll? a)
                  (cs (empty? a) :empty
                      (seq? a) {:seq a}
                      {:coll a})))

            ;; the thing is that now you can mix condish syntax and condletish syntax

            (defn cs_3 [a]
              (cs (number? a) [:num a]
                  (symbol? a) [:sym a]
                  (string? a) [:str a]
                  [? (sequential? a)
                   sa (seq a)]
                  (into
                   [(cs (vector? a) :vec
                        (list? a) :lst
                        :seq)]
                   (map cs_3 sa))
                  [(type a) a]))

            (cs_3 [1 2 "aze" 'rt '(42 :iop a) {:a 1}])

            )

        #_(destructure '[[x y z & xs] y])
        #_(mx*' (cs [[x & xs] (range 1)] [x xs] :nop))
        )

    (defmac when! [x & body]
      `(do (assert ~x)
           ~@body))

    (defmac when-let! [[pat expr] & body]
      `(when-let [~pat (assert {"when-let! failure:" ~expr})]
         ~@body))

    (defmac let! [bs & xs]
      `(let ~bs (assert ~@xs) ~(last xs)))

)

(do :misc

    (defn call* [xs]
      #_(pp xs)
      (apl (first xs) (rest xs)))

    (defn word? [x]
      (c/or (sym? x) (kw? x)))

    (defn holymap? [x]
      (and (not (record? x))
           (map? x)))

    (defn holycoll? [x]
      (c/or (seq? x) (vec? x)
            (set? x) (holymap? x))))

(do :template

    (defn gensyms []
      (repeatedly gensym))

    (defn argv-litt [n & [prefix]]
      (vec (repeatedly n #(gensym (c/or prefix "a_")))))

    (defn quote? [x]
      (and (seq? x) (= (first x) 'quote)))

    (defn unquote? [form]
      (and (seq? form)
           (= (car form)
              'clojure.core/unquote)))

    (defn unquote-splicing? [form]
      (and (seq? form)
           (= (car form)
              'clojure.core/unquote-splicing)))

    (defn quotef
      "@bbloom/backtic, simplified version"
      [form]
      (cp form
          unquote? (second form)
          unquote-splicing? (error "splice not in list")
          holycoll?
          (let [xs (if (map? form) (cat* form) form)
                parts (for [x xs]
                        (if (unquote-splicing? x)
                          (second x)
                          [(quotef x)]))
                cat (doall `(concat ~@parts))]
            (cp form
                vec? `(vec ~cat)
                map? `(apply hash-map ~cat)
                set? `(set ~cat)
                seq? `(apply list ~cat)
                (error "Unknown collection type")))
          `'~form))

    (defmac sq
      ([x] (quotef x))
      ([x & xs] (quotef (cons x xs))))

    (_ :tries
       (mx' (sq (a b ~(+ 1 2) (sq (c b ~'~(+ 1 2 3))))))

       (let [name1 '(range 3)
             name2 'y]
         (quotef (list 'a (sq (b ~@~name1 ~'~name2 d)) 'e)))

       (quotef '(+ a b c ~(+ 1 2) ~@(range 10)))))

(do :$

    (defn redh [f xs]
      (reduce f {} xs))

    (def remnil
      (partial remove nil?))

    (defn mentry? [x]
      (instance? clojure.lang.MapEntry x))

    (defn empty [x]
      (cp x
          record? (apply dissoc x (keys x))
          mentry? []
          (c/empty x)))

    (defn $fn [ffn]
      (fn [x f]
        (if (seq? x)
          (ffn f x)
          (into (empty x) (ffn f x)))))

    (def shrink+ ($fn filter))
    (def shrink- ($fn remove))
    (def $! ($fn keep))
    (def $ ($fn map))

    (defn $vals [x f]
      ($ x (fn [[k v]][k (f v)])))

    (defn $keys [x f]
      ($ x (fn [[k v]][(f k) v])))

    (defn all? [x f]
      (when (= (count x)
               (count (filter f x)))
        (c/or x true)))

    (defn walk? [x node? f]
      (if (node? x)
        ($ x #(walk? % node? f))
        (f x)))

    (defn deep-truth [x]
      (if (coll? x)
        (all? x deep-truth)
        x))

    (assert
     (deep-truth [1 2 [3 5 {:a 1 :b 2}]])
     (not (deep-truth [1 2 [3 5 {:a nil :b 2}]])))

    )

(do :colls

    (def lst* list*)

    (defn set* [& xs] (into (set (butlast xs)) (last xs)))
    (defn set+ [& xs] (reduce into #{} xs))

    (defn vec* [& xs] (catv (butlast xs) (last xs)))
    (defn vec+ [& xs] (catv* xs))

    (def set+* (p* set+))
    (def vec+* (p* vec+))

    (_ :tests
       (set* 1 2 3 (range 34 36))
       (set+ (range 12) [45 6])
       (set+* [90 8] [(range 12) [45 6]]))

    (defn set- [& xs]
      (reduce set/difference ($ xs set)))

    (def uncs (juxt first rest))
    (def runcs (juxt butlast last))

    (defn flagmap
      ([] {})
      ([x]
       (cond
         (c/or (seq? x)(vec? x)(set? x))
         (zipmap x (repeat true))
         (nil? x) {}
         :else {x true}))
      ([x & xs] (flagmap (cons x xs))))

    (assert
     (= (flagmap :a :b)
        (flagmap (keys {:a 1 :b 2}))
        (flagmap #{:a :b})
        (flagmap (lst :a :b))
        (flagmap [:a :b])))

    (def kset
      (comp set keys))

    (defn member? [xs e]
      (contains? (set xs) e))

    (defn indexof [xs e]
      (and (member? xs e)
           (loop [i 0 [x & xs] xs]
             (if (= x e)
               i (recur (inc i) xs)))))

    (defn gat [xs i]
      (if (>= i 0)
        (cp xs
            vec? (get xs i)
            seq? (nth xs i nil)
            nil)
        (gat (reverse xs) (- i))))

    (defn not-empty [x]
      (when-not (empty? x) x))

    (defn butlasts
      [s]
      (if (seq s)
        (cons s (butlasts (butlast s)))
        '(())))

    (defn tails
      [s]
      (if (seq s)
        (cons s (tails (cdr s)))
        '(())))

    (defn gat [xs i]
     (if (>= i 0)
      (cond
       (vector? xs) (get xs i)
       (seq? xs) (first (drop i xs)))
      (gat (reverse xs) (- (inc i)))))

    (defn deep-merge
      ([x y]
       (cond
         (nil? x) y
         (nil? y) x

         (every? holymap? [x y])
         (merge-with deep-merge x y)

         (every? set? [x y])
         (into x y)

         :else y))
      ([x y & ys]
       (reduce deep-merge
               x (cons y ys))))

    (defn findeep [x p]
      (cp x
          p (list x)
          coll? (mapcat #(findeep % p) x)
          ()))

    (_ :split-at-xp

        (defn split-at
          ([x idx] (split-at x idx []))
          ([x idx acc]
           (if (zero? idx) [acc x]
               (recur (rest x) (dec idx) (conj acc (first x))))))

        (time (dotimes [_ 100000]
                (let [[pre post] (c/split-at 42 (range 100))]
                  [(doall pre) (doall post)]))) ;; 602ms

        ;; a little faster
        (time (dotimes [_ 100000]
                (let [[pre post] (split-at (range 100) 42)]
                  [(doall pre) (doall post)]))) ;; 502ms
        ))

(do :expand
    (def mx macroexpand)
    (def mx1 macroexpand-1)
    (def mx* clojure.walk/macroexpand-all)
    (defmacro mx' [x] `(mx '~x))
    (defmacro mx1' [x] `(mx1 '~x))
    (defmacro mx*' [x] `(mx* '~x)))

(do :shadowing

    (let [h (fn me [x]
              (cp x
                  sym? [x]
                  coll? (mapcat me x)
                  []))]

      (def all-syms (comp set h)))

    (defn shadows
      "given a binding form as the one that fn use for its args
       it return a set of shadowed syms"
      [binding-form]
      (->> (destructure [binding-form '_])
           (take-nth 2) set
           (clojure.set/intersection (all-syms binding-form))))

    )

(do :print

    (defn pp [& xs] (mapv clojure.pprint/pprint xs) nil)
    (defn pretty-str [& xs] (with-out-str (apply pp xs)))
    (defn prob [& xs] (mapv println xs) (last xs))
    (defn pprob [& xs] (mapv pp xs) (last xs))
    (defn dbg [& xs] (when @debug (apply println xs)))

    (defmethod clojure.pprint/simple-dispatch clojure.lang.AFunction [x]
      (clojure.pprint/simple-dispatch 'λ)))

(do :xp

    (defmacro use!
      "the purpose of this is to be able to 'use' this ns without do the :refer-clojure :exclude boilerplate
       but this does not works :)"
      []
      `(~'ns ~(symbol (str *ns*))
        (:refer-clojure :exclude ~'[assert not-empty empty or cat])
        (:use mad.boot.prelude))))

(comment

  ;; defmac works exactly like defmacro.

  (defmac postfix [& xs]
    (reverse xs))

  (is '(+ 3 2 1)
      (mx' (postfix 1 2 3 +)))

  ;; But under the covers some useful functions have been defined too.

  ;; <macro-name>-fn is a function that works exactly like the macro when given quoted-args.

  (is '(+ b a)
      (postfix-fn 'a 'b '+))

  ;; <macro-name>-fn* is the partially applied version

  (is  '(+ 3 2 1)
       (postfix-fn* '(1 2 3 +))
       (postfix-fn* 1 '(2 3 +)))

  ;; This way we can more easily compose macros implementations I think...
  ;; I mean, in the body of a macro, we can use those functions to expand some part of the resulting expression
  ;; note that macroexpand could have been used to do the same thing
  ;; but it result in more verbose code with quotes/unquote/splice...
  ;; nevertheless, we lose nothing, we only gain two functions that can be useful... so why not? :)

  (marked-fn fu "my custom lambda")

  (fu? (fu [a] a))

  )
