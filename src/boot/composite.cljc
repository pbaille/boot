(ns boot.composite
  (:refer-clojure :exclude [< get =])
  (:require [clojure.core :as core]
            [boot.control :as c]
            [boot.generics :as g]
            [boot.prelude :as u
             #?(:clj :refer :cljs :refer-macros)
             [is isnt f1 fk f_ defn+ marked-fn]]))

;; declarations
;; ------------------------------------------------------------------------------

(g/generic form [x] x)

(g/generic getter [x] (u/error "no getter impl for " x))
(g/generic updater [x] (u/error "no updater impl for " x))
(g/generic swaper [x] (u/error "no swaper impl for " x))
(g/generic checker [x] (u/error "no checker impl for " x))

(g/generic rget [x y] ((getter x) y))
(g/generic rupd [x y f] ((updater x) y f))
(g/generic rswap [x y] ((swaper x) y))
(g/generic rcheck [x y] ((checker x) y))

;; core
;; ------------------------------------------------------------------------------

(defn+ check
       ([x y] (rcheck y x))
       ([x y & ys] (and (rcheck y x) (check* x ys))))

(defn+ get
       ([x y] (rget y x))
       ([x y & ys] (reduce get (rget y x) ys)))

(defn+ swap
       ([x y] (rswap y x))
       ([x y & ys] (reduce swap (rswap y x) ys)))

(defn+ upd
       ([x y f] (rupd y x (swaper f)))
       ([x y f & others] (reduce upd* (rupd y x f) (partition 2 others))))

;; extras
;; ------------------------------------------------------------------------------

(defn+ put
       ([x l v]
        (upd x l (constantly v)))
       ([x l v & lvs]
        (reduce put*
                (upd x l v)
                (partition 2 lvs))))

(defn+ upd<
       "takes a datastructure to transform (x)
        and series of couples of form [lens(able) fn]
        executing the first transformation which associated lens does not focuses on nil"
       ([x couples]
        (when (seq couples)
          (c/or
            (c/and
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
            (fn [y] (contains? y x))

            :vec
            (let [get (getter x)]
              (fn [y] (c/? (get y) true false)))
            #_(let [cs (seq (map checker x))]
                (fn [y]
                  (loop [cs cs]
                    (if-not cs true (and ((first cs) y)
                                         (recur (next cs)))))))

            :link
            (let [get (getter (key x))
                  check (checker (val x))]
              (fn [y]
                (c/let? [v (get y)]
                        (check v))))

            :map
            #_(checker (into [] x))
            (let [cs (seq (map checker x))]
              (fn [y]
                (loop [cs cs]
                  (if-not cs
                    true
                    (and ((first cs) y)
                         (recur (next cs)))))))

            :fun
            (fn [y] (boolean (x y)))

            :any
            (partial core/= x))

(do :impl

    (defn vec->swaper [v]
      (let [ts (map swaper v)]
        (fn [y] (reduce #(%2 %1) y ts))))

    (defn link->swaper [e]
      (fn [x]
        (upd x
             (key e)
             #(swap % (val e)))))

    (defn map->swaper [m]
      (vec->swaper (mapv link->swaper m))))

(g/generic+ swaper
            [x]
            :nil identity
            :fun x
            :map (map->swaper x)
            :vec (vec->swaper x)
            :link (link->swaper x)
            :any (constantly x))

(macroexpand-1 '(g/thing (rswap [x y] :swap!)
                         (rget [x y] :get!)))

(g/generic+ getter
            [x]

            :nil
            identity

            :fun
            (let [f (or (c/core-guards x) x)]
              (fn [y] (f y)))

            #{:num :key}
            (fn [y] (core/get y x c/failure))

            :vec
            (let [gs (seq (map getter x))]
              (fn [y]
                (loop [y y gs gs]
                  (if-not gs
                    y
                    (c/let? [y ((first gs) y)]
                            (recur y (next gs)))))))

            :map
            (let [m (zipmap (keys x)
                            (map getter (vals x)))]
              (fn [y]
                #_(loop [{} ret m (seq m)]
                    (if-not m
                      ret
                      (c/let? [[k v] (first m)
                               y' (v y)]
                              (recur (assoc ret k y') (next m)))))
                (reduce (fn [a e]
                          (c/let? [v ((val e) y)]
                                  (assoc a (key e) v)
                                  (reduced nil)))
                        {} m)))

            :any
            (getter (partial (c/core-guards core/=) x)))

#_(defn lens+
    "lens composition, don't use directly
     prefer passing a vector to the 'lens function"
    [l m]
    (fn [x f]
      (c/let? [v1 (get x l)
               v2 (mut v1 m f)]
              (put x l v2))))

(defn lens
  ([x]
   (lens (getter x)
         (updater x)
         (list 'lens x)))
  ([get upd & [form']]
   (g/thing
     (getter [x] (fn [y] (get y)))
     (updater [x] (fn [y f] (upd y f)))
     (form [_] form'))))

(defn lens+
  "lens composition, don't use directly
   prefer passing a vector to the 'lens function"
  [l m]
  (lens (fn [x]
          (c/let? [lx (get x l)
                   lm (get lx m)] lm))
        (fn [x f]
          ;; the idea here is to shortcircuit when encountering an intermediate nil result
          (c/let? [v1 (get x l)
                   v2 (upd v1 m f)]
                  (put x l v2)))))

(g/generic+ updater
            [x]

            :nil
            (fn [x f] (f x))

            #{:num :key}
            (let [get (getter x)]
              (fn [y f]
                (c/? (get y)
                     (core/update y x f))))
            :vec
            (updater
              (reduce lens+ (map lens x)))

            :fun
            (let [get (getter x)]
              (fn [y f] (c/let? [y' (get y)] (f y'))))


            :map
            (let [get (getter x)]
              (fn [y f] (c/let? [z (get y)] (f z))))

            :any
            (updater (partial (c/core-guards core/=) x)))


(defmacro lazy-cast [pat & body]
  `(let [ret# (atom nil)]
     (fn [x#]
       (or @ret#
           (let [~pat x#]
             (reset! ret# (do ~@body)))))))

(let [f (lazy-cast x (println "casted " x) (str x))]
  [(f 1) (f [1 2])])

(comment
  :comparing-perfs-between-reify-and-records-construction
  (defprotocol P1 (iop [x]))
  (defprotocol P2 (pop [x]))
  (defn p1 [iop-impl] (reify P1 (iop [x] (iop-impl x))))
  (defrecord R1 [x] P1 (iop [_] x))
  (defrecord R2 [iop-impl] P1 (iop [x] (iop-impl x)))

  ;; record construction is slightly faster
  (time (dotimes [_ 100000] (p1 1)))
  (time (dotimes [_ 100000] (R1. 1)))

  (let [x (R2. identity)
        y (p1 identity)]
    #_(time (dotimes [_ 100000] (iop x)))
    (time (dotimes [_ 100000] (iop y))))

  ;; get a glance of perf impact when introducing a failure value for control flow
  (time (dotimes [_ 100000] (let [x (rand-nth [nil true false])] (when-not (nil? x) x))))
  (time (dotimes [_ 100000] (let [x (rand-nth [nil true ::fail])] (when-not (core/= ::fail x) x))))
  (time (dotimes [_ 100000] (let [x (rand-nth [nil true false])] (when-not x x)))))

(do

  (do :check-tests

      (is true (check 1 pos?))
      (is true (check [0 1 2] 2))
      (is false (check [0 1 2] 3))
      (is true
          (check {:a 1} [:a pos?]))
      (is true
          (check {:a 1 :b {:c -1 :d 0}}
                 [:a pos?]
                 [:b :c neg?]))
      (is false (check {:a 1} (first {:a neg?})))
      (is true (check {:a 1} (first {:a pos?})))
      (is true
          (check {:a 1 :b -1}
                 {:a pos?
                  :b neg?}))
      (is (check 0 [number? zero?]))
      (is true
          (check {:a 1 :b {:c -1 :d 0}}
                 {:a pos?
                  :b {:c neg? :d [number? zero?]}
                  }))

      (is false
          (check {:a 1 :b {:c -1 :d 0}}
                 {:a pos?
                  :b {:c neg? :d string?}
                  })))

  (do :get-tests

      (is 0
          (get 0 zero?)
          (get 0 [number? zero?])
          (get {:a 0} :a)
          (get {:a 0} [:a zero?])
          (get {:a {:b 0}} [:a :b])
          (get {:a {:b 0}} [:a :b zero?]))

      (is 1
          (get [1] 0) ;; getting an index
          (get [{:a 1}] [0 :a number?]))

      (is {:count 10, :sum 45}
          (get (range 10)
               {:count count
                :sum (partial apply +)}))

      (is 9/2
          (get (range 10)
               ;; using map as a getter is building a map structure where
               ;; each key contains the result of its val as a getter applied to the given seed
               {:count count
                :sum (partial apply +)}
               (fk [count sum]
                   (/ sum count)))))

  (do :keyword-lenses
      (is 1 (get {:a 1} :a))
      (is (c/failure? (get {:a 1} :b)))
      (is {:a 2} (upd {:a 1} :a inc))
      (is {:a 1 :b 1} (upd {:a 0 :b 2} :a inc :b dec)))

  (do :indexes-leses
      (is 2 (get [1 2 3] 1))
      (is [1 3 3] (upd [1 2 3] 1 inc))
      (is [2 2 2] (upd [1 2 3] 0 inc 2 dec))
      (is [1 2 [4 4]]
          (upd [1 2 [3 4]] [2 0] inc)))

  (do :composition
      ;; vector denotes composition (left to right)
      (is 1 (get {:a {:b 1}} [:a :b]))
      (is 3 (get {:a {:b [1 2 3]}} [:a :b 2]))
      (is {:a {:b 2}} (upd {:a {:b 1}} [:a :b] inc))
      (is {:a {:b 2 :c 1}}
          (upd {:a {:b 1 :c 2}}
               [:a :b] inc
               [:a :c] dec))

      (is {:a 3, :c {:d 3}}
          (upd {:a 1 :c {:d 2}}
               :a (fn [x] (+ x x x))
               [:c :d] inc)))


  (do :functions
      (is 1 (get 1 pos?))
      (is c/failure (get 1 neg?))
      (is {:a 0} (upd {:a 1} [:a pos?] dec))
      (is c/failure (upd {:a 0} [:a pos?] dec)))

  (do :branching

      (is (zero? (upd< 1
                       neg? inc
                       pos? dec)))
      (is {:a 0}

          (upd< {:a 1}
                [:a pos?] dec
                [:a neg?] inc)

          (upd< {:a -1}
                [:a pos?] dec
                [:a neg?] inc))

      (is {:a {:b 2, :c -1}}
          (upd {:a {:b 1 :c -1}}
               (< [:a :c pos?] ;; branching lens
                  [:a :b pos?])
               inc)))

  (do :option
      (is {:a {:b 1}}
          (mut {:a {:b 1}}
               (? [:a :z :b]) ;; if points to something perform the transformation, else return data unchanged
               inc))

      (is {:a {:b 2}}
          (mut {:a {:b 1}}
               (? [:a :b])
               inc)))

  (do :non-existant-keys

      (is {:a {:b {:c 42}}}
          (mut {} (path [:a :b :c]) (constantly 42)))

      (is {:a {:b {:c 42}}}
          (put {} (path :a :b :c) 42) ;; put is a thin wrapper around 'mut, it simply wrap the transformation in a constantly call
          (put {} (path [:a :b :c]) 42)
          (put {} (path :a [:b :c]) 42)
          (mut {} (path [:a :b] :c) (constantly 42)))

      (is {:b 1}
          (mut {} (path :b) (fnil inc 0))))

  (do :matching-values
      (is "io"
          (get {:a "io"} [:a "io"]))

      (is c/failure (get {:a "io"} [:a "iop"]))

      ;; if you want to match an integer (else it would be interpreted as an index lens)
      (is (core/= 2 (get [2] [0 (= 2)])))
      )

  (do :pass-tests
      ;; the pass lens can be used as a validation mecanism
      (is (pass
            {:a 1 :b "io" :p 1}
            [:a number? pos?]
            [:b string?])
          {:a 1
           :b "io"
           :p 1})

      ;; coercion
      (is (pass
            {:a 1 :b "io" :p 1}
            [:a number? pos? inc]
            [:b string?])
          {:a 2 ;; :a has been coerced
           :b "io"
           :p 1})

      )

  (do :builtins
      ;; keys
      (is {:a 2 :b 3}
          (mut {:a 1 :b 2} :* inc))

      (is '(1 2)
          (get {:a 1 :b 2} :*))

      ;; convertion
      (is (/ 11 10)
          (mut 1 (convertion #(* % 10)
                             #(/ % 10))
               inc))))

;; fn sketxh

(comment

  (fn inc0
    (:num a) ;; seq denotes arity 1 , keywords denotes type
    (inc a))

  ;; should be expanded to
  '(fn inc0
     (get a num?) ;; the type keyword is replaced by the corresponding type predicate
     (inc a))

  (is 2 (inc0 1))

  ;or

  '(fn inc0
    (t a :num) ;; maybe this is better and leaves keyword to contains check
    (inc a))

  ;; function taking several positional arguments
  (fn add1 :num ;; optional return spec
    [(:num a) (:num b)]
    (+ a b))

  (is 3
      (add1 [1 2])
      (add1 1 2))

  ;; function taking a map
  (fn add2
    {a :num
     b [number? neg?]} (+ a b))

  (is 3
      (add2 {:a 1 :b 2})
      (add2 :a 1 :b 2))

  ;; case function
  (fn add3 :num
    [(:num a)] a ;; can i strip this literal vec ?
    [(:num a) (:num b)] (+ a b)
    [a b & c] (reduce add3 (add3 a b) c))

  (is 10
      (add3 5 5)
      (add3 5 3 2)
      (add3 5 3 1 1))

  (fn pos-int
    ([int? pos?] a) a) ;; anything implementing get is a valid spec

  (fn pouet
    (I a do-stuff) (do-stuff a)) ;; a has to implement do-stuff

  (fn pouet
    (I a [do-stuff greet]) (do-stuff a)) ;; a has to implement do-stuff and greet (vector is optional)

  ;; maybe we should implement let first

  (let [(:num a) x] a)

  ;; then fn expansion use this let form
  (fn inc0 [x]
    (let [(:num a) x]
      (inc a)))

  )

(defmacro let? [v & bod]
  (let [lefts (take-nth 2 v)
        rights (take-nth 2 (next v))
        pats (map second lefts)
        body (if (next bod) (list* `do bod) bod)
        exprs (map (fn [r l]
                     (let [args (-> l next next)
                           verb (first l)
                           address (if args `(fn [x#] (~verb x# ~@args))
                                            verb)]
                       `(get ~r ~address)))
                   rights lefts)]
    `(c/let? ~(vec (interleave pats exprs))
       ~body)))

(defn wrapping-let? [x y]
  (let? [(number? a) x
         (> a 10) a
         ([number? pos-int?] b) y]
        (+ a b)))

(g/generic bind [x args seed])

(g/generic binder [x]
           :vec
           (fn [args seed]
             (let [s (gensym "_vec__")]
               (concat [s seed]
                       (mapcat (fn [pat ]))))))



