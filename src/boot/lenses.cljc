(ns boot.lenses
  (:refer-clojure :exclude [< get =])
  (:require [clojure.core :as core]
            [boot.control :as c]
            [boot.generics :as g]
            [boot.prelude :as u
             #?(:clj :refer :cljs :refer-macros)
             [is isnt f1 f_ defn+ marked-fn]]))

(declare checker lens builtins id)

(defprotocol IntoChecker
  (->checker [x]))

(defprotocol ICheck
  (-check [_ x]))

(defn checker? [x]
  (cond (satisfies? ICheck x) (partial -check x)
        (satisfies? IntoChecker x) (->checker x)))

(defprotocol IntoLens
  (->lens [x]))

(defprotocol ILens
  (-get [_ x])
  (-upd [_ x f]))

(defn lens? [x]
  (cond (satisfies? ILens x) x
        (satisfies? IntoLens x) (->lens x)))

;; checkers
;; -----------------------------------------------------------

(g/generic into-checker
           [x]

           :nil
           (constantly true)

           #{:num :key}
           (fn [y] (contains? y x))

           :vec
           (checker (lens x))

           :map
           (let [cs (mapv vector
                          (map lens (keys x))
                          (map checker (vals x)))]
             (fn [y]
               (loop [cs (seq cs)]
                 (if-not cs
                   true
                   (let [[lens check] (first cs)
                         v (get y lens)]
                     (and (c/success? v) (check v)
                          (recur (next cs))))))))

           :fun
           (fn [y] (boolean (x y)))

           :any
           (partial core/= x))

(defn lens->checker [x]
  (when-let [l (lens? x)]
    (fn [y] (boolean (-get l y)))))

(defn checker [x]
  (if (fn? x)
    (comp boolean x)
    (or (checker? x)
        (lens->checker x)
        (into-checker x))))

(defn+ check
  ([x] true)
  ([x c] ((checker c) x))
  ([x c & cs] (when (check x c) (check* x cs))))

;; operations
;; -----------------------------------------------------------

(defn+ get [x l]
       (-get (lens l) x))

(defn+ mut
       ([x l f]
        (-upd (lens l) x f))
       ([x l f & lfs]
        (reduce mut*
                (mut x l f)
                (partition 2 lfs))))

(defn+ mut<
       "takes a datastructure to transform (x)
        and series of couples of form [lens(able) fn]
        executing the first transformation which associated lens does not focuses on nil"
       ([x couples]
        (when (seq couples)
          (c/or
            (c/and
              (get x (ffirst couples))
              (mut* x (first couples)))
            (mut< x (next couples)))))
       ([x l f & lfs]
        (mut< x (cons [l f] (partition 2 lfs)))))

(c/and 1 3)

(defn+ put
       ([x l v]
        (mut x l (constantly v)))
       ([x l v & lvs]
        (reduce put*
                (put x l v)
                (partition 2 lvs))))

(defn+ pass
       "take a datastructure and a series of lenses
        try to forward x thru all given lenses
        can be used to do validation and coercion (with the help of 'lfn)"
       [x & xs]
       (if (seq xs)
         (c/let? [x' (mut x (first xs) identity)]
                 (pass* x' (next xs)))
         x))

;; creation
;; -----------------------------------------------------------



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
                   v2 (mut v1 m f)]
                  (put x l v2))
          #_(put x l (mut (get x l) m f)))))

(g/generic into-lens
           [x]

           :nil
           (lens identity
                 (fn [x f] (f x)))

           #{:num :key}
           (lens (fn [y] (core/get y x c/failure))
                 (fn [y f] (c/? (contains? y x)
                                (core/update y x f))))
           :vec
           (reduce lens+ (map lens x))

           :fun
           (lens (fn [y] (x y))
                 (fn [y f] (c/let? [y' (x y)] (f y'))))

           :map
           (let [m (zipmap (keys x) (map lens (vals x)))
                 getter
                 #(reduce (fn [a e]
                            (let [k (key e)
                                  v (get % (val e))]
                              (if v (assoc a k v) (reduced nil))))
                          {} m)]
             (lens getter
                   (fn [y f] (f (getter y)))))

           :any
           (lens (partial (c/core-guards core/=) x)))

(defn lens
  "arity 1:
    convert something to a lens
   arity 2:
    Given a function for getting the focused value from a state
    (getter) and a function that takes the state and and update
    function (setter), constructs a lens."
  ([x]
   (or (lens? x)
       (builtins x)
       (into-lens x)))

  ([get upd]
   (reify ILens
     (-get [_ x] (get x))
     (-upd [_ x f] (upd x f)))))

;; instances and constructors
;; -----------------------------------------------------------

(def core-predicates-lenses
  (u/$vals c/core-guards lens))

(def extra-lenses
  {:*
   (lens (fn [x] (c/? (map? x) (vals x)))
         (fn [x f] (u/$vals x f)))})

(def builtins
  (merge core-predicates-lenses
         extra-lenses))

(def k
  "Constant lens"
  (lens identity (fn [x _] x)))

(def id
  "Identity lens."
  (lens identity (fn [x f] (f x))))

(def prob
  "probing lens."
  (lens (partial u/prob 'get)
        (fn [x f] (u/prob 'set (f x)))))

(def never
  (lens (constantly nil)
        (constantly nil)))

(defn <
  "fork lens, tries every given lens(able) in order
   use the first that does not focuses on nil"
  [& xs]
  (let [lenses (seq (map lens xs))]
    (lens
      (fn [x]
        (loop [ls lenses]
          (if-not ls
            c/failure
            (c/let? [ret (get x (first ls))]
                    ret (recur (next ls))))))
      (fn [x f]
        (loop [ls lenses]
          (if-not ls
            c/failure
            (c/? (get x (first ls))
                 (mut x (first ls) f)
                 (recur (next ls)))))))))

(defn path
  "a lens representing deep access/update in a map (with keyword keys)
   unlike regular lens composition it does not return nil if the path points to nil
   this way it can be used to introduce new values in a map (unlike lens composition, that would have failed (returning nil))"
  [& xs]
  (let [ks (flatten xs)]
    (assert (every? keyword? ks)
            "path should only contains keywords")
    (lens (fn [x] (core/get-in x ks c/failure))
          (fn [x f] (core/update-in x ks f)))))

(defn ?
  "build a lens that when focuses on nil, returns the state unchanged, or behave normally"
  [l] (< (lens l) k))

(defn !
  "a lens that that returns nil when focuses on nil"
  [l] (< (lens l) never))

(defn convertion
  "Given a function from A to B and another in the
   opposite direction, construct a lens that focuses and updates
   a converted value."
  [one->other other->one]
  (lens one->other
        (fn [s f]
          (other->one (f (one->other s))))))

(defn = [x]
  (lens (fn [y] (if (core/= x y) y c/failure))
        (fn [y f] (if (core/= x y) (f y) c/failure))))

;; assertions
;; -----------------------------------------------------------

#_(println c/core-guards)

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

  (do :keyword-lenses
      (is 1 (get {:a 1} :a))
      (is (c/failure? (get {:a 1} :b)))
      (is {:a 2} (mut {:a 1} :a inc))
      (is {:a 1 :b 1} (mut {:a 0 :b 2} :a inc :b dec)))

  (do :indexes-leses
      (is 2 (get [1 2 3] 1))
      (is [1 3 3] (mut [1 2 3] 1 inc))
      (is [2 2 2] (mut [1 2 3] 0 inc 2 dec))
      (is [1 2 [4 4]]
          (mut [1 2 [3 4]] [2 0] inc)))

  (do :composition
      ;; vector denotes composition (left to right)
      (is 1 (get {:a {:b 1}} [:a :b]))
      (is 3 (get {:a {:b [1 2 3]}} [:a :b 2]))
      (is {:a {:b 2}} (mut {:a {:b 1}} [:a :b] inc))
      (is {:a {:b 2 :c 1}}
          (mut {:a {:b 1 :c 2}}
               [:a :b] inc
               [:a :c] dec))

      (is {:a 3, :c {:d 3}}
          (mut {:a 1 :c {:d 2}}
               :a (fn [x] (+ x x x))
               [:c :d] inc)))


  (do :functions
      (is 1 (get 1 pos?))
      (is c/failure (get 1 neg?))
      (is {:a 0} (mut {:a 1} [:a pos?] dec))
      (is c/failure (mut {:a 0} [:a pos?] dec)))

  (do :branching

      (is (zero? (mut< 1
                       neg? inc
                       pos? dec)))
      (is {:a 0}

          (mut< {:a 1}
                [:a pos?] dec
                [:a neg?] inc)

          (mut< {:a -1}
                [:a pos?] dec
                [:a neg?] inc))

      (is {:a {:b 2, :c -1}}
          (mut {:a {:b 1 :c -1}}
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




