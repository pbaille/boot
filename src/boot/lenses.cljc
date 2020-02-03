(ns boot.lenses
  (:refer-clojure :exclude [< get =])
  (:require #?(:clj [clojure.core :as c] :cljs [cljs.core :as c])
            [boot.prelude :as u
             #?(:clj :refer :cljs :refer-macros) [is isnt f1 f_ defn+ marked-fn]]))

;; Lens
;; -----------------------------------------------------------

(declare lens builtins id)

(defrecord Lens [get upd])

(defprotocol ILens (->lens [x]))

(defn lens? [x]
  (cond (instance? Lens x) x
        (satisfies? ILens x) (->lens x)))

(marked-fn lfn
           "'lfn works exactly like fn but
            return a function that is marked with metadata
            an lfn can be recognized via the lfn? predicate
            lfn(s) behaves differently that regular lambdas when used as a lens
            the value that it returns is persisted during navigation
            it can be used as/in a lens that performs coercion (see exemples)
            it also has a special behavior on arity 1,
            that can be used to turn a regular function to a 'lfn")

;; treating all fns as lfns could have been considered
;; introducing a function to wrap predicates into guards
;; the following form (valid in the current version)
;; (mut {:a 1} [:a number? pos? (lfn inc)] identity)
;; could have been replaced by one of those two forms
;; (mut {:a 1} [:a (guard number?) (guard pos?) inc] identity)
;; (mut {:a 1} [:a (guards number? pos?) inc] identity)

;; operations
;; -----------------------------------------------------------

(defn+ get [x l]
       ((:get (lens l)) x))

(defn+ mut
       ([x l f]
        ((:upd (lens l)) x f))
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
          (or (and (get x (ffirst couples))
                   (mut* x (first couples)))
              (mut< x (next couples)))))
       ([x l f & lfs]
        (mut< x (cons [l f] (partition 2 lfs)))))

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
         (when-let [x' (mut x (first xs) identity)]
           (pass* x' (next xs)))
         x))

;; creation
;; -----------------------------------------------------------

(defn lens+
  "lens composition, don't use directly
   prefer passing a vector to the 'lens function"
  [l m]
  (Lens. (fn [x] (some-> x (get l) (get m)))
         (fn [x f]
           ;; the idea here is to shortcircuit when encountering an intermediate nil result
           (when-let [v1 (get x l)]
             (when-let [v2 (mut v1 m f)]
               (put x l v2)))
           #_(put x l (mut (get x l) m f)))))

(defn lens
  "arity 1:
    convert something to a lens
   arity 2:
    Given a function for getting the focused value from a state
    (getter) and a function that takes the state and and update
    function (setter), constructs a lens."
  ([x]
   #_(println "lens " x)
   (or (lens? x)
       (builtins x)
       (cond

         ;; nil is the identity lens
         (nil? x)
         (lens identity
               (fn [x f] (f x)))

         ;; index or key lens
         ;; TODO handle negative indexes
         (or (keyword? x) (integer? x))
         (lens (fn [y] (c/get y x))
               (fn [y f] (when (contains? y x)
                           (c/update y x f))))

         ;; lens composition
         (vector? x)
         (reduce lens+ (map lens x))

         ;; lfn perform a transformation while navigating
         (lfn? x)
         (lens (fn [y] (x y))
               (fn [y f] (when-let [y' (x y)] (f y'))))

         ;; functions are turned into a guard-lens
         (fn? x)
         (lens (fn [y] (when (x y) y))
               (fn [y f] (when (x y) (f y))))

         ;; values acts as = guards
         :else
         (lens (partial c/= x)))))

  ([get upd]
   (Lens. get upd)))

;; instances and constructors
;; -----------------------------------------------------------

(def builtins
  {:*
   (lens (fn [x] (when (map? x) (vals x)))
         (fn [x f] (u/$vals f x)))})

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
  (let [lenses (map lens xs)]
    (lens
      (fn [x]
        (loop [xs lenses]
          (when (seq xs)
            (or (get x (first xs))
                (recur (next xs))))))
      (fn [x f]
        (loop [xs lenses]
          (when (seq xs)
            (if (get x (first xs))
              (mut x (first xs) f)
              (recur (next xs)))))))))

(defn path
  "a lens representing deep access/update in a map (with keyword keys)
   unlike regular lens composition it does not return nil if the path points to nil
   this way it can be used to introduce new values in a map (unlike lens composition, that would have failed (returning nil))"
  [& xs]
  (let [ks (flatten xs)]
    (assert (every? keyword? ks)
            "path should only contains keywords")
    (Lens. (fn [x] (c/get-in x ks))
           (fn [x f] (c/update-in x ks f)))))

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
  (lens (fn [y] (when (c/= x y) y))
        (fn [y f] (when (c/= x y) (f y)))))

;; assertions
;; -----------------------------------------------------------






