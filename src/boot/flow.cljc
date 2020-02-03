(ns boot.flow
  (:refer-clojure :exclude [> <])
  (:require [boot.prelude :as u #?(:clj :refer :cljs :refer-macros) [is isnt f1 f_ defn+]]
            [boot.lenses :as l]))

;; links

(defn link [a b]
  #?(:clj  (clojure.lang.MapEntry. a b)
     :cljs (cljs.core/MapEntry. a b nil)))

(def link? map-entry?)

;; transformations

(defprotocol ITrans (->trans [x]))
(defprotocol ICombine (combine [x y]))

(defn trans? [x]
  (or (when (fn? x) x)
      (when (satisfies? ITrans x) (->trans x))))

(do :impl

    (declare trans step)

    (defn vec->trans [v]
      (let [ts (map trans v)]
        (fn [y] (reduce #(%2 %1) y ts))))

    (defn link->trans [e]
      (fn [x]
        (l/mut x
               (key e)
               #(step % (val e)))))

    (defn map->trans [m]
      (vec->trans (mapv link->trans m))))

(defn trans
  "given anything, return a function representing a transformation (a reduction step of '> )
   used in 'step when its first argument (the seed) does not implement ICombine"
  [x]
  (or (trans? x)
      (cond
        (nil? x) identity
        (map? x) (map->trans x)
        (link? x) (link->trans x)
        (vector? x) (vec->trans x)
        :else (constantly x))))

;; flow

(defn step [x y]
  (if (satisfies? ICombine x)
    (combine x y)
    ((trans y) x)))

(defn+ >
       "thread x thru given transformations (xs) shortcircuiting on first nil result"
       [x & xs]
       (loop [x x xs xs]
         (if (and x xs)
           (recur (step x (first xs)) (next xs))
           x)))

(defn+ <
       "try all given transformations over x until the first non nil result"
       [x & xs]
       (loop [xs xs]
         (when (seq xs)
           (or (step x (first xs))
               (recur (next xs))))))

(defn at
  "arity 2:
    the at function returns a trans(able)
    built upon 'lenses/path, 'path does not have to point to an existing value to succeed
   variadic artity
    takes several couples (flat), that will be executed in order (by the transformation it returns)"
  ([path f]
   (link (l/path path) f))
  ([x y & zs]
   (reduce (fn [f [p g]]
             (comp (link->trans (at p g)) f))
           (link->trans (at x y))
           (partition 2 zs))))




