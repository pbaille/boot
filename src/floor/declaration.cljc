(ns floor.declaration
  (:require [boot.generics :as g]
            [boot.prelude :as u]))

#?(:clj
   (do
     (g/generic read
                ([x] (read x {}))
                ([x options] x))
     (g/generic bindings
                ([x y] (bindings x y {}))
                ([x y options] [x y]))))

(g/generic form [x] x)

(g/generic fail [x])
;; TODO I want to write (deft failure [data] (fail [_] data))
(g/deft :failure [data] []
        (fail [this] (:data this)))

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
         ([x y f & others] (reduce upd* (rupd y x f) (partition 2 others)))))
