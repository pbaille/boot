(ns boot.lenses
  (:refer-clojure :exclude [- < key get])
  (:require [clojure.core :as c]
            [boot.prelude :as p]))

;; this is stolen from https://github.com/funcool/lentes
;; i've removed the thing that I don't need, and extended it

(p/marked-fn lens-impl)

(defn lens+ [xs]
  (with-meta (apply comp xs)
    {:lens-impl true}))

;; constructor

(declare ?)

(defn lens
  "arity 1:
    convert something to a lens
   arity 2:
    Given a function for getting the focused value from a state
    (getter) and a function that takes the state and and update
    function (setter), constructs a lens."
  ([x]
   #_(println "lens " x)
   (cond

     (lens-impl? x) x

     ;; index or key lens
     (or (keyword? x) (number? x))
     (lens (fn [s] (c/get s x))
           (fn [s f] (update s x f)))

     ;; lens composition
     (map-entry? x)
     (? (lens [(! (c/key x)) (c/val x)]))

     (vector? x) (lens+ (map lens x))

     (seq? x)
     (lens-impl [next]
                (fn
                  ([y] (reduce #((%2 next) %1) y (map lens x)))
                  ([y f] (reduce #((%2 next) %1 f) y (map lens x)))))

     (map? x)
     (lens (map lens x))

     ;; functions are turned into a guard-lens
     (fn? x)
     (lens (fn [y] (when (x y) y))
           (fn [y f] (when (x y) (f y))))

     ;; values acts as = guards
     :else
     (lens (fn [y] (when (= x y) x))
           (fn [y f] (f y)))))

  ([getter setter]
   (vary-meta
    (lens-impl
     [next]
     (fn
       ([s]
        (when s (next (getter s))))
       ([s f]
        (when s (setter s #(next % f))))))
    merge
    {:setter setter :getter getter})))

(defn id-setter
  "The identity setter, applies the function to the state."
  [s f]
  (f s))

(defn const-setter
  "The constant setter, returns the state unaltered."
  [s _]
  s)

;; low level

(defn focus
  "Given a lens and a state, return the value focused by the lens."
  [l s]
  (let [getter (l identity)]
    (getter s)))

(defn over
  "Given a setter, a function and a state, apply the function over
  the value focused by the setter."
  [l f s]
  (let [setter (l id-setter)]
    (setter s f)))

;; lenses

(def id
  "Identity lens."
  (lens identity id-setter))

(def prob
  "probing lens."
  (lens (partial p/prob 'get) (fn [x f] (p/prob 'set (f x)))))

(def k
  "constant lens."
  (lens identity
        const-setter))

(def never
  (lens (constantly nil)
        (constantly nil)))

(defn convertion
  "Given a function from A to B and another in the
   opposite direction, construct a lens that focuses and updates
   a converted value."
  [one->other other->one]
  (lens one->other
        (fn [s f]
          (other->one (f (one->other s))))))

(defn upd
  ([x l f]
   (over (lens l) f x))
  ([x l f & xs]
   (reduce (fn [x [l f]] (upd x l f))
           (upd x l f)
           (partition 2 xs))))

(defn put
  ([x l v]
   (upd x l (constantly v)))
  ([x l v & xs]
   (reduce (fn [x [l v]] (put x l v))
           (put x l v)
           (partition 2 xs))))

(defn get
  ([x l]
   (focus (lens l) x))
  ([x l & ls]
   (reduce get (get x l) ls)))

(defn upd?
  ([x l f]
   (if (get x l) (upd x l f) x))
  ([x l f & xs]
   (reduce (fn [x [l f]] (upd? x l f))
           (upd? x l f)
           (partition 2 xs))))

(comment
  (upd {:a {:b 1}
        :c 0}
       [:a :b] inc
       :c dec)
  (put {:a {:b 1}
        :c 0}
       [:a :d]
       42)
  (get {:a {:b 1}
        :c 0}
       :a :b)
  (upd? {:a {:b 1}
         :c 0}
        [:a :b] inc
        :d dec))

(defn <
  "fork lens, tries every given lens in order
   use the first that does not focuses on nil"
  [& ls]
  (lens
   (fn [x]
     (loop [ls ls]
       (when (seq ls)
         (or (get x (first ls))
             (recur (next ls))))))
   (fn [x f]
     (loop [ls ls]
       (when (seq ls)
         (or (and (get x (first ls))
                  (upd x (first ls) f))
             (recur (next ls))))))))

(defn ?
  "build a lens that when focuses on nil, returns the state unchanged, or bahave normally"
  [l] (< l k))

(defn ! [l]
  "a lens that that returns nil when focuses on nil"
  (< l never))

(comment
  (upd {:b 1} (? :a) inc)
  (upd {:b 1} (! :a) inc)
  (upd {:b 1} (< :a) inc)
  (upd {:a {:c 1}} [:a (! :b)] inc)
  (get {:b 1} [(? :a) :b])

  (upd {:a 1} (< :a :b) inc)
  (upd {:b 1 :c 2} (< :a :b) inc)
  (upd {} (? (< :a :b)) inc)

  (upd {:b {:c 1}} (< :a [:b :c]) inc)
  (upd {:b {:c 1}} [:b :c] inc)

  (get {:a {:b "iop"}} [:a :b "iop"])

  (upd {:a {:b 1 :c -1}}
       #_[:a :b (guard pos?)]
       (< [:a :c pos?]
          [:a :b pos?])
       inc)

  (get 1 pos?)
  (get -1 pos?)

  (get 0 (< pos?
            neg?)))

(upd {:a {:b 1 :c -1}}
     {:a [never prob]}
     identity)

(upd {:a {:b 1 :c -1}}
     {:a prob
      :b prob}
     identity)

(upd {:a 0 :b {:c 0}}
     {:a prob
      :b :c}
     inc)

(get {:a 0 :b {:c 0}}
     {:a prob
      :b :c}
     )

(upd {:a {:b 1 :c -1}}
     {:a id} 
     p/prob)

(do :new

    (defrecord Lens [get upd])

    (defn lens? [x] (when (instance? Lens x) x))

    (declare lens)

    (defn get [x l]
      ((:get (lens l)) x))

    (defn mut
      ([x m]
       (reduce (p/p* mut) x m))
      ([x l f]
       ((:upd (lens l)) x f))
      ([x l f & lfs]
       (reduce (p/p* mut) (mut x l f)
               (partition 2 lfs))))

    (defn put
      ([x m]
       (reduce (p/p* put) x m))
      ([x l v]
       (mut x l (constantly v)))
      ([x l v & lvs]
       (reduce (p/p* put) (put x l v)
               (partition 2 lvs))))

    (defn lens+ [l m]
      (Lens. (fn [x] (-> x (get l) (get m)))
             (fn [x f] (put x l (mut (get x l) m f)))))

    (def builtins
      {:*
       (lens (fn [x] (when (map? x) (vals x)))
             (fn [x f] (p/$vals x f)))
       '*
       (lens (fn [x] (when (sequential? x) (seq x)))
             (fn [x f] (p/$ x f)))})

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
             ;; index or key lens
             (or (keyword? x) (number? x))
             (Lens. #(c/get % x)
                    #(c/update %1 x %2))

             ;; lens composition
             (vector? x) (reduce lens+ (map lens x))

             ;; functions are turned into a guard-lens
             (fn? x)
             (lens (fn [y] (when (x y) y))
                   (fn [y f] (when (x y) (f y))))

             ;; values acts as = guards
             :else
             (lens (fn [y] (when (= x y) x))
                   (fn [y f] (f y))))))

      ([get upd]
       (Lens. get upd)))


    (def k
      "Constant lens"
      (lens identity (fn [x _] x)))

    (def id
      "Identity lens."
      (lens identity (fn [x f] (f x))))

    (def prob
      "probing lens."
      (lens (partial p/prob 'get)
            (fn [x f] (p/prob 'set (f x)))))

    (def never
      (lens (constantly nil)
            (constantly nil)))

    (defn <
      "fork lens, tries every given lens in order
       use the first that does not focuses on nil"
      [& xs]
      (lens (fn [x]
              (loop [xs xs]
                (when (seq xs)
                  (or (get x (first xs))
                      (recur (next xs))))))
            (fn [x f]
              (loop [xs xs]
                (when (seq xs)
                  (when (get x (first xs))
                    (mut x (first xs) f)
                    (recur (next xs))))))))

    (defn ?
      "build a lens that when focuses on nil, returns the state unchanged, or bahave normally"
      [l] (< l k))

    (defn ! [l]
      "a lens that that returns nil when focuses on nil"
      (< l never))


    (defn convertion
      "Given a function from A to B and another in the
       opposite direction, construct a lens that focuses and updates
       a converted value."
      [one->other other->one]
      (lens one->other
            (fn [s f]
              (other->one (f (one->other s))))))


    (comment

      (get {:a 1} :a)
      (mut {:a 2} :a inc)

      (mut {:a {:b 1 :c -1}}
           #_[:a :b (guard pos?)]
           (< [:a :c pos?]
              [:a :b pos?])
           inc)

      (get {:a 1} (lens :a))
      (get {:a {:b 0}} (lens+ (lens :a) (lens :b)))
      (mut {:a {:b 0}} [:a :b] inc)

      (get {:a "io"} [:a"io"])
      (mut {:a "io"} [:a "iop"] p/prob)

      (mut {:a 1 :c {:d 2}}
           :a p/prob
           [:c :d] inc)

      (mut {:a 1 :b 2} :* inc)
      (get {:a 1 :b 2} :*)

      (mut {:a 1 :c {:d 2}}
           {:a p/prob
            [:c :d] inc}))
    )

(defn link [a b] (clojure.lang.MapEntry. a b))
(def - link)
(defn link? [x] (map-entry? x))


