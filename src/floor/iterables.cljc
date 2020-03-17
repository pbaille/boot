(ns floor.iterables
  (:refer-clojure :exclude [+ last take drop butlast cons])
  (:require [clojure.core :as c]
            [boot.prelude :as p :refer [is isnt]]
            [boot.generics :as g]
            [floor.declaration :as d]
            [floor.monoids :as m :refer [lst]]))

(g/generic+
  d/iter
  [a]
  :nil ()
  #{:sym :key} (d/iter (name a))
  :any (or (seq a) ()))

(g/generic+
  d/vals
  [x]
  :map (or (vals x) ())
  :coll (d/iter x)
  :any (p/error "vals: no impl for " x))

(g/generic+
  d/idxs
  [x]
  :map (or (keys x) ())
  :set (d/iter x)
  :coll (range (count x))
  :any (p/error "idxs: no impl for " x))

(defmacro defiterg
  "an update to define generic functions for iterables
   hiding the iter/wrap boilerplate"

  [name [a1 :as argv] expr]
  `(g/generic
     ~name
     ~argv
     :lst
     ~expr
     (let [a# ~a1
           ~a1 (d/iter ~a1)]
       (m/wrap* a# ~expr))))

(g/generic car [x] (c/first (d/iter x)))
(g/generic last [x] (c/last (d/iter x)))
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
    (d/+ (d/pure cdr) cars cdr)))

(defn cons? [x]
  (when (and (coll? x)
             (not (d/pure? x)))
    x))

;; vector optimized impls

(g/type+
  :vec
  (last [x] (get x (dec (count x))))
  (take [x n] (subvec x 0 (min (count x) n)))
  (drop [x n] (subvec x (min (count x) n)))
  (takend [x n] (let [c (count x)] (subvec x (- c n) c)))
  (dropend [x n] (subvec x 0 (- (count x) n)))
  (butlast [x] (subvec x 0 (dec (count x))))
  (section [x from to] (subvec x (max 0 from) (min (count x) to)))
  (cdr [x] (subvec x 1)))

(do :assertions

    ;; car (is like Lisp's car or clojure.core/first)
    (is 1 (car (lst 1 2)))
    (is 1 (car [1 2]))
    (is [:a 1] (car {:a 1 :b 2}))

    ;; cdr (is like clojure.core/rest but preserve collection type)
    (is (cdr [1 2 3]) [2 3])
    (is (cdr (lst 1 2 3)) (lst 2 3))
    (is (cdr {:a 1 :b 2 :c 3}) {:b 2 :c 3})

    ;; last
    (is 2 (last (lst 1 2)))
    (is 2 (last [1 2]))
    (is [:b 2] (last {:a 1 :b 2}))

    ;; butlast (is like clojure.core/butlast but preserve collection type)
    (is (cdr [1 2 3]) [2 3])
    (is (cdr (lst 1 2 3)) (lst 2 3))
    (is (cdr {:a 1 :b 2 :c 3}) {:b 2 :c 3})

    ;; take (like clojure.core/take with arguments reversed and preserving collection type)
    (is (take (lst 1 2 3) 2) (lst 1 2))
    (is (take [1 2 3] 2) [1 2])
    (is (take {:a 1 :b 2 :c 3} 2) {:a 1 :b 2})

    ;; drop
    (is (drop (lst 1 2 3) 2) (lst 3))
    (is (drop [1 2 3] 2) [3])
    (is (drop {:a 1 :b 2 :c 3} 2) {:c 3})

    ;; takend
    (is (takend (lst 1 2 3) 2) (lst 2 3))
    (is (takend [1 2 3] 2) [2 3])
    (is (takend {:a 1 :b 2 :c 3} 2) {:b 2 :c 3})

    ;; dropend
    (is (dropend (lst 1 2 3) 2) (lst 1))
    (is (dropend [1 2 3] 2) [1])
    (is (dropend {:a 1 :b 2 :c 3} 2) {:a 1})

    ;; rev
    (is (rev [1 2 3]) [3 2 1])
    (is (rev (lst 1 2 3)) (lst 3 2 1))

    ;; section (select a subsection of a sequantial data structure)
    (is (section [1 2 3 4 5 6] 2 5) [3 4 5])
    (is (section (lst 1 2 3 4 5 6) 1 5) (lst 2 3 4 5))

    ;; splat (split a sequential datastructure at the given index)
    (is (splat [1 2 3 4] 2) [[1 2] [3 4]])
    (is (splat (lst 1 2 3 4) 2) [(lst 1 2) (lst 3 4)])

    ;; uncs (uncons)
    (is (uncs [1 2 3]) [1 [2 3]])
    (is (uncs (lst 1 2 3)) [1 (lst 2 3)])

    ;; runcs
    (is (runcs [1 2 3]) [[1 2] 3])
    (is (runcs (lst 1 2 3)) [(lst 1 2) 3])

    ;; cons
    (is (cons 1 [2 3]) [1 2 3])
    (is (cons 1 (lst 2 3)) (lst 1 2 3))
    ;; it can take more arguments
    (is (cons 0 1 [2 3]) [0 1 2 3])
    (is (cons 1 2 3 (lst)) (lst 1 2 3))

    ;; cons?
    (is (cons? [1 2]) [1 2])
    (isnt (cons? []))
    (is (cons? (lst 1 2)) (lst 1 2))
    (isnt (cons? (lst)))
    (is (cons? {:a 1}) {:a 1})
    (isnt (cons? {}))
    (isnt (cons? #{})))

