(in-ns 'floor.core)

(comment
  (defmacro lazy-cast [pat & body]
    `(let [ret# (atom nil)]
          (f [x#]
             (or @ret#
                 (let [~pat x#]
                      (reset! ret# (do ~@body)))))))

  (let [f (lazy-cast x (println "casted " x) (str x))]
       [(f 1) (f [1 2])]))

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
