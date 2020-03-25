(in-ns 'floor.core)


(p/mx*' (? [a 1] a))

(defmacro fails [& xs]
  `(do ~@(c/map (f [e] `(is (failure? ~e))) xs)))

(comment
  (require '[floor.compiler.bindings :refer [bindings]])
  (bindings '[a b . c] 'x {})
  (bindings '[a b c] 'x {})
  (bindings '[a b . c] 'x {})
  (bindings '[a b . c d] 'x {})
  (bindings '[_ b . c d] 'x {:binding-mode :strict})
  (bindings '{:a a :b bibi} 'x {})
  (bindings '{:a a :b bibi . r} 'x {})
  (bindings 'a 'x)
  (bindings '?a 'x {})
  (bindings '!a 'x {})
  (bindings '¡a 'x {:binding-mode :strict})
  (bindings '¡a 'x {})
  (bindings '(& a b) 'x)
  (bindings '(& mymap (ks a b)) 'x {})
  (bindings '(pos? a) 'x)

  (bindings '[?a (failure 0)] {})

  (let [?a (failure 0)] a)
  )

(or (failure 1) (failure 2))

(do :control

    (is 1 (cs [a 1] a))

    (is (failure 1)
        (cs [a (failure 1)] a))

    (is (failure "my failure")
        (cs [a (failure "my failure")] a))

    (p/throws (!cs [a (failure 1)] a))
    (is 1 (!cs [a 1] a))

    (is 1 (cs [a (failure 1)] a 1))

    (is 1 (cs [a (failure 1)] a
              [b 1] b))

    (is (failure 2)
        (cs [a (failure 1)] a
            [b (failure 2)] b))

    (is :bottom
        (cs [a (failure 1)
             _printed (println "never")] a
            [something 42
             b (failure 2)] b
            :bottom))

    (is [nil 1] (cs [?a failure0] [a 1] 2))

    (is [0 1] (cs [?a 0] [a 1] 2))

    (is ::catched
        (try (cs [!a failure0] [a 1] 2) (catch Throwable e ::catched)))

    (is 3 (or (failure 1) (failure 2) 3))
    (is 3 (and 1 2 3))
    (is (failure 3) (and 1 2 (failure 3) 4))

    )

(do :monoids

    (is [] (pure [1 2 3]))
    (is #{} (pure #{:pouet 12}))
    (is {} (pure {:a 1}))
    (is "" (pure "hello"))

    (is (sip [] 1 2) [1 2])
    (is (sip [1] 2 3) [1 2 3])
    (is (sip #{1} 2 3) #{1 2 3})
    (is (sip {:a 1} [:b 2] [:c 3]) {:a 1 :b 2 :c 3})
    (is ((sip c/+ 1) 1) 2)

    (is () (iter []))
    (is () (iter nil))
    (is () (iter ""))
    (is '(1 2) (iter [1 2]))
    (is '(1 2) (iter '(1 2)))
    (is '([:a 1] [:b 2]) (iter {:a 1 :b 2}))
    (is '(\f \o \o) (iter "foo") (iter (sym "foo")) (iter :foo))

    (is (+ {:a 1} {:b 2})
        {:a 1 :b 2})
    (is (+ '(1 2) [3 4])
        '(1 2 3 4))
    (is (+ [1 2] '(3 4) [5 6] '(7 8))
        [1 2 3 4 5 6 7 8])
    (is (+ #{1 2} [3 4] '(5 6))
        #{1 2 3 4 5 6})
    (is (+ :foo :bar)
        :foobar)
    (is (+ 'foo :bar "baz")
        'foo:barbaz)
    (is (+ "foo" 'bar 'baz)
        "foobarbaz")
    (is ((+ inc inc inc) 0)
        3)

    (is '(1 2 3)
        (vals '(1 2 3))
        (vals [1 2 3])
        (sort (vals {:a 1 :b 2 :c 3}))
        (sort (vals #{1 2 3})))

    (is '(0 1 2)
        (idxs '(1 2 3))
        (idxs [1 2 3]))
    (is (lst :a :b :c)
        (sort (idxs {:a 1 :b 2 :c 3}))
        (sort (idxs #{:a :b :c})))

    (is [] (pure? []))
    (is #{} (pure? #{}))
    (is "" (pure? ""))
    (is {} (pure? {}))
    (is (failure? (pure? [1 2])))
    (is (failure? (pure? {:a 1})))
    (is (failure? (pure? "iop")))

    (is (vec 1 2 3)
        (vec* 1 [2 3])
        (vec+ '(1) [2 3])
        (vec+* '(1) [[2] #{3}])
        [1 2 3])

    (is (lst 1 2 3)
        (lst* 1 [2 3])
        (lst+ '(1) [2 3])
        (lst+* '(1) [[2] #{3}])
        '(1 2 3))

    (is (set 1 2 3)
        (set* 1 [2 3])
        (set+ '(1) [2 3])
        (set+* '(1) [[2] #{3}])
        #{1 2 3})

    (is (map [:a 1] [:b 2] [:c 3])
        (map* [:a 1] {:b 2 :c 3})
        (map* [:a 1] #{[:b 2] [:c 3]})
        (map+ {:a 1} #{[:b 2]} {:c 3})
        {:a 1 :b 2 :c 3})

    (is (key "iop" 'foo :bar)
        :iopfoobar)
    (is (sym "iop" 'foo :bar)
        'iopfoo:bar)
    (is (str "iop" 'foo :bar)
        "iopfoo:bar"))

(do :iterables

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
    (is (failure? (cons? [])))
    (is (cons? (lst 1 2)) (lst 1 2))
    (is (failure? (cons? (lst))))
    (is (cons? {:a 1}) {:a 1})
    (is (failure? (cons? {})))
    (is (failure? (cons? #{}))))

(do :bindings

    (is (let [a 1] a)
        1)

    (is (let [a 1 b 2] (add a b))
        3)

    ;; refer earlier binding

    (is (let [a 1 b a] (add a b))
        2)

    ;; sequential bindings

    (is (let [[a b c] [1 2 3]] [a b c])
        (let [[a b c] '(1 2 3)] [a b c])
        (let [[a b c] (next (range 4))] [a b c])
        [1 2 3])

    (c/every?
      #(is (failure? %))
      [(let [[a b c] [1 2]] [a b c])
       (let [[a b c] [1 2]] [a b c])
       (let [[a b c] [1 2 3 4]] [a b c])
       (let [[a b c] '(1 2 3 4 5)] [a b c])
       (let [[a b c] (range)] [a b c])])

    (is (let [[a b c . xs] (range 10)] [a b c xs])
        [0 1 2 '(3 4 5 6 7 8 9)])
    (is (let [[a b c . xs] (range 3)] [a b c xs])
        [0 1 2 ()])

    (fails (let [[a b c . xs] (range 2)] [a b c xs]))

    ;; preserve collection type

    (is (let [[x . xs] (vec 1 2 3)] [x xs])
        [1 [2 3]])

    ;; post rest pattern

    (is (let [[x . xs lastx] (range 6)] [x xs lastx])
        [0 (range 1 5) 5])

    ;; maps
    (is (let [{:a aval :b bval} {:a 1 :b 2 :c 3}] [aval bval])
        [1 2])

    ;; maps have rest patterns to
    (is (let [{:a aval . xs} {:a 1 :b 2 :c 3}] [aval xs])
        [1 {:b 2 :c 3}])

    ;; ks (similar to :keys)
    (is (let [(ks a b) {:a 1 :b 2 :c 3}] (add a b))
        3)

    ;; & (parrallel bindings)
    (is (let [(& mymap (ks a b)) {:a 1 :b 2 :c 3}] [mymap a b])
        [{:a 1 :b 2 :c 3} 1 2])

    ;; guards
    (is (let [(pos? a) 1 (neg? b) -1] (add a b))
        0)


    (fails (let [a (failure 0)
                 b (p/error "never evaluated")]
                42))

    ;; strict bindings
    ;; binding symbol's prepended by ! must bind to non nil value
    (is :catched
        (try (let [!a (pos? -1)] :never)
             (catch Exception _ :catched)))

    ;; you can use ? and ! prefixes in guard patterns but...
    ;; it is not so pretty... see '?let section

    (fails (let [(pos? a) 1 (neg? b) 0] (div a b)))

    ;; type guards
    (is [1 2] (let [(:vec v) [1 2]] v))
    (fails (let [(:map v) [1 2] _ (p/error "never")] v))

    (is :ok (let [:yo (key "yo")] :ok))
    (fails (let [:yo 42] :ok))
    (is :ok (let [a (inc 2) 3 a] :ok))
    (is :ok (let [a 1 b 2 3 (add a b)] :ok))


    (is 1 (?let [a (failure 0) b 1] b))

    :accumulate-bindings
    (is (?let [a 1 b a] (add a b))
        2)


    (defmacro qb
      ([e] `(qb 100000 ~e))
      ([n e]
       `(time (dotimes [_# ~n] ~e))))


    (qb (cs [a 1 b a] (add a b)))

    (qb
      (let*
        [G__17516 (clojure.core/let [a 1] (if (floor.core/success? a) #:floor.compiler.expanders{:cs-return (add a a)} a))]
        (if (floor.core/success? G__17516) (clojure.core/get G__17516 :floor.compiler.expanders/cs-return) G__17516)))

    (qb
      (let*
        [G__17516 (clojure.core/let [a 1] (if (floor.core/success? a) (add a a) a))]
        (if (floor.core/success? G__17516) G__17516 G__17516)))

    (qb
      (let*
        [G__17516 (clojure.core/let [a 1] (if-not (instance? Failure a) (add a a) a))]
        (if G__17516 G__17516 G__17516)))

    (macroexpand '(g/implements? [] fail))


    (time (dotimes [_ 100000] (g/implements? (failure 0) fail)))
    (time (dotimes [_ 100000] (nil? nil)))
    (time (dotimes [_ 100000] (c/let [a 1 b a] (add a b))))

    :guards
    "with guards ?let make sense"
    (nil? (?let [(pos? a) -1] (p/error "never touched")))

    :bang-prefix
    "in ?let ! behaves the same as in let"
    (throws
      (?let [!a (pos? -1)] :never))

    :underscore-prefix
    "if you want to allow some binding to be nil in a ?let form use the _ prefix"
    (is (macroexpand '(let [a 1 ?b (failure :aaaargg)] (add a (or b 0))))
        1)



    :lut
    (is (lut [a 1 a 1] (add a a))
        2)

    ;; this shorts because the second binding of a does not unify with the previous one
    (fails (lut [a 1 a (inc a)] (p/error "never touched")))

    (is (!lut [a 1 a 1] (add a a))
        2)

    ;; on failing unification it throws
    (is :catched
        (try (!lut [a 1 a (inc a)] :never)
             (catch Exception _ :catched)))
    )


