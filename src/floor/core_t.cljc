(in-ns 'floor.core)


(p/mx*' (? [a 1] a))

(comment
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
  (bindings '(pos? a) 'x)
  )

(do :control

    (is 1 (cs [a 1] a))

    (is failure0
        (cs [a failure0] a))

    (is (failure "my failure")
        (cs [a (failure "my failure")] a))

    (p/throws (!cs failure0))
    (p/throws (!cs [a failure0] a))
    (is 1 (!cs [a 1] a))

    (is 1 (cs [a failure0] a 1))

    (is 1 (cs [a failure0] a
              [b 1] b))

    (is (failure 2)
        (cs [a failure0] a
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

    (clojure.walk/macroexpand-all '(cs [a failure0] a
                                       [b (failure 2)] b))


    (macroexpand (CS-expand
                   {}
                   '([[a b c] failure0] a
                     [[a b c] (failure 2)] b
                     pouet)
                   {}))

    (CS-expand
      {}
      '([[a b c] pouet] :iop :nop)
      {})

    (bindings '[a b c] 'xs)
    )

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
    (isnt (cons? []))
    (is (cons? (lst 1 2)) (lst 1 2))
    (isnt (cons? (lst)))
    (is (cons? {:a 1}) {:a 1})
    (isnt (cons? {}))
    (isnt (cons? #{})))

