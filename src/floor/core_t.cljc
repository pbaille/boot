(in-ns 'floor.core)

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

    (is [(failure 0) 1] (cs [?a (failure 0)] [a 1] 2))

    (is [0 1] (cs [?a 0] [a 1] 2))

    (is ::catched
        (try (cs [!a (failure 0)] [a 1] 2) (catch Throwable e ::catched)))

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

    (is (?let [a 1 b a] (add a b))
        2)

    (is (failure? (let [(pos? a) -1] (p/error "never touched"))))

    (throws
      (let [!a (pos? -1)] :never))

    (is (let [a 1 ?b (failure :aaaargg)] (add a (or b 0)))
        1)

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

    (is (cs [x (pos? -1)] {:pos x}
            [x (neg? -1)] {:neg x})
        {:neg -1})

    (let [f (c/fn [seed]
              (cs [x (num? seed) x++ (inc x)] x++
                  [x (str? seed) xbang (+ x "!")] xbang))]
         (is (f 1))
         (is "yo!" (f "yo"))
         (is (failure? (f :pop))))

    (is (cs [x (pos? 0) n (p/error "never touched")] :pos
            [x (neg? 0) n (p/error "never touched")] :neg
            :nomatch)
        :nomatch)

    (throws
      (!cs [x (pos? 0)] :pos
           [x (neg? 0)] :neg))

    (let [f (f [seed]
               (csu [[a a] seed] :eq
                    [[a b] seed] :neq))]
         (is :eq (f [1 1]))
         (is :neq (f [1 2])))

    (let [x [:tup [1 2]]]
         (throws
           (!csu [[:wat a] x] :nop
                 [(:vec vx) x [:tup [a a]] vx] :yep)))

    (let [p [:point 0 2]]
         (cs [[:point x 0] p] :y0
             [[:point 0 y] p] :x0
             [[:point x y] p] [x y]))

    )

(do :check-tests

    (is true (check 1 pos?))
    (is true (check [0 1 2] 2))
    (is (failure? (check [0 1 2] 3)))
    (is true
        (check {:a 1} [:a pos?]))
    (is true
        (check {:a 1 :b {:c -1 :d 0}}
               [:a pos?]
               [:b :c neg?]))
    (is (failure? (check {:a 1} (car {:a neg?}))))
    (is true (check {:a 1} (car {:a pos?})))
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

    (is (failure?
          (check {:a 1 :b {:c -1 :d 0}}
                 {:a pos?
                  :b {:c neg? :d string?}
                  }))))

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
             (p/fk [count sum]
                   (/ sum count)))))

(do :keyword-lenses
    (is 1 (get {:a 1} :a))
    (is (failure? (get {:a 1} :b)))
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
             :a (f [x] (add x x x))
             [:c :d] inc)))


(do :functions
    (is 1 (get 1 pos?))
    (is (failure? (get 1 neg?)))
    (is {:a 0} (upd {:a 1} [:a pos?] dec))
    (is (failure? (upd {:a 0} [:a pos?] dec))))

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
             ((:< lenses)
              [:a :c pos?] ;; branching lens
              [:a :b pos?])
             inc)))

(do :option
    (is {:a {:b 1}}
        (upd {:a {:b 1}}
             ((:? lenses) [:a :z :b]) ;; if points to something perform the transformation, else return data unchanged
             inc))

    (is {:a {:b 2}}
        (upd {:a {:b 1}}
             ((:? lenses) [:a :b])
             inc)))

(do :non-existant-keys

    (is {:a {:b {:c 42}}}
        (upd {} ((:path lenses) [:a :b :c]) (constantly 42)))

    (is {:a {:b {:c 42}}}
        (put {} ((:path lenses) :a :b :c) 42) ;; put is a thin wrapper around 'mut, it simply wrap the transformation in a constantly call
        (put {} ((:path lenses) [:a :b :c]) 42)
        (put {} ((:path lenses) :a [:b :c]) 42)
        (upd {} ((:path lenses) [:a :b] :c) (constantly 42)))

    (is {:b 1}
        (upd {} ((:path lenses) :b) (fnil inc 0))))

(do :matching-values
    (is "io"
        (get {:a "io"} [:a "io"]))

    (is (failure? (get {:a "io"} [:a "iop"])))

    ;; if you want to match an integer (else it would be interpreted as an index lens)
    (is 2 (get [2] [0 ((:eq lenses) 2)]))
    )

(do :pass-tests
    ;; the pass lens can be used as a validation mecanism
    (is ((:pass lenses)
          {:a 1 :b "io" :p 1}
          [:a number? pos?]
          [:b string?])
        {:a 1
         :b "io"
         :p 1})

    ;; coercion
    (is ((:pass lenses)
          {:a 1 :b "io" :p 1}
          [:a number? pos? inc]
          [:b string?])
        {:a 2 ;; :a has been coerced
         :b "io"
         :p 1})

    )

(do :misc

    ;; convertion
    (is (div 11 10)
        (upd 1 ((:convertion lenses)
                #(mul % 10)
                #(div % 10))
             inc)))

(comment :bench

         (defmacro qb
           ([e] `(qb 100000 ~e))
           ([n e]
            `(time (dotimes [_# ~n] ~e))))


         (qb (cs [a 1 b a] (add a b)))
         (qb (csu [a 1 a 1] (add a a)))
         (qb (c/let [a 1 b a] (add a b)))

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
         (time (dotimes [_ 100000] (c/let [a 1 b a] (add a b)))))