(ns boot.generics-t
  (:require [boot.prelude :as p])
  (#?(:clj :require :cljs :require-macros)
   [boot.generics :as g :refer [generic generic+ fork]]
   [boot.types :as t :refer [isa]]))

#_(+ 1 1)

(generic g1 [x]
         ;; prim type impl
         :vec :g1vec
         ;; this type is a group
         ;; under the hood it implements for all collections
         :coll [:g1coll x]
         ;; group litteral can be handy
         #{:key :sym} :key-or-sym)

(p/assert
  (g1 [])
  (g1 #{})
  (g1 '())
  (g1 'a)
  (g1 :a))

;; extension
(generic+ g1 [x]
          ;; str impl
          :str [:str x]
          ;; if a last expresion is given it extends Object
          [:unknown x])

#?(:clj (do (g/get-spec! 'g1)
            (g/implementers (g/get-spec! 'g1))
            (g/get-reg)))

(p/assert
  (g1 "a")
  (g1 (atom {})))

;; poly arity exemple
(generic g2
         ([x y]
          :vec [:g2vec x y]
          :coll [:g2coll x y]
          :num [:g2num x y]
          :any [:g2any x y])
         ([x y z]
          :coll [:coll x y z])
         ;; variadic arity
         ([x y z & more]
          :any
          [:variadic x y z more]))

(p/assert
  (= (g2 [] 1)
     [:g2vec [] 1])
  (= (g2 #{} 1)
     [:g2coll #{} 1])
  (= (g2 #{} 1 2)
     [:coll #{} 1 2])
  (= (g2 "me" 1 2 3 4)
     [:variadic "me" 1 2 '(3 4)])
  (= (g2 :iop 1 2 3 4)
     [:variadic :iop 1 2 '(3 4)]))

(generic+ g2
          ([a b] :vec [:g2vec2 a b])
          ([a b c & ds] :str [:variadstr a b c ds]))

;; extension of an existing generic

(p/assert
  (= (g2 [] 1)
     [:g2vec2 [] 1])
  (= (g2 "me" 1 2 3 4)
     [:variadstr "me" 1 2 '(3 4)]))

;; fork is creating a new generic from an existing one
;; it inherit all impls and extend/overide it with given implementations
(fork g2 g2+
      ([a b] :lst [:g2+seq2 a b])
      ([a b c & ds] :str [:g2+variadstr a b c ds]))

(p/assert

  (= (g2 () 2) [:g2coll () 2])
  (= (g2+ () 2) [:g2+seq2 () 2])

  ;; original untouched
  (= (g2+ "me" 1 2 3 4)
     [:g2+variadstr "me" 1 2 '(3 4)])

  ;; original untouched
  (= (g2 "me" 1 2 3 4)
     [:variadstr "me" 1 2 '(3 4)])
  )

#?(:clj (g/get-spec! 'g2+))

(p/assert

  (= (g2 () 2) [:g2coll () 2])
  (= (g2+ () 2) [:g2+seq2 () 2])

  ;; original untouched
  (= (g2+ "me" 1 2 3 4)
     [:g2+variadstr "me" 1 2 '(3 4)])

  ;; original untouched
  (= (g2 "me" 1 2 3 4)
     [:variadstr "me" 1 2 '(3 4)])
  )

(fork g2+ g2+clone)

;; type+ is like extendtype
;; implement several generics at a time for a given type

(g/type+ :fun
         (g1 [x] :g1fun)
         (g2 [x y] [:g2fun2 x y]))

(p/assert
  (= [:g2fun2 inc 1] (g2 inc 1))
  (= :g1fun (g1 (fn [a]))))

;; the implementations given to type+ does not have to be asparagus generics,
;; it can be regular clojure protocols functions
;; CAUTION: it will not reflect type hierarchy further changes as with generics

(defprotocol Prot1 (prot1-f [x] [x y]))

(meta (resolve 'prot1-f))

(g/type+ :fun
         (g1 [x] :g1fun)
         (g2 [x y] [:g2fun2 x y])
         ;; a raw protocol function
         (prot1-f ([x] "prot1-f fun")
                  ([x y] "prot1-f fun arity 2"))) ;; <- here;; if childs are added to :fun, prot1-f will not be sync! so, use at your own risk...

#?(:clj
   (p/assert
     (= "prot1-f fun" (prot1-f inc))
     (= "prot1-f fun arity 2" (prot1-f inc 42))))


#_(p/error "stop")

(generic sip'
         ([a b]
          :vec (conj a b)
          :map (apply assoc a b)
          :set (conj a b)
          :lst (concat a [b])
          :str (str a (.toString b))
          :sym (symbol (sip' (name a) (.toString b)))
          :key (keyword (sip' (name a) (.toString b))))
         ([a b & xs]
          (apply sip' (sip' a b) xs)))

(p/assert
  (= (sip' [] 1 2 3)
     [1 2 3])
  (= (sip' #{} 1 2 3)
     #{1 2 3}))

(generic valid'
         [x]
         :nil nil
         :map (when (every? valid' (vals x)) x)
         :coll (when (every? valid' x) x)
         :word :validword
         :any x)

(p/assert
  (not (valid' [nil 1 nil]))
  (valid' [1 2 3])
  (valid' #{1 2 3})
  (valid' {:a 1 :b 2})
  (not (valid' {:a 1 :b 2 :c nil})))

#_(clojure.walk/macroexpand-all '(generic+ valid'
                                           [x] :key :validkey))

(generic+ valid'
          [x] :key :validkey)

#?(:clj (g/get-spec! 'valid'))

(p/assert
  (= :validkey (valid' :a))
  (= :validword (valid' 'a)))
