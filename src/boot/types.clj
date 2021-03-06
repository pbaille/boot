(ns boot.types
  (:refer-clojure :exclude [parents >= <=])
  (:require [boot.prelude :as p :refer [cs $ $vals]]
            [boot.state :as state]
            [clojure.core :as c]
            [clojure.set :as set]
            [clojure.string :as str]))

;; this is a thin layer over clojure class hierarchy
;; the need for this comes from asparagus.boot.generics
;; which is a collection of tools to define generic functions

;; for a quick introduction by examples, see the tutorial section at the end of this file

(do :builtins

    (defn- cmap [& xs]
      ($vals (apply hash-map xs)
             hash-set))

    (do :clj

        (def atoms
          (cmap
            :fun 'clojure.lang.Fn
            :num 'java.lang.Number
            :str 'java.lang.String
            :sym 'clojure.lang.Symbol
            :key 'clojure.lang.Keyword
            :link 'clojure.lang.MapEntry))

        (def colls
          '{:lst #{clojure.lang.ISeq}
            ;;:lst #{clojure.lang.PersistentList}
            :map #{clojure.lang.PersistentArrayMap
                   clojure.lang.PersistentHashMap}
            :set #{clojure.lang.IPersistentSet}
            :vec #{clojure.lang.IPersistentVector}})

        (def prims
          (merge (cmap :nil nil)
                 atoms colls))

        (def groups
          {:prim (p/kset prims)
           :atom (p/kset atoms)
           :coll (p/kset colls)
           :word #{:key :str :sym}
           :line #{:vec :lst}
           :hash #{:map :set}}))

    (do :cljs

        (def cljs-atoms
          (cmap
            :fun 'function
            :num 'number
            :str 'string
            :sym 'Symbol
            :key 'Keyword
            :link 'MapEntry))

        (def cljs-colls
          '{:lst #{ArrayNodeSeq ChunkedCons ChunkedSeq
                   Cons Cycle ES6IteratorSeq EmptyList
                   IndexedSeq Iterate KeySeq LazySeq
                   List NodeSeq PersistentArrayMapSeq
                   PersistentQueue PersistentQueueSeq PersistentTreeMapSeq
                   RSeq Range #_RangeChunk Repeat ValSeq}
            :map #{ObjMap PersistentArrayMap PersistentHashMap PersistentTreeMap}
            :set #{PersistentHashSet PersistentTreeSet}
            :vec #{BlackNode MapEntry PersistentVector RedNode Subvec}})

        (def cljs-prims
          (merge (cmap :nil nil)
                 cljs-atoms cljs-colls))

        (def cljs-groups
          {:prim (p/kset cljs-prims)
           :atom (p/kset cljs-atoms)
           :coll (p/kset cljs-colls)
           :word #{:key :str :sym}
           :line #{:vec :lst}
           :hash #{:map :set}}))

    (def preds-symbols
      {:fun `fn?
       :vec `vector?
       ;:seq `seq?
       :lst `seq?
       :set `set?
       :map `map? #_`p/holymap?
       :num `number?
       :key `keyword?
       :sym `symbol?
       :str `string?
       :nil `nil?}))

(do :registry

    ;; the global type registry
    ;; prims key holds a map from type-keyword -> class
    ;; groups key hold a map from type-keyword -> #{type-keyword}

    (swap! state/state
           #(-> %
                (assoc-in [:clj :types] (merge prims groups))
                (assoc-in [:cljs :types] (merge cljs-prims cljs-groups))))

    (defn get-reg []
      (state/get :types))

    (defn get-type [t]
      (get (get-reg) t))

    (defn get-guards []
      (state/get :guards))

    (defn get-guard [t]
      (get (get-guards) t))

    #_(p/pp @state/state)

    (defn all-paths
      ([]
       (all-paths (get-reg)))
      ([x]
       (all-paths x (map vector (keys x))))
      ([x lines]
       (doall
         (mapcat
           (fn [l]
             (let [ll (last l)
                   xs (seq (get x ll))
                   overlap (seq (set/intersection (set l) (set xs)))]
               (cs (not xs) [l]
                   overlap (p/error "cycle! " l)
                   (all-paths x (map (partial conj l) xs)))))
           lines))))

    #_(all-paths)

    (defn cyclic? [x]
      (try (not (all-paths x))
           (catch Exception e true)))

    #_(cyclic? @reg)

    (p/defmac regfn
              [name doc & cases]
              (assert (string? doc) "doc please")
              (if (vector? (first cases))
                `(regfn ~name ~doc (~@cases))
                `(defn ~name ~doc
                   ([x#] (~name (get-reg) x#))
                   ~@cases))))

(do :basics

    (regfn childs
           "children seq"
           [reg k]
           (if (set? k)
             (mapcat (partial childs reg) k)
             (loop [ret [] ps (all-paths reg [[k]])]
               (if-let [ps (seq (filter seq ps))]
                 (let [new (set/difference (set (map first ps)) (set ret))]
                   (recur (concat ret new)
                          (map rest ps)))
                 (vec (rest ret))))))

    (regfn parents
           "parents seq"
           [reg x]
           (when-let [ps (keys (filter (fn [[_ xs]] (xs x)) reg))]
             (concat ps (mapcat (partial parents reg) ps))))

    (regfn childof
           "is x a child of y?"
           [x y]
           (and (cond (= :any y) true
                      (= :any x) false
                      :else (set/subset? (set (childs x)) (set (childs y))))
                x)
           #_((set (childs y)) x))

    (regfn parentof
           "is x a parent of y?"
           [x y]
           (and (cond (= :any x) true
                      (= :any y) false
                      :else (set/subset? (set (childs y)) (set (childs x))))
                x)
           #_((set (parents y)) x))

    (regfn classes

           "returns all classes for a type
            registry can be passed as first argument
            if not, global registry is derefered and used"

           [reg t]

           (cond

             (symbol? t)
             #_(if *cljs* (symbol? t) (class? t)) [t]

             (= :any t) (list (if (state/cljs?) 'default 'Object))

             (set? t)
             (mapcat #(classes reg %) t)

             (= :nil t) [nil]

             :else
             (when-let [cs (reg t)]
               (->> cs
                    (mapcat #(childs reg %))
                    (concat cs)
                    (filter symbol? #_class?)))))

    (defn all-types
      "return a set containing all types of a registry
   or of the global registry"
      ([] (all-types (get-reg)))
      ([reg]
       (into #{:any} (p/kset reg))))

    (def builtin-types
      (into #{:any} (concat (keys prims) (keys groups))))

    (defn split-prims []
      (let [all (get-reg)
            prim? (c/fn [[_ xs]] (c/every? #(c/or (c/nil? %) (c/symbol? %)) xs))]
        {:prims (into {} (filter prim? all))
         :groups (into {} (remove prim? all))
         :all all}))
    )

(do :assertions

    (split-prims)

    (p/assert
      (classes :nil)
      (classes :coll)
      (classes :prim)
      (classes :any)
      (classes :sym)
      (classes #{:sym :key}))

    (p/assert
      (parents :vec)
      (childs :coll))

    (childof :coll :vec)
    (childof :vec :coll)

    (childs #{:word :coll})
    (childof :sym #{:word :coll})
    (childof #{:sym :str} #{:word :coll})
    (parentof #{:sym :str} #{:word :coll})
    (parentof #{:word :coll} #{:sym :str})
    (parentof :vec :vec)
    (childof :vec :vec)
    (childof :vec :any)
    (parentof :vec :any)
    (childs :any)
    )

(do :preds

    ;; in this section, we will compile a fast predicate for each type (prims and groups)
    ;; and store all those predicates in #'builtin-preds

    #_(defn class->symbol [c]
        (-> (str c)
            (clojure.string/split #" ")
            second symbol))

    #_(defn symbol->class [s]
        (if (symbol? s)
          (let [k (resolve s)]
            (if (class? k) k
                           (p/error "not a resolvable class symbol")))
          (p/error "symbol->class needs a symbol and got: " s)))

    #_(defn ensure-class [x]
        (if (class? x) x (symbol->class x)))

    (defn symbolic-preds->or-form [ps]
      (if (= (count ps) 1)
        (first ps)
        `(clojure.core/or ~@ps)))

    (defn symbolic-pred-body [reg k gsym]
      #_(println k (type k) gsym)
      (cs [psym (preds-symbols k)]
          (list psym gsym)
          (symbol? k) #_(class? k)
          (list `instance? k #_(class->symbol k) gsym)
          [members (reg k)]
          (symbolic-preds->or-form
            (map #(symbolic-pred-body reg % gsym) members))))

    #_(symbolic-pred-body @reg :hash 'x)

    (defn symbolic-pred
      ([k] (symbolic-pred (get-reg) k))
      ([reg k]
       (if-not (map? reg)
         (symbolic-pred (get-reg) reg k)
         (do
           (p/assert {:unknown-type {k (reg k)}})
           (let [gsym (gensym)]
             `(fn [~gsym] (when ~(symbolic-pred-body reg k gsym) ~gsym))))))
      ([reg k seed]
       (p/assert {:unknown-type {k (reg k)}})
       (let [gsym (gensym)]
         `(let [~gsym ~seed]
            (when ~(symbolic-pred-body reg k gsym) ~gsym)))))

    (comment
      (symbolic-pred (get-reg) :map)
      (symbolic-pred :map)
      (symbolic-pred :uk)
      (symbolic-pred (get-reg) :hash '(heavy-computation)))
    #_(symbolic-pred (assoc (get-reg) :iop #{:hash 'clojure.lang.AMapEntry})
                     :iop)

    (defn compile-pred-map
      ([] (compile-pred-map (get-reg)))
      ([reg]
       (->> reg
            (map (fn [[k v]] [k (symbolic-pred reg k)]))
            (into {}))))

    (defn predmap
      ([] (compile-pred-map (get-reg)))
      ([reg] (compile-pred-map reg)))

    (def builtin-preds (predmap))

    #_(p/defmac sync-guards!
                "recompile the guards map, used by group+ and prim+
                 not intended to be used directly"
                [] `(state/swap! assoc :guards ~(predmap)))

    ;; initializing guards with builtin types
    #_(sync-guards!)
    #_(macroexpand '(sync-guards!))

    #_((get-in @state [:guards :map]) ())

    (p/defmac isa
              ([t] `(fn [x#] (isa ~t x#)))
              ([t x]
               (cs [? (get-type t)] `(~(symbolic-pred t) ~x)
                   (set? t) `(or ~@(map (fn [t] (isa-fn t x)) t)))))

    (p/assert
      (isa :any)
      (isa :line ())
      (isa :line [1 2 3])
      (not (isa :line {}))
      (isa :word 'a)
      (isa #{:sym :key} 'a)
      ((isa :word) :pouet))

    )

;; tuto -----------------------------------------------

(comment

  ;; asparagus.boot.type is a thin and simple layer on top of clojure's class hierarchy
  ;; lets first inpect the registry, which old the state of the system

  (clojure.pprint/pprint (get-reg))
  (classes :path)

  ;; looks like:
  '{:num #{java.lang.Number},
    :fun #{clojure.lang.Fn},
    :lst #{clojure.lang.ISeq},
    :hash #{:set :map},
    :vec #{clojure.lang.IPersistentVector},
    :key #{clojure.lang.Keyword},
    :coll #{:lst :vec :set :map},
    :sym #{clojure.lang.Symbol},
    :str #{java.lang.String},
    :line #{:lst :vec},
    :word #{:key :sym :str},
    :nil #{nil},
    :set #{clojure.lang.IPersistentSet},
    :atom #{:num :fun :key :sym :str},
    :map
    #{clojure.lang.PersistentArrayMap clojure.lang.PersistentHashMap},
    :prim #{:num :fun :lst :vec :key :sym :str :nil :set :map}}

  ;; cljs
  (binding [*cljs* true]
    (clojure.pprint/pprint (get-reg))
    (-> (get-reg) :num first type))

  ;; so we use keyword to represent what I will refer from now as 'typetags'

  ;; in the registry the keys are the typetags of our system
  ;; registry values are sets of classes and/or typetags which represent the members of the corresponding typetag
  ;; any instance of one of its members belongs to the parent type

  ;; you can extend the registry like this

  ;; adding a typetag
  (tag+ :char ;; the introduced typetag
        [java.lang.Character] ;; the classes|typetags that belongs to it
        [:prim :atom] ;; the typetags it belongs to
        )

  ;; enriching or declaring a typetag
  (tag+ :hash ;; the introduced or enriched typetag
        [:map :set] ;; the members that belongs to it
        )

  ;; there is also a way to create clojure record along with declaring a new typetag
  (type+ :pouet ;; declare a new typetag :pouet for a the record Pouet (created)
         [iop foo] ;; with two fields
         [:hash] ;; belongs to the hash type
         (g1 [x] "g1foo")) ;; implement some generic function (see asparagus.boot.generics)

  #_(map type ((get-reg) :pouet))
  ;; inspection utilities

  (childs :hash) ;;=> (:set :map)

  (childof :set :hash) ;;=> :set
  (childof :vec :hash) ;;=> nil

  ;; >= behaves like childof but is also true if the two given typetag are equals
  (<= :hash :hash) ;;=> :hash
  (<= :map :hash) ;;=> :map
  (<= :vec :hash) ;;=> nil

  (parents :map) ;;=> (:prim :coll :hash)

  (parentof :hash :map) ;;=> :hash
  (parentof :hash :vec) ;;=> nil

  ;; >= behaves like parentof but is also true if the two given typetag are equals
  (>= :hash :hash) ;;=> :hash
  (>= :hash :map) ;;=> :hash
  (>= :hash :vec) ;;=> nil

  ;; you can list all classes that belongs to a typetag

  (classes :word) ;;=> (clojure.lang.Keyword clojure.lang.Symbol java.lang.String)

  (all-types)
  ;; #{:num :fun :hash :vec :key :coll :sym
  ;;   :str :line :word :nil :seq :set :atom
  ;;   :map :prim :char :any}

  ;; isa lets you test if something belongs to a typetag
  (isa :vec []) ;;=> true
  (isa :vec "aze") ;;=> false

  ;; isa is kinf of slow, it is enough for non critical application (like compile time stuff)
  ;; if you want fast typechecks you can use those, for any registry update (prim+, group+) it is recomputed

  (let [coll? (:coll guards)]
    (coll? [1 2]) ;;=> [1 2]
    (coll? "yo") ;;=> nil
    ))








