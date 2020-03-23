(ns floor.compiler.bindings
  (:require [boot.named :as n]
            [boot.prelude :as p :refer [cs]]
            [boot.generics :as g]
            [floor.compiler.composite :as compo]
            [floor.compiler.expansion :as exp]))

(g/generic bindings
         ([x options])
         ([x y options] [x y]))

(do :vec

    (defn raw-vec [v seed options]
      (let [cnt (count v)
            symseed? (symbol? seed)]
        (p/with-gensyms
          [vect head tail ¡linecheck ¡size>= ¡size=]
          (let [vect (if symseed? seed vect)]
            (p/catv
              (when-not symseed? [vect seed])
              (bindings
                [¡linecheck `(sequential? ~vect)
                 head `(floor.core/take ~vect ~cnt)
                 ¡size>= `(floor.core/eq (count ~head) ~cnt)
                 tail `(floor.core/drop ~vect ~cnt)
                 ¡size= `(floor.core/pure? ~tail)]
                options)
              (mapcat
                (fn [e i] (bindings e `(floor.core/nth ~head ~i) options))
                (seq v) (range))

              )))))

    (defn composite-vec [v seed options]
      (let [doti (p/indexof v '.)
            cars (take doti v)
            [eli & queue] (drop (inc doti) v)
            qcnt (count queue)
            symseed? (symbol? seed)]
        (p/with-gensyms
          [ysym qsym cdr']
          (let [ysym (if symseed? seed ysym)]
            (p/catv
              (when-not symseed? [ysym seed])
              (raw-vec cars `(floor.core/take ~ysym ~doti) options)
              (bindings eli `(floor.core/drop ~ysym ~doti) options)
              #_(bind.vec.body cars ysym doti)
              (when-not (zero? qcnt)
                (p/catv
                  [cdr' eli]
                  (bindings eli `(floor.core/dropend ~cdr' ~qcnt) options)
                  [qsym `(floor.core/takend ~cdr' ~qcnt)]
                  (raw-vec queue qsym options)))))))))

(do :map

    (defn map-keys [x seed options]
      (mapcat
        (fn [[k v]]
          (bindings v `(get ~seed ~k) options))
        x))


    (defn raw-map [x seed options]
      (p/with-gensyms
        [¡mapcheck ¡seed]
        (p/catv
          [¡seed seed
           ¡mapcheck `(map? ~¡seed)]
          (map-keys x ¡seed options))))

    (defn composite-map [x seed options]
      (let [rs (get x '.)
            m (dissoc x '.)
            ks (keys m)]
        (p/with-gensyms
          [¡seed]
          (p/catv
            [¡seed seed]
            (map-keys m ¡seed options)
            (bindings rs `(dissoc ~¡seed ~@ks) options))))))

(do :sym

    (defn symbol-mode [s default]
      (let [default (or default :short)]
        (condp = (first (name s))
          \¡ default
          \? :opt
          \! :strict
          \_ :short
          default)))

    (defn parse-symbol [x options]
      (let [name (name x)
            prefix (#{\? \! \¡ \_} (first name))]
        {:prefix prefix
         :name (if prefix (n/sym (or (next name) (gensym))) x)
         :mode (symbol-mode x (:binding-mode options))}))

    (defn symbol-form [seed mode]
      (condp = mode
        :short seed
        :opt `(floor.core/or ~seed nil)
        :strict `(floor.core/or ~seed (p/error "strict binding failure:\n" (floor.core/fail ~seed)))))

    (comment
      (bindings '!a 'x {}))

    )

(def operators
  (atom
    {:&
     (fn [xs seed options]
       (p/with-gensyms
         [seedsym]
         (apply p/catv
                [seedsym seed]
                (map #(bindings % seedsym options) xs))))

     :ks
     (fn [xs seed options]
       (bindings (zipmap (map (comp keyword :name parse-symbol) xs) xs)
                 seed options))

     :ks-req
     (fn [xs seed options]
       (bindings (zipmap (map keyword xs) xs) seed options))

     :ks-opt
     (fn [xs seed options]
       (let [keys (map keyword xs)
             opt-syms (map (partial n/sym "?") xs)]
         (bindings (zipmap keys opt-syms) seed options)))

     :ks-or
     (fn [xs seed options]
       (let [keys (take-nth 2 xs)
             or-exprs (map (fn [[k v]] `(or ~k ~v)) (partition 2 xs))]
         (p/catv
           ((get @operators :ks-opt) keys seed options)
           (interleave keys or-exprs))))

     :cons
     (fn [[a b] seed options]
       (p/with-gensyms
         [seedsym]
         (p/catv
           [seedsym seed]
           (bindings a `(floor.core/car ~seedsym) options)
           (bindings b `(floor.core/cdr ~seedsym) options))))

     :quote
     (fn [[a] seed options]
       (bindings (gensym "¡") `(floor.core/eq ~seed '~a) options))

     :bind_
     (fn [[p expr] seed options]
       (p/catv
         ['_ seed]
         (bindings p expr options)))

     :!
     (fn [[f & [p]] seed options]
       (bindings (or p (gensym)) (list f seed) options))

     ::default
     (fn [[verb pat & args] seed options]
       (bindings pat (list* verb seed args) options))}))

(defn compile-binding-vector [xs & [options]]
  (vec (mapcat (fn [[pat seed]]
                 (bindings pat seed (or options {})))
               (partition 2 xs))))

(defn unified
  "takes a binding vector (like let) , compile it with 'bindings
   then add unification constraints on symbols that occurs multiple times"
  [xs]
  (loop [ret [] seen #{}
         [a b & nxt] (compile-binding-vector xs)]
    (if a
      (if (seen a)
        (recur (conj ret (gensym) `(= ~a ~b)) seen nxt)
        (recur (conj ret a b) (conj seen a) nxt))
      ret)))

(defn optimize [env bs]
  (reduce
    (fn [{:keys [bindings env]} [sym expr]]
      (if (symbol? expr)
        {:bindings bindings :env (assoc-in env [(p/ns-sym) sym] {:substitute expr})}
        {:bindings (p/catv bindings [sym (exp/expand env expr)]) :env env}))
    {:env env :bindings []}
    (partition 2 bs)))

#_(optimize {} '[a b c a])

(g/generic+ bindings

            ([xs options]
             :vec
             (vec (mapcat (fn [[pat seed]]
                            (bindings pat seed options))
                          (partition 2 xs))))

            ([x seed options]

             :sym
             (let [{:keys [name mode]}
                   (parse-symbol x options)]
               [name (symbol-form seed mode)])

             :vec
             (if (compo/single-dotted? x)
               (composite-vec x seed options)
               (raw-vec x seed options))

             :map
             (if (compo/single-dotted? x)
               (composite-map x seed options)
               (raw-map x seed options))

             :lst
             (let [[v & args] x]
               (cs [k (and (symbol? v) (keyword v))
                    op (get @operators k)]
                   (op args seed options)
                   ((::default @operators) (cons v args) seed options)))
             :any
             (bindings (gensym) `(floor.core/eq ~x ~seed) options)))