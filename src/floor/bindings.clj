(ns floor.bindings
  (:require [floor.declaration :as d :refer [bindings]]
            [floor.composite :as c]
            [boot.named :as n]
            [boot.generics :as g]
            [boot.prelude :as p :refer [cs]]
            [boot.types :as t]))

(defn line? [x]
  (or (seq? x)
      (vector? x)))

(defmacro with-gensyms [xs & body]
  `(let [~xs (map gensym ~(mapv #(str (name %) "_") xs))]
     ~@body))

(do :vec

    (defn vec_raw-bindings [v seed options]
      (let [cnt (count v)
            symseed? (symbol? seed)]
        (with-gensyms
          [vect _head _tail ¡linecheck ¡size>= ¡size=]
          (let [vect (if symseed? seed vect)]
            (p/catv
              (when-not symseed? [vect seed])
              (d/bindings ¡linecheck `(line? ~vect) options)
              [_head `(take ~cnt ~vect)
               (d/bindings ¡size>= `(= (count ~_head) ~cnt) options)
               _tail `(drop ~cnt ~vect)
               (d/bindings ¡size= `(not (seq ~_tail)) options)]
              (mapcat
                (fn [e i] (d/bindings e `(nth ~_head ~i (d/failure {:index-not-found ~i})) options))
                (seq v) (range)))))))

    (defn vec_composite-bindings [v seed options]
      (let [doti (p/indexof v '.)
            cars (vec (take doti v))
            [eli & queue] (drop (inc doti) v)
            qcnt (count queue)
            symseed? (symbol? seed)]
        (with-gensyms
          [ysym qsym cdr']
          (let [ysym (if symseed? seed ysym)]
            (p/catv
              (when-not symseed? [ysym seed])
              (vec_raw-bindings cars `(take ~doti ~ysym) options)
              (d/bindings eli `(drop ~doti ~ysym) options)
              #_(bind.vec.body cars ysym doti)
              (when-not (zero? qcnt)
                (p/catv
                  [cdr' eli]
                  (d/bindings eli `(drop-last ~qcnt ~cdr') options)
                  [qsym `(take-last ~qcnt ~cdr')]
                  (vec_raw-bindings queue qsym options)))))))))

(do :map



    (defn map_keys-bindings [x seed options]
      (mapcat
        (fn [[k v]]
          (d/bindings v `(get ~seed ~k) options))
        x))


    (defn map_raw-bindings [x seed options]
      (with-gensyms
        [¡mapcheck ¡seed]
        (p/catv
          [¡seed seed
           ¡mapcheck `(map? ~¡seed)]
          (map_keys-bindings x ¡seed options))))

    (defn map_composite-bindings [x seed options]
      (let [rs (get x '.)
            m (dissoc x '.)
            ks (keys m)]
        (with-gensyms
          [¡seed]
          (p/catv
            [¡seed seed]
            (map_keys-bindings m ¡seed options)
            (d/bindings rs `(dissoc ~¡seed ~@ks) options))))))

(do :sym

    (defn sym_binding-mode [s default]
      (let [default (or default :short)]
        (condp = (first (name s))
          \¡ default
          \? :opt
          \! :strict
          \_ :short
          default)))

    (defn sym_parse [x options]
      (let [name (name x)
            prefix (#{\? \! \¡ \_} (first name))]
        {:prefix prefix
         :name (if prefix (n/sym (next name)) x)
         :mode (sym_binding-mode x (:binding-mode options))}))

    (defn sym_form [seed mode]
      (condp = mode
        :short seed
        :opt `(or ~seed nil)
        :strict `(or ~seed (ex-info "binding" {:failure (d/fail ~seed)}))))

    )

(def operators
  (atom
    {:&
     (fn [xs seed options]
       (with-gensyms
         [seedsym]
         (apply p/catv
                [seedsym seed]
                (map #(d/bindings % seedsym options) xs))))

     :ks
     (fn [xs seed options]
       (d/bindings (zipmap (map (comp keyword :name sym_parse) xs) xs)
                   seed options))

     :ks-req
     (fn [xs seed options]
       (d/bindings (zipmap (map keyword xs) xs) seed options))

     :ks-opt
     (fn [xs seed options]
       (let [keys (map keyword xs)
             opt-syms (map (partial p/sym "?") xs)]
         (d/bindings (zipmap keys opt-syms) seed options)))

     :ks-or
     (fn [xs seed options]
       (let [keys (take-nth 2 xs)
             or-exprs (map (fn [[k v]] `(or ~k ~v)) (partition 2 xs))]
         (p/catv
           ((get @operators :ks-opt) keys seed options)
           (interleave keys or-exprs))))

     :cons
     (fn [[a b] seed options]
       (with-gensyms
         [seedsym]
         (p/catv
           [seedsym seed]
           (d/bindings a `(first ~seedsym) options)
           (d/bindings b `(next ~seedsym) options))))

     :quote
     (fn [[a] seed options]
       (d/bindings (gensym "¡") `(= ~seed '~a) options))

     :bind_
     (fn [[p expr] seed options]
       (p/catv
         ['_ seed]
         (d/bindings p expr options)))

     :!
     (fn [[f & [p]] seed options]
       (d/bindings (or p (gensym)) (list f seed) options))

     ::default
     (fn [[verb pat & args] seed options]
       (d/bindings pat (list* verb seed args) options))}))

(defn compile-binding-vector [xs & [options]]
  (vec (mapcat (fn [[pat seed]]
                 (d/bindings pat seed (or options {})))
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

(g/generic+ d/bindings
            ([x seed options]

             :sym
             (let [{:keys [name mode]}
                   (sym_parse x options)]
               [name (sym_form seed mode)])

             :vec
             (if (c/single-dotted? x)
               (vec_composite-bindings x seed options)
               (vec_raw-bindings x seed options))

             :map
             (if (c/single-dotted? x)
               (map_composite-bindings x seed options)
               (map_raw-bindings x seed options))

             :lst
             (let [[v & args] x]
               (cs [k (and (symbol? v) (keyword v))
                    op (get @operators k)]
                   (op args seed options)
                   ((::default @operators) (cons v args) seed options)))))



(comment
  (d/bindings '[a b . c] 'x {})
  (d/bindings '[a b c] 'x {})
  (d/bindings '[a b . c] 'x {})
  (d/bindings '[a b . c d] 'x {})
  (d/bindings '{:a a :b bibi} 'x {})
  (d/bindings '{:a a :b bibi . r} 'x {})
  (d/bindings 'a 'x)
  (d/bindings '?a 'x {})
  (d/bindings '!a 'x {})
  (d/bindings '¡a 'x {:binding-mode :strict})
  (d/bindings '¡a 'x {})
  (d/bindings '(& a b) 'x)
  (d/bindings '(pos? a) 'x)
  )
