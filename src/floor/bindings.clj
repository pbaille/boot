(ns floor.bindings
  (:require [floor.declaration :as d :refer [bindings]]
            [floor.composite :as c]
            [floor.control :as ctl]
            [boot.named :as n]
            [boot.generics :as g]
            [boot.prelude :as p :refer [cs]]
            [boot.types :as t]))





(do :vec

    (defn bindings_raw-vec [v seed options]
      (let [cnt (count v)
            symseed? (symbol? seed)]
        (with-gensyms
          [vect _head _tail ¡linecheck ¡size>= ¡size=]
          (let [vect (if symseed? seed vect)]
            (p/catv
              (when-not symseed? [vect seed])
              (bindings ¡linecheck `(line? ~vect) options)
              [_head `(take ~vect ~cnt)]
              (bindings ¡size>= `(= (count ~_head) ~cnt) options)
              [_tail `(drop ~vec ~cnt)]
              (bindings ¡size= `(not (seq ~_tail)) options)
              (mapcat
                (fn [e i] (bindings e `(nth ~_head ~i (failure {:index-not-found ~i})) options))
                (seq v) (range)))))))

    (defn bindings_composite-vec [v seed options]
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
              (bindings_raw-vec cars `(take ~doti ~ysym) options)
              (bindings eli `(drop ~doti ~ysym) options)
              #_(bind.vec.body cars ysym doti)
              (when-not (zero? qcnt)
                (p/catv
                  [cdr' eli]
                  (bindings eli `(drop-last ~qcnt ~cdr') options)
                  [qsym `(take-last ~qcnt ~cdr')]
                  (bindings_raw-vec queue qsym options)))))))))

(do :map

    (defn bindings_map-keys [x seed options]
      (mapcat
        (fn [[k v]]
          (bindings v `(get ~seed ~k) options))
        x))


    (defn bindings_raw-map [x seed options]
      (with-gensyms
        [¡mapcheck ¡seed]
        (p/catv
          [¡seed seed
           ¡mapcheck `(map? ~¡seed)]
          (bindings_map-keys x ¡seed options))))

    (defn bindings_composite-map [x seed options]
      (let [rs (get x '.)
            m (dissoc x '.)
            ks (keys m)]
        (with-gensyms
          [¡seed]
          (p/catv
            [¡seed seed]
            (bindings_map-keys m ¡seed options)
            (bindings rs `(dissoc ~¡seed ~@ks) options))))))

(do :sym

    (defn bindings_symbol-mode [s default]
      (let [default (or default :short)]
        (condp = (first (name s))
          \¡ default
          \? :opt
          \! :strict
          \_ :short
          default)))

    (defn bindings_parse-symbol [x options]
      (let [name (name x)
            prefix (#{\? \! \¡ \_} (first name))]
        {:prefix prefix
         :name (if prefix (n/sym (next name)) x)
         :mode (bindings_symbol-mode x (:binding-mode options))}))

    (defn bindings_symbol-form [seed mode]
      (condp = mode
        :short seed
        :opt `(ctl/or ~seed nil)
        :strict `(or ~seed (ex-info "binding" {:failure (fail ~seed)}))))

    )

(def bindings_operators
  (atom
    {:&
     (fn [xs seed options]
       (with-gensyms
         [seedsym]
         (apply p/catv
                [seedsym seed]
                (map #(bindings % seedsym options) xs))))

     :ks
     (fn [xs seed options]
       (bindings (zipmap (map (comp keyword :name bindings_parse-symbol) xs) xs)
                   seed options))

     :ks-req
     (fn [xs seed options]
       (bindings (zipmap (map keyword xs) xs) seed options))

     :ks-opt
     (fn [xs seed options]
       (let [keys (map keyword xs)
             opt-syms (map (partial p/sym "?") xs)]
         (bindings (zipmap keys opt-syms) seed options)))

     :ks-or
     (fn [xs seed options]
       (let [keys (take-nth 2 xs)
             or-exprs (map (fn [[k v]] `(or ~k ~v)) (partition 2 xs))]
         (p/catv
           ((get @bindings_operators :ks-opt) keys seed options)
           (interleave keys or-exprs))))

     :cons
     (fn [[a b] seed options]
       (with-gensyms
         [seedsym]
         (p/catv
           [seedsym seed]
           (bindings a `(first ~seedsym) options)
           (bindings b `(next ~seedsym) options))))

     :quote
     (fn [[a] seed options]
       (bindings (gensym "¡") `(= ~seed '~a) options))

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

(defn bindings_compile-binding-vector [xs & [options]]
  (vec (mapcat (fn [[pat seed]]
                 (bindings pat seed (or options {})))
               (partition 2 xs))))

(defn bindings_unified
  "takes a binding vector (like let) , compile it with 'bindings
   then add unification constraints on symbols that occurs multiple times"
  [xs]
  (loop [ret [] seen #{}
         [a b & nxt] (bindings_compile-binding-vector xs)]
    (if a
      (if (seen a)
        (recur (conj ret (gensym) `(= ~a ~b)) seen nxt)
        (recur (conj ret a b) (conj seen a) nxt))
      ret)))

(generic bindings
         ([x]
          )

         ([x y] (bindings x y {}))

         ([x seed options]

          :sym
          (let [{:keys [name mode]}
                (bindings_parse-symbol x options)]
            [name (bindings_symbol-form seed mode)])

          :vec
          (if (c/single-dotted? x)
            (bindings_composite-vec x seed options)
            (bindings_raw-vec x seed options))

          :map
          (if (c/single-dotted? x)
            (bindings_composite-map x seed options)
            (bindings_raw-map x seed options))

          :lst
          (let [[v & args] x]
            (cs [k (and (symbol? v) (keyword v))
                 op (get @bindings_operators k)]
                (op args seed options)
                ((::default @bindings_operators) (cons v args) seed options)))))



(comment
  (bindings '[a b . c] 'x {})
  (bindings '[a b c] 'x {})
  (bindings '[a b . c] 'x {})
  (bindings '[a b . c d] 'x {})
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
