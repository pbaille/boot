(ns floor.bindings
  (:require [floor.declaration :as d :refer [bindings]]
            [floor.composite :as c]
            [boot.named :as n]
            [boot.generics :as g]
            [boot.prelude :as p]))

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
     (fn [xs y options]
       (with-gensyms
         [seed]
         (apply p/catv
                [seed y]
                (map #(d/bindings % seed options) xs))))

     :ks
     (fn [xs seed options]
       (d/bindings (zipmap (map keyword xs) xs) seed options))

     :ks-opt
     (fn [xs seed options]
       (let [keys (map keyword xs)
             opt-syms (map (partial p/sym "_") xs)]
         (d/bindings (zipmap keys opt-syms) seed options)))

     :ks-or
     (fn [xs seed options]
       (let [keys (take-nth 2 xs)
             or-exprs (map (fn [[k v]] `(or ~k ~v)) (partition 2 xs))]
         (p/catv
           ((get @operators :ks-opt) keys seed options)
           (interleave keys or-exprs))))

     :cons
     (fn [[a b] y options]
       (with-gensyms
         [seed]
         (+ [seed y]
            (d/bindings a `(first ~seed) options)
            (d/bindings b `(next ~seed) options))))

     :quote
     (fn [[a] y options]
       (d/bindings (gensym "¡") `(= ~y '~a) options))

     #_:tup
     #_(fn [xs y]
         (let [xs (vec* xs)
               [ysym] (gensyms)]
           (+
             [ysym y
              (gensym "?!line") (qq (line? ~ysym))
              (gensym "?!countable") (qq (c/counted? ~ysym))
              (gensym "?!countcheck") (qq (= ~(count xs) (count ~ysym)))]
             (bind.vec.body xs ysym))))

     :bind_
     (fn [[p expr] y options]
       (p/catv
         ['_ y]
         (d/bindings p expr options)))

     :!
     (fn [[f & [p]] y]
       (d/bindings (or p (gensym)) (list f y)))}))

(g/generic+ d/bindings
            [x seed options]

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

            :seq
            (let [[v & args] x]
              (p/cs [k (and (symbol? v) (keyword v))
                     op (get @operators k)]
                    (op args y options)
                    ((get @operators 'default) (cons v args) y options))))



(comment
  (d/bindings '[a b . c] 'x {})
  (bindings '[a b c] 'x {})
  (d/bindings '[a b . c] 'x {})
  (d/bindings '[a b . c d] 'x {})
  (d/bindings '{:a a :b bibi} 'x {})
  (d/bindings '{:a a :b bibi . r} 'x {})
  (d/bindings 'a 'x)
  (d/bindings '?a 'x {})
  (d/bindings '!a 'x {})
  (d/bindings '¡a 'x {:binding-mode :strict})
  (d/bindings '¡a 'x {})
  )
