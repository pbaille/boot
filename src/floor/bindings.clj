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

    (defn vec_body-bindings [x y cnt options]
      (let [headsym (gensym "head_")
            tailsym (gensym "tail_")]
        (p/catv
          [headsym `(take ~cnt ~y)]
          (d/bindings (gensym "¡size>=") `(= (count ~headsym) ~cnt) options)
          [tailsym `(drop ~cnt ~y)]
          (d/bindings (gensym "¡size=") `(not (seq ~tailsym)) options)
          (mapcat
            (fn [v i] (d/bindings v `(nth ~headsym ~i (d/failure {:index-not-found ~i})) options))
            (seq x) (range)))))

    (defn vec_body-bindings' [headsym tailsym cnt options]
      (p/catv
        [headsym `(take ~cnt ~y)]
        (d/bindings (gensym "¡size>=") `(= (count ~headsym) ~cnt) options)
        [tailsym `(drop ~cnt ~y)]
        (d/bindings (gensym "¡size=") `(not (seq ~tailsym)) options)
        (mapcat
          (fn [v i] (d/bindings v `(nth ~headsym ~i (d/failure {:index-not-found ~i})) options))
          (seq x) (range))))

    (defn vec_size-check
      ([sym cnt options]
       (let [headsym (gensym "head_")
             tailsym (gensym "tail_")]
         (p/catv [headsym `(take ~cnt ~sym)]
                 (d/bindings (gensym "¡size>=") `(= (count ~headsym) ~cnt) options)
                 [tailsym `(drop ~cnt ~sym)]
                 (d/bindings (gensym "¡size=") `(not (seq ~tailsym)) options))))
      ([headsym tailsym cnt options]
       (p/catv (d/bindings (gensym "¡size>=") `(= (count ~headsym) ~cnt) options)
               (d/bindings (gensym "¡size=") `(not (seq ~tailsym)) options))))

    (defn vec_raw-bindings [v seed options]
      (let [cnt (count v)]
        (with-gensyms
          [vect _head _tail ¡linecheck]
          (p/catv
            [vect seed]
            (d/bindings ¡linecheck `(line? ~vect) options)
            [_head `(take ~cnt ~vect)
             _tail `(drop ~cnt ~vect)]
            (vec_size-check _head _tail cnt options)))))

    (defn vec_composite-bindings [v seed options]
      (let [doti (p/indexof v '.)
            cars (take doti v)
            [eli & queue] (drop (inc doti) v)
            qcnt (count queue)
            [ysym qsym cdr' cars'] (repeatedly gensym)]
        (println "io")
        (p/catv
          [ysym seed]
          (d/bindings (gensym "¡linecheck") `(line? ~ysym) options)
          (vec_body-bindings cars `(take ~doti ~ysym) doti options)
          (d/bindings eli `(drop ~doti ~ysym) options)
          #_(bind.vec.body cars ysym doti)
          (when-not (zero? qcnt)
            (p/catv
              [cdr' eli]
              (d/bindings eli `(drop-last ~qcnt ~cdr') options)
              [qsym `(take-last ~qcnt ~cdr')]
              (vec_body-bindings queue qsym qcnt options)))))))

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

(g/generic+ d/bindings
            [x seed options]

            :sym
            (let [{:keys [name mode]}
                  (sym_parse x options)]
              [name (sym_form seed mode)])

            :vec
            (if (c/single-dotted? x)
              (vec_composite-bindings x seed options)
              (vec_raw-bindings x seed options)))

(d/bindings '[a b . c] 'x {})

(comment
  (bindings '[a b c] 'x {})
  (d/bindings '[a b . c] 'x {})
  (d/bindings 'a 'x)
  (d/bindings '?a 'x {})
  (d/bindings '!a 'x {})
  (d/bindings '¡a 'x {:binding-mode :strict})
  (d/bindings '¡a 'x {})
  )
