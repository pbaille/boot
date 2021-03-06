(ns floor.compiler.bindings
  (:require [boot.named :as n]
            [boot.prelude :as p :refer [cs]]
            [boot.generics :as g]
            [floor.compiler.composite :as compo]
            [floor.compiler.env :as env]))

(g/generic bindings
           ([x options])
           ([x y options] [x y]))

(do :vec

    (defn raw-vec [v seed options]
      (let [cnt (count v)
            symseed? (symbol? seed)]
        (p/with-gensyms
          [vect head tail linecheck size>= size=]
          (let [vect (if symseed? seed vect)]
            (p/catv
              (when-not symseed? (bindings [vect seed] options))
              (bindings
                [linecheck `(sequential? ~vect)
                 head `(floor.core/take ~vect ~cnt)
                 size>= `(floor.core/eq (count ~head) ~cnt)
                 tail `(floor.core/drop ~vect ~cnt)
                 size= `(floor.core/pure? ~tail)]
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
              (when-not symseed? (bindings [ysym seed] options))
              (raw-vec cars `(floor.core/take ~ysym ~doti) options)
              (bindings eli `(floor.core/drop ~ysym ~doti) options)
              #_(bind.vec.body cars ysym doti)
              (when-not (zero? qcnt)
                (p/catv
                  (bindings [cdr' eli
                             eli `(floor.core/dropend ~cdr' ~qcnt)
                             qsym `(floor.core/takend ~cdr' ~qcnt)] options)
                  (raw-vec queue qsym options)))))))))

(do :map

    (defn map-keys [x seed options]
      (mapcat
        (fn [[k v]]
          (bindings v `(get ~seed ~k) options))
        x))


    (defn raw-map [x seed options]
      (p/with-gensyms
        [mapcheck seedsym]
        (p/catv
          (bindings
            [seedsym seed
             mapcheck `(map? ~seedsym)]
            options)
          (map-keys x seedsym options))))

    (defn composite-map [x seed options]
      (let [rs (get x '.)
            m (dissoc x '.)
            ks (keys m)]
        (p/with-gensyms
          [seedsym]
          (p/catv
            (bindings [seedsym seed] options)
            (map-keys m seedsym options)
            (bindings rs `(dissoc ~seedsym ~@ks) options))))))

(do :sym

    (defn symbol-mode [s default]
      (let [default (or default :short)]
        (condp = (first (name s))
          \¡ default
          \? :opt
          \! :strict
          \_ :short
          default)))

    (defn parse-symbol [x & [options]]
      (let [name (name x)
            prefix (#{\? \! \¡ \_} (first name))]
        {:prefix prefix
         :name (if prefix (n/sym (or (next name) (gensym))) x)
         :mode (symbol-mode x (:binding-mode options))}))

    (defn symbol-form [seed mode]
      (condp = mode
        :short seed
        :opt `(floor.core/or ~seed nil)
        :strict `(floor.core/or ~seed (p/error "strict binding failure:\n" (:data ~seed)))))

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
                (bindings [seedsym seed] options)
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
         (bindings [seedsym seed
                    a `(floor.core/car ~seedsym)
                    b `(floor.core/cdr ~seedsym)] options)))

     :quote
     (fn [[a] seed options]
       (bindings (gensym "¡") `(floor.core/eq ~seed '~a) options))

     :bind_
     (fn [[p expr] seed options]
       (bindings ['_ seed p expr] options))

     :!
     (fn [[f & [p]] seed options]
       (bindings (or p (gensym)) (list f seed) options))

     ::default
     (fn [[verb pat & args] seed options]
       (p/with-gensyms
         [seedsym typecheck]
         (if (keyword? verb)
           (bindings [seedsym seed
                      typecheck `(floor.core/eq (floor.core/type ~seedsym) ~verb)
                      pat seedsym]
                     options)
           (bindings pat (list* verb seed args) options))))}))

(do :compilation

    (defn unified
      "takes a binding vector (like let) , compile it with 'bindings
       then add unification constraints on symbols that occurs multiple times"
      [xs & [options]]
      (loop [ret [] seen #{}
             [a b & nxt] (bindings xs options)]
        (if a
          (if (seen a)
            (recur (p/catv ret (bindings (gensym) `(floor.core/eq ~a ~b) options)) seen nxt)
            (recur (conj ret a b) (conj seen a) nxt))
          ret)))

    (defn optimize
      ([{:as ret :keys [todo bindings env]}]
       (if (not (seq todo))
         ret
         (optimize
           (let [[sym expr & todo] todo]
             (if (and (symbol? expr)
                      (not (contains? (set (take-nth 2 todo)) expr)))
               {:bindings bindings :env (assoc-in env [(p/ns-sym) sym] {:substitute expr}) :todo todo}
               {:bindings (p/catv bindings [sym (env/expand env expr)]) :env (env/env-shadow env sym) :todo todo})))))
      ([env bs]
       (optimize {:todo bs :env env :bindings []})))

    (defn compile-let-form
      ([{:keys [env return options] bs :bindings}]
       (let [bs (bindings bs options)
             bs (if (:unified options) (unified bs options) bs)
             {:keys [env bindings]} (optimize env bs)
             return (env/expand env return)]
         (if-not (seq bindings)
           return
           (loop [return return
                  [[p1 e1] & pes :as bs]
                  (reverse (partition 2 bindings))]
             (if-not (seq bs)
               return
               (let [mode (:mode (meta p1))]
                 (recur (condp = mode
                          :opt
                          (if (= p1 return) e1 `(let [~p1 ~e1] ~return))

                          :strict
                          `(let [~p1 ~e1]
                             (if (floor.core/success? ~p1)
                               ~return
                               (p/error "strict binding failure:\n" (:data ~p1))))

                          :short
                          (if (= p1 return) e1
                            `(let [~p1 ~e1]
                               (if (floor.core/success? ~p1)
                                 ~return
                                 ~p1))))
                        pes)))))))

      ([env bindings return options]
       (compile-let-form
         {:env env :bindings bindings
          :return return :options options}))))

(g/generic+ bindings

            ([xs options]
             :vec
             (vec (mapcat (fn [[pat seed]]
                            (bindings pat seed options))
                          (partition 2 xs)))
             :map
             (p/error "parallel bindings: not yet implemented"))

            ([x seed options]

             :sym
             (let [{:keys [name mode]}
                   (parse-symbol x options)]
               [(with-meta name {:mode mode})
                seed #_(symbol-form seed mode)])

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

#_(compile-let-form {}
                  '[a 1 b 2]
                  '(+ a b)
                  {:binding-mode :strict})