(ns floor.compiler
  (:require [boot.prelude :as p]
            [floor.composite :as compo]
            [boot.generics :as g :refer [generic]]
            [boot.named :as n]
            [floor.lambda :as lambda]))

(p/use!)

(do :env
    ;; hold compile time implementations
    (def global-env (atom {}))

    (declare expand)

    (def mobject0
      {:expand (fn [env form] ($ form (p expand env)))
       :parse (fn [env form] form)})

    (defn mobject
      ([x]
       (cp x
           fn? (mobject {:expand x})
           holymap? (merge mobject0 x)))
      ([parse expand & more]
       (merge {:expand expand :parse parse} more)))

    (defmacro expander [bindings & body]
      `(mobject {:expand (fn ~bindings ~@body)}))

    (defn env-shadow [e x]
      (if (sequential? x)
        (reduce env-shadow e x)
        (let [{:keys [ns name]} (parse-symbol x)]
          (assoc-in e [ns name] mobject0))))

    (defn env-get [e sym]
      (cs
        [{:keys [ns name]} (parse-symbol sym)
         found (get-in e [ns name])]
        (merge mobject0 found)
        ;; is symbol try to find metas
        (when (symbol? sym)
          (some-> sym resolve meta mobject)))))

(do :expand

    (defn expand-seq
      [env form]
      (if-let [mobj (env-get env (first form))]
        ((:expand mobj) env ((:parse mobj) env (rest form)))
        ($ form (p expand env))))

    (defn expand-sym
      [env sym]
      (let [{:keys [substitute]}
            (env-get env sym)]
        (if substitute
          (expand-sym env substitute)
          sym)))

    (defn expand [env form]
      (compo/expand
        (cp form
            seq? (expand-seq env form)
            holycoll? ($ form (p expand env))
            symbol? (expand-sym env form)
            form)))

    (defmacro def+ [name val metas]
      `(alter-meta!
         (def ~name ~val)
         (fn [m#] (merge m# ~metas))))

    (def+ mvar (fn [y z] z)
          {:expand (fn [_ _] :pouet)})

    (do :assertions

        (is (expand {'floor.compiler {'rev (expander [env form] (reverse ($ form (p expand env))))}}
                    '(rev 1 (mvar 2 4) [3 . xs] +)
                    )
            '(+ (clojure.core/vec (clojure.core/concat [3] xs)) :pouet 1))))

(do :bindings

    (generic bindings
             ([x options])
             ([x y options] [x y]))

    (do :vec

        (defn bindings_raw-vec [v seed options]
          (let [cnt (count v)
                symseed? (symbol? seed)]
            (with-gensyms
              [vect head tail ¡linecheck ¡size>= ¡size=]
              (let [vect (if symseed? seed vect)]
                (catv
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

        (defn bindings_composite-vec [v seed options]
          (let [doti (indexof v '.)
                cars (take doti v)
                [eli & queue] (drop (inc doti) v)
                qcnt (count queue)
                symseed? (symbol? seed)]
            (with-gensyms
              [ysym qsym cdr']
              (let [ysym (if symseed? seed ysym)]
                (catv
                  (when-not symseed? [ysym seed])
                  (bindings_raw-vec cars `(floor.core/take ~ysym ~doti) options)
                  (bindings eli `(floor.core/drop ~ysym ~doti) options)
                  #_(bind.vec.body cars ysym doti)
                  (when-not (zero? qcnt)
                    (catv
                      [cdr' eli]
                      (bindings eli `(floor.core/dropend ~cdr' ~qcnt) options)
                      [qsym `(floor.core/takend ~cdr' ~qcnt)]
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
            (catv
              [¡seed seed
               ¡mapcheck `(map? ~¡seed)]
              (bindings_map-keys x ¡seed options))))

        (defn bindings_composite-map [x seed options]
          (let [rs (get x '.)
                m (dissoc x '.)
                ks (keys m)]
            (with-gensyms
              [¡seed]
              (catv
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
             :name (if prefix (n/sym (or (next name) (gensym))) x)
             :mode (bindings_symbol-mode x (:binding-mode options))}))

        (defn bindings_symbol-form [seed mode]
          (condp = mode
            :short seed
            :opt `(floor.core/or ~seed nil)
            :strict `(floor.core/or ~seed (p/error "strict binding failure:\n" (floor.core/fail ~seed)))))

        (comment
          (bindings '!a 'x {}))

        )

    (def bindings_operators
      (atom
        {:&
         (fn [xs seed options]
           (with-gensyms
             [seedsym]
             (apply catv
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
                 opt-syms (map (partial sym "?") xs)]
             (bindings (zipmap keys opt-syms) seed options)))

         :ks-or
         (fn [xs seed options]
           (let [keys (take-nth 2 xs)
                 or-exprs (map (fn [[k v]] `(or ~k ~v)) (partition 2 xs))]
             (catv
               ((get @bindings_operators :ks-opt) keys seed options)
               (interleave keys or-exprs))))

         :cons
         (fn [[a b] seed options]
           (with-gensyms
             [seedsym]
             (catv
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

    (defn bindings_optimize [env bs]
      (reduce
        (fn [{:keys [bindings env]} [sym expr]]
          (if (symbol? expr)
            {:bindings bindings :env (assoc-in env [(ns-sym) sym] {:substitute expr})}
            {:bindings (p/catv bindings [sym (expand env expr)]) :env env}))
        {:env env :bindings []}
        (partition 2 bs)))

    #_(bindings_optimize {} '[a b c a])

    (g/generic+ bindings

                ([xs options]
                 :vec
                 (vec (mapcat (fn [[pat seed]]
                                (bindings pat seed options))
                              (partition 2 xs))))

                ([x seed options]

                 :sym
                 (let [{:keys [name mode]}
                       (bindings_parse-symbol x options)]
                   [name (bindings_symbol-form seed mode)])

                 :vec
                 (if (compo/single-dotted? x)
                   (bindings_composite-vec x seed options)
                   (bindings_raw-vec x seed options))

                 :map
                 (if (compo/single-dotted? x)
                   (bindings_composite-map x seed options)
                   (bindings_raw-map x seed options))

                 :lst
                 (let [[v & args] x]
                   (cs [k (and (symbol? v) (keyword v))
                        op (get @bindings_operators k)]
                       (op args seed options)
                       ((::default @bindings_operators) (cons v args) seed options)))
                 :any
                 (bindings (gensym) `(floor.core/eq ~x ~seed) options))))

(do :macros

    (defn IF_form
      ([test then]
       (if (symbol? test)
         `(if (floor.core/success? ~test) ~then ~test)
         `(let [t# ~test]
            (if (floor.core/success? t#) ~then t#))))
      ([test then else]
       (if else
         `(if (floor.core/success? ~test) ~then ~else)
         (IF_form test then)))
      ([test then test2 then2 & others]
       (IF_form test then (apply IF_form test2 then2 others))))

    (defn IF-expand [env args]
      (apply IF_form (map (partial expand env) args)))

    (defn CS_compile-case [env bs expr options]
      (let [bs (bindings bs options)
            bs (if (:unified options) (bindings_unified bs) bs)
            {:keys [env bindings]} (bindings_optimize env bs)
            expr (expand env expr)]
        (if-not (seq bindings)
          expr
          (loop [ret expr
                 [[p1 e1] & pes :as bs]
                 (reverse (partition 2 bindings))]
            (if-not (seq bs)
              ret
              (recur `(let [~p1 ~e1] (if (floor.core/success? ~p1) ~ret ~p1))
                     pes))))))

    (defn CS_mk [options]
      {:expand
       (fn CS_expand
         [env [b1 e1 & more :as args]]
         (let [exp (p expand env)]
           (condp = (count args)
             0 nil
             1 (exp b1) #_(CS_wrap-return (exp b1) options)
             2 (cond
                 (not (vector? b1)) (IF-expand env [b1 e1])
                 :else (CS_compile-case env b1 e1 options))
             ;else
             `(let [a# ~(CS_expand env [b1 e1])]
                (if (floor.core/success? a#)
                  a# ~(CS_expand env more))))))})

    (defn LAMBDA_mk [binding-form]
      {:expand (fn [env xs] (expand env (lambda/compile binding-form (lambda/parse xs))))})

    (defn CASE_expand [{:keys [binding-form seed cases]}]
      (let [patterns (take-nth 2 cases)
            exprs (take-nth 2 (next cases))
            seed-sym (gensym "seed_")]
        `(let [~seed-sym ~seed]
           (~binding-form
             ~@(interleave (map (fn [p] [p seed-sym]) patterns)
                           exprs)))))

    (defn CASE_mk [binding-form]
      {:expand
       (fn [env [seed & cases]]
         (expand env (CASE_expand {:cases cases :seed seed :binding-form binding-form})))})

    (defmacro casu [seed & cases]
      (CASE_expand {:cases cases :seed seed :binding-form `csu}))

    (swap! global-env
           update
           'floor.core
           merge
           {'cs   (CS_mk {})
            'csu  (CS_mk {:unified true})
            '?cs  (CS_mk {:binding-mode :opt})
            '!cs  (CS_mk {:binding-mode :strict})
            '?csu (CS_mk {:binding-mode :opt :unified true})
            '!csu (CS_mk {:binding-mode :strict :unified true})

            'f    (LAMBDA_mk 'floor.core/cs)
            'fu   (LAMBDA_mk 'floor.core/csu)
            '!f   (LAMBDA_mk 'floor.core/!cs)
            '!fu  (LAMBDA_mk 'floor.core/!csu)
            '?f   (LAMBDA_mk 'floor.core/?cs)
            '?fu  (LAMBDA_mk 'floor.core/?csu)

            'case (CASE_mk 'floor.core/cs)
            'casu (CASE_mk 'floor.core/csu)})

    (expand @global-env
            '(floor.core/cs [[a b] x] :a [1 x] :b)))