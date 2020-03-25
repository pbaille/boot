(ns floor.compiler.lambda
  (:refer-clojure :exclude [compile])
  (:require [boot.prelude :as p]
            [floor.compiler.composite :as compo]))

(defn bodify [body]
  (condp = (count body)
     0 ::void
     1 (first body)
     (list* 'do body)))

(defn parse-case [[pat & body]]
  (let [arity
        (when (not (compo/dotted? pat))
          (count pat))

        [pat-prefix rest-pat]
        (split-with (complement '#{. ..}) pat)

        rest-pat
        (if (= 2 (count rest-pat))
          (second rest-pat) (vec rest-pat))]

    (merge
      {:pat pat
       :body (bodify body)}
      (if arity
        {:arity arity}
        {:variadic true
         :pat-prefix (vec pat-prefix)
         :rest-pat rest-pat
         :min-arity (count pat-prefix)}))))

(defn check-variadic-sigs [xs]
  (assert (apply = (map :min-arity xs))
          (apply str "variadic arities count mismatch\n"
                 (interleave (map :pat xs) (repeat "\n")))))

(defn parse [[fst & nxt :as form]]
  (let [[name fst & nxt]
        (if (symbol? fst)
          (cons fst nxt)
          (concat [nil fst] nxt))

        [doc & cases]
        (if (string? fst)
          (cons fst nxt)
          (concat ["no doc" fst] nxt))

        cases
        (if (every? seq? cases)
          cases
          (partition 2 2 nil cases))

        ;_ (println cases)

        parsed-cases
        (map parse-case cases)

        variadic-cases (seq (filter :variadic parsed-cases))
        variadic (boolean variadic-cases)
        monadic (and (not variadic) (apply = (map (comp count first) cases)))
        polyadic (not monadic)

        arities
        (reduce
          (fn [r {:keys [arity min-arity] :as c}]
            (if arity
              (update r arity (fnil conj []) c)
              (update r :& (fnil conj []) c)))
          {} parsed-cases)]


    (when variadic
      (check-variadic-sigs (:& arities)))

    {:doc doc
     :name name
     :monadic monadic
     :variadic variadic
     :polyadic polyadic
     :arity-map arities
     :cases cases}))

(defn compile-arity [verb [n cases]]
  (if (number? n)
    ;; fixed arity
    (let [argv (vec (take n (p/gensyms)))
          cases
          (mapcat
            (fn [{:keys [pat body]}]
              [(vec (interleave pat argv)) body])
            cases)]
      (list argv (list* verb cases)))
    ;; variadic arity
    (let [vsym (gensym)
          prefcnt (:min-arity (first cases))
          argv-prefix (take prefcnt (p/gensyms))
          argv (p/catv argv-prefix ['& vsym])
          cases
          (mapcat
            (fn [{:keys [pat-prefix rest-pat body]}]
              [(p/catv (interleave pat-prefix argv-prefix) [rest-pat vsym])
               body])
            cases)]
      (list argv (list* verb cases)))))

(defn compile [verb {:as parsed :keys [arity-map name]}]
  `(fn ~@(when name [name])
     ~@(map (partial compile-arity verb) arity-map)))

(defn wrap-generic-body [body]
  (let [{:as parsed :keys [arity-map name]} (parse body)]
    (cons name (map (partial compile-arity 'floor.core/cs) arity-map))))