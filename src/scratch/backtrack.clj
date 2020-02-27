(ns scratch.backtrack
  (:require [boot.prelude]
            [clojure.core :as c]))

;; experimantal WIP

(boot.prelude/use!)

(defonce state
  (atom {:at []
         :tree []}))

(defn next-position [s]
  (when (seq (:at s))
    (let [parent-path (vec (butlast (:at s)))
          at-next (conj parent-path (inc (last (:at s))))]
      (if (get-in (:tree s)
                  at-next)
        (assoc s :at at-next)
        (next-position (assoc s :at parent-path))))))

(next-position
 {:at [1 2]
  :tree
  [:iop
   [:a :b :c]
   [:d [:e :f]]]})

(next-position
 {:at [2 1 0]
  :tree
  [:iop
   [:a :b :c]
   [:d [:e :f]]]})

(def end (fn [] nil))

(require '[scratch.nsub :refer [defmac+]])

(c/defn parse-fn' [[fst & nxt :as all]]

  (let [[name fst & nxt]
        (if (symbol? fst)
          (cons fst nxt)
          (concat [nil fst] nxt))

        [doc fst & nxt]
        (if (string? fst)
          (cons fst nxt)
          (concat ["" fst] nxt))

        [opts fst & nxt]
        (if (map? fst)
          (cons fst nxt)
          (concat [{} fst] nxt))

        impls
        (if (vector? fst)
          {fst (vec nxt)}
          (into {}
                (map
                 (c/fn [[args & body]]
                   [args (vec body)])
                 (cons fst nxt))))]

    {:meta opts
     :name name
     :doc doc
     :impls impls
     :cases (mapv (p* list*) impls)}))

(defmac+ defn
  [cases doc name meta]
  `(c/defn ~name ~doc ~meta
     ~@(map (fn [[bindings & body]]
              `(~bindings
                (when (and ~@(shadows bindings))
                  ~@body)))
            cases))
  [& xs]
  (prob (parse-fn' xs)))

(comment
  :scratch
  (parse-fn '(iop "iop" {:me :ta} ([x] x) ([x y] y)))

  (defn add "zer" {:a 1} [a b] (println "adding" a b) (+ a b))

  (add 1 nil)

  (for [x '[c/map]]
    `(def ~(sym (name x))
       (fn [& xs#] (when (every? identity xs#) (apply ~(resolve x) xs#)))))

  (meta #'c/map)

  (defmacro core-import [x]
    (let [v (resolve x)
          pats (:arglists (meta v))]
      (println v pats)
      (pprob `(c/defn ~(sym (name x))
                ~@(c/map (fn [p]
                           `(~p (when (and ~@(shadows p))
                                  (~(symbol "clojure.core" (name x)) ~@p))))
                         pats)))))

  (mx' (core-import c/map)))

(defn wrap-fn [f]
  (fn [& xs]
    (when (every? identity xs)
      (apply f xs))))

(def map (wrap-fn c/map))

(map inc '(1 2 3))
