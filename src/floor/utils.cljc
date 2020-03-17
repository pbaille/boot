(ns floor.utils
  (:require [boot.prelude :as p]))

(p/use!)

(letfn [(expansion-size [] 5)

        (ellipsis? [x] (= '... x))

        (set-expr [xs]
          (cons `hash-set
                (sort-by ellipsis? xs)))

        (replace-ellipsis [expr args applied?]
          (let [k #(replace-ellipsis % args applied?)]
            (cp expr
                map? ($vals expr k)
                set? (k (set-expr expr))
                vec?
                (cs (ellipsis? (last expr))
                    (k (cons `vector expr))
                    ($ expr k))
                seq?
                (map k
                       (cs (ellipsis? (last expr))
                           (cs applied?
                               (cons `apply (concat (butlast expr) args))
                               (concat (butlast expr) args))
                           expr))
                expr)))

        (cases [[argv expr]]
          (let [argsyms (take (expansion-size) (gensyms))
                vsym (gensym)]
            (concat
              ($ (range (inc (expansion-size)))
                 (fn [x]
                   (let [args (take x argsyms)]
                     (list (catv argv args)
                           (replace-ellipsis expr args false)))))
              [(list (catv argv argsyms ['& vsym])
                     (replace-ellipsis
                       expr (conj (vec argsyms) vsym) true))])))]

  (defmacro fn&
    "the idea is to be able to declare concisely variadic functions, while mitigating the performance cost
      exemple:
      (fn& [a b] (add a b ...))
      a and b are mandatory arguments, the minimum arity is therefore 2
      but if we feed it more arguments, they will take place where the ... appears in the code.
      ... (which we call ellipsis) can appears several times in the function body.

      with fn&.expansion-size set to 3, the compiled function looks roughly like this
      (fn
       ([a b] (add a b))
       ([a b G__1] (add a b G__1))
       ([a b G__1 G__2] (add a b G__1 G__2))
       ([a b G__1 G__2 G__3] (add a b G__1 G__2 G__3))
       ([a b G__1 G__2 G__3 & G__4]
        (apply add a b G__1 G__2 G__3 G__4)))

      it would be absolutly painful to write such things by hand, and we gain performance on arity 1..5, and use apply only for larger ones
      this should looks like a minimal gain, because apply is quite permormant, but for core functions this gain is valuable"
    [& body]
    (list* `fn (cases body)))

  (is (macroexpand '(fn& [a b] (add a b ...))))

  )



