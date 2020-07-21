(ns meander.match.ir.epmacro) 
(defmacro defop [symbol op params & body]
  (let [symbol (vary-meta symbol assoc
                          :arglists `'(~params)
                          :style/indent :defn)]
    `(defn ~symbol ~params
       ~(if (seq body)
          `(assoc (do ~@body) :op ~op)
          `(hash-map :op ~op
                     ~@(mapcat
                        (fn [param]
                          (when (not= 'op param)
                            [(keyword (name param)) param]))
                        params))))))
