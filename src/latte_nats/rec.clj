(ns latte-integers.rec
  "The recursion theorem for natural numbers."

  (:refer-clojure :exclude [and or not int =])

  (:require [latte.core :as latte :refer [defaxiom defthm definition
                                          deflemma
                                          lambda forall proof assume have
                                          pose try-proof qed]]

            [latte-prelude.prop :as p :refer [and]]
            [latte-nats.core :as nats :refer [nat zero succ =]]
            [latte-prelude.equal :as eq :refer [equal]]
            [latte-prelude.quant :as q]
            ))


(definition nat-recur-prop
  "The property of the recursion principle for natural numbers."
  [[?T :type] [x T] [f (==> T T)]]
  (lambda [g (==> nat T)]
    (and (equal (g zero) x)
         (forall [n nat]
           (equal (g (succ n)) (f (g n)))))))

(defthm nat-recur
  "The recursion principle for natural numbers.
cf. [[nat-recur-prop]]."
  [[?T :type] [x T] [f (==> T T)]]
  (q/unique (nat-recur-prop x f)))


(defthm nat-recur-ex
  [[?T :type] [x T] [f (==> T T)]]
  (q/ex (nat-recur-prop x f)))


