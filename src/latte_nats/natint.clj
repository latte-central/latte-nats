(ns latte-nats.natint
  "Connection between ℕ as a type (this development)
 and ℕ as a subset of ℤ (the latte-integers development)."

  (:refer-clojure :exclude [and or not int = +])

  (:require [latte.core :as latte :refer [defaxiom defthm definition
                                          deflemma
                                          lambda forall proof assume have
                                          pose try-proof qed]]

            [latte.utils :as u]

            [latte-prelude.prop :as p :refer [and and* or not <=>]]
            [latte-prelude.equal :as eq :refer [equal]]
            [latte-prelude.quant :as q :refer [exists]]
            
            [latte-sets.quant :a sq :refer [forall-in]]
            [latte-sets.quant :a sq :refer [forall-in]]

            [latte-nats.core :as nats :refer [nat = zero succ]]
            [latte-nats.rec :as rec]

            [latte-integers.int :as int :refer [int]]
            [latte-integers.nat :as intnat]

            ))


(definition fzero
  [n nat]
  zero)

(definition natset->nat-prop
  []
  (lambda [g (==> int nat)]
    (and (= (g int/zero) zero)
         (forall [n int]
           (and (==> (intnat/positive (int/succ n))
                     (= (g (int/succ n)) (succ (g n))))
                (==> (intnat/negative (int/pred n))
                     (= (g (int/pred n)) (fzero (g n)))))))))

(defthm natset->nat-prop-unique
  [[n int]]
  (q/unique (natset->nat-prop)))

(defthm nat-to-natset
  (forall [P (==> nat :type)]
    (==> (forall [n nat] (P n))
         (forall-in [m intnat/nat]))
          
