(ns latte-nats.core
  "A formalization of the type of natural numbers."

  (:refer-clojure :exclude [and or not int =])

  (:require [latte.core :as latte :refer [defaxiom defthm definition
                                          lambda forall
                                          proof try-proof assume have qed]]
            [latte-prelude.prop :as p :refer [not]]
            [latte-prelude.equal :as eq]
            [latte-prelude.quant :as q :refer [exists]]
            [latte-prelude.fun :as fun]
            ))

(defaxiom nat
  "The type of natural numbers."
  []
  :type)

(definition =
  "The equality on natural numbers."
  [[n nat] [m nat]]
  (eq/equality nat n m))

(definition <>
  "The inequality on natural numbers."
  [[n nat] [m nat]]
  (not (= n m)))

(defaxiom zero
  "The number zero."
  []
  nat)

(defaxiom succ
  "The successor number."
  []
  (==> nat nat))

(definition one
  "The number one."
  []
  (succ zero))

(defaxiom succ-injective
  "The successor function is injective."
  []
  (fun/injective succ))

(defthm succ-single
  []
  (forall [n nat] (q/single (lambda [m nat] (= (succ m) n)))))

(proof 'succ-single
  (qed ((fun/injective-single succ) succ-injective)))

(defaxiom zero-not-succ
  "There is not natural number \"below\" zero."
  []
  (forall [n nat] 
    (<> (succ n) zero)))

(defaxiom nat-induct
  "The induction principle for natural numbers."
  [[P (==> nat :type)]]
  (==> (P zero)
       (forall [n nat]
         (==> (P n)
              (P (succ n))))
       (forall [n nat]
         (P n))))


(defthm nat-case
  "Case analysis for natural numbers."
  [[P (==> nat :type)]]
  (==> (P zero)
       (forall [n nat] (P (succ n)))
       (forall [n nat] (P n))))

(proof 'nat-case
  (assume [H0 (P zero)
           Hs (forall [n nat] (P (succ n)))]
    (assume [n nat
             Hn (P n)]
      (have <a> (P (succ n)) :by (Hs n)))
    (assume [n nat]
      (have <b> (P n) :by ((nat-induct P) H0 <a> n))))
  (qed <b>))





