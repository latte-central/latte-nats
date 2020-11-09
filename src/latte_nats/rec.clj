(ns latte-nats.rec
  "The recursion theorem for natural numbers."

  (:refer-clojure :exclude [and or not int =])

  (:require [latte.core :as latte :refer [defaxiom defthm definition
                                          deflemma
                                          lambda forall proof assume have
                                          pose try-proof qed]]

            [latte-prelude.prop :as p :refer [and]]
            [latte-nats.core :as nats :refer [nat zero succ =]]
            [latte-prelude.equal :as eq :refer [equal]]
            [latte-prelude.quant :as q :refer [exists]]

            [latte-sets.rel :as rel :refer [rel]]
            [latte-sets.powerrel :as prel]
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


(definition nat-recur-prop-rel
  "A relational variant of the recursion principle [[nat-recur-prop]]."
  [[?T :type] [x T] [f (==> T T)]]
  (lambda [R (rel nat T)]
     (and (R zero x)
          (forall [n nat]
            (forall [y T]
              (==> (R n y)
                   (R (succ n) (f y))))))))

(definition nat-fixpoint-rel
  "The relational definition of the least fixed-point
for (primitive) recursive functions on natural numbers."
  [[?T :type] [x T] [f (==> T T)]]
  (prel/rintersections (nat-recur-prop-rel x f)))
;; (lambda [n nat]
;;   (lambda [y T]
;;     (forall [R (rel nat T)]
;;       (==> (prel/rel-elem R (nat-recur-prop-rel x f))
;;            (R n y)))))

(defthm nat-fixpoint-zero
  [[?T :type] [x T] [f (==> T T)]]
  ((nat-fixpoint-rel x f) zero x))

(proof 'nat-fixpoint-zero-thm
  (assume [R (rel nat T)
           HR (prel/rel-elem R (nat-recur-prop-rel x f))]
    (have <a> (R zero x) :by (p/and-elim-left HR)))
  (qed <a>))

(defthm nat-fixpoint-succ
  [[?T :type] [x T] [f (==> T T)]]
  (forall [n nat]
    (forall [y T]
      (==> ((nat-fixpoint-rel x f) n y)
           ((nat-fixpoint-rel x f) (succ n) (f y))))))

(proof 'nat-fixpoint-succ-thm
  (assume [n nat
           y T
           Hny ((nat-fixpoint-rel x f) n y)]
    (assume [R (rel nat T)
             HR (prel/rel-elem R (nat-recur-prop-rel x f))]
      (have <a> (R n y) :by (Hny R HR))
      (have <b> (R (succ n) (f y)) :by ((p/and-elim-right HR) n y <a>))))
  (qed <b>))

(defthm nat-fixpoint-elem
  [[?T :type] [x T] [f (==> T T)]]
  (prel/rel-elem (nat-fixpoint-rel x f) (nat-recur-prop-rel x f)))

(proof 'nat-fixpoint-elem-thm
  (qed (p/and-intro (nat-fixpoint-zero x f)
                    (nat-fixpoint-succ x f))))


(defthm nat-fixpoint-prop
  [[?T :type] [x T] [f (==> T T)]]
  (forall [R (rel nat T)]
        (==> (prel/rel-elem R (nat-recur-prop-rel x f))
             (rel/subrel (nat-fixpoint-rel x f) R))))

(proof 'nat-fixpoint-prop-thm
  (qed (prel/rintersections-lower-bound (nat-recur-prop-rel x f))))


(defthm nat-recur-rel-ex
  "The existential part of the relational recursion theorem
for natural numbers."
  [[?T :type] [x T] [f (==> T T)]]
  (forall [n nat]
    (exists [y T] ((nat-fixpoint-rel x f) n y))))


(proof 'nat-recur-rel-ex-thm
  "We proceed by induction on `n`."

  (pose FIX := (nat-fixpoint-rel x f))

  "Base case n=0 : we want to prove (FIX zero y) is true for some y."
  (have <a1> (FIX zero x) :by (nat-fixpoint-zero x f))
  (have <a> (exists [y T] (FIX zero y))
        :by ((q/ex-intro (lambda [y T] (FIX zero y)) x) <a1>))

  "Inductive case"
  (assume [n nat
           Hn (exists [y T] (FIX n y))]
    (assume [y T
             Hy (FIX n y)]
      (have <b1> (FIX (succ n) (f y))
            :by ((nat-fixpoint-succ x f) n y Hy))
      (have <b2> (exists [z T] (FIX (succ n) z))
            :by ((q/ex-intro (lambda [z T] (FIX (succ n) z)) (f y)) <b1>)))

    (have <b> (exists [z T] (FIX (succ n) z))
          :by ((q/ex-elim-rule (lambda [y T] (FIX n y)) (exists [z T] (FIX (succ n) z)))
               Hn <b2>)))

  (have <c> (forall [n nat]
              (exists [z T] (FIX n z)))
        :by ((nats/nat-induct (lambda [n nat]
                                (exists [z T] (FIX n z))))
             <a> <b>))

  (qed <c>))

(defthm nat-recur-rel-sing
  "The singleness part of the relational recursion theorem
for natural numbers."
  [[?T :type] [x T] [f (==> T T)]]
  (forall [n nat]
    (q/single (lambda [y T] ((nat-fixpoint-rel x f) n y)))))

(proof 'nat-recur-rel-sing-thm
  (pose FIX := (nat-fixpoint-rel x f))

  (assume [x1 T x2 T
           Hx1 (FIX zero x1)
           Hx2 (FIX zero x2)]
    ))
