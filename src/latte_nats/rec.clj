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
  (pose FIX := (nat-fixpoint-rel x f))
  "We proceed by induction on `n`."
  "Base case n=0 : we want to prove (FIX zero y) is true for some y."
  (assume [R (rel nat T)
           HR (prel/rel-elem R (nat-recur-prop-rel x f))]
    (have <a1> (R zero x) :by (p/and-elim-left HR)))
  (have <a> (exists [y T] (FIX zero y)) 
        :by ((q/ex-intro (lambda [y T] (FIX zero y)) x) <a1>))
  "Inductive case"
  (assume [n nat
           Hn (exists [y T] (FIX n y))]
    (assume [y T
             Hy (FIX n y)]
      (assume [R (rel nat T)
               HR (prel/rel-elem R (nat-recur-prop-rel x f))]
        (have <b1> (R n y) :by (Hy R HR))
        (have <b2> (==> (R n y) (R (succ n) (f y)))
              :by ((p/and-elim-right HR) n y))
        (have <b3> (R (succ n) (f y))
              :by (<b2> <b1>)))
      (have <b4> (FIX (succ n) (f y)) :by <b3>)
      (have <b5> (exists [z T] (FIX (succ n) z))
            :by ((q/ex-intro (lambda [z T] (FIX (succ n) z)) (f y)) <b4>)))

    (pose P := (lambda [y T] (FIX n y)))
    (have <b6> (forall [y T] (==> (P y)
                                  (exists [z T] (FIX (succ n) z))))
          :by <b5>)

    (have <Hn'> (q/ex P) :by Hn)

    (pose A := (exists [z T] (FIX (succ n) z)))

    (have <b7> (==> (forall [y T] (==> (P y) A)) A)
          :by ((q/ex-elim-rule P A) <Hn'>))

))

    (have <b> _
          :by ((q/ex-elim-rule P
                               (exists [z T] (FIX (succ n) z)))
               <Hn'> <b6>))
  ))
))

  "Now we apply the induction principle."
  (have <c> (forall [n nat]
              (exists [y T] (FIX n y)))
        :by ((nats/nat-induct (lambda [n nat]
                                (exists [y T] (FIX n y))))
             <a> <b>))
)

  (qed <c>))




    

