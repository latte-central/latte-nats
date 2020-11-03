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
  "We proceed by induction on `n`."
  "Base case n=0 : we want to prove (FIX zero y) is true for some y."

  ;; BUG !!! If we use the following definition,
  ;; then the variable x will be capture inside (ex-def ... (FIX ...) ...) below
  ;;(pose FIX := (nat-fixpoint-rel x f))

  (assume [R (rel nat T)
           HR (prel/rel-elem R (nat-recur-prop-rel x f))]
    (have <a1> (R zero x) :by (p/and-elim-left HR)))
  (have <a> (exists [y T] ((nat-fixpoint-rel x f) zero y)) 
        :by ((q/ex-intro (lambda [y T] ((nat-fixpoint-rel x f) zero y)) x) <a1>))
  "Inductive case"
  (assume [n nat
           Hn (exists [y T] ((nat-fixpoint-rel x f) n y))]
    (assume [y T
             Hy ((nat-fixpoint-rel x f) n y)]
      (assume [R (rel nat T)
               HR (prel/rel-elem R (nat-recur-prop-rel x f))]
        (have <b1> (R n y) :by (Hy R HR))
        (have <b2> (==> (R n y) (R (succ n) (f y)))
              :by ((p/and-elim-right HR) n y))
        (have <b3> (R (succ n) (f y))
              :by (<b2> <b1>)))
      (have <b4> ((nat-fixpoint-rel x f) (succ n) (f y)) :by <b3>)
      (have <b5> (exists [z T] ((nat-fixpoint-rel x f) (succ n) z))
            :by ((q/ex-intro (lambda [z T] ((nat-fixpoint-rel x f) (succ n) z)) (f y)) <b4>)))

    (have <b6> (forall [y T] (==> ((lambda [y T] ((nat-fixpoint-rel x f) n y)) y) 
                                  (exists [z T] ((nat-fixpoint-rel x f) (succ n) z)))) :by <b5>)

    (have <Hn'> (q/ex (lambda [y T] ((nat-fixpoint-rel x f) n y))) :by Hn)

    (have <b7> (==> (q/ex (lambda [y T] ((nat-fixpoint-rel x f) n y))) 
                    (forall [y T] (==> ((lambda [y T] ((nat-fixpoint-rel x f) n y)) y)
                                       (exists [z T] ((nat-fixpoint-rel x f) (succ n) z))))
                    (exists [z T] ((nat-fixpoint-rel x f) (succ n) z)))
          :by (q/ex-elim-rule (lambda [y T] ((nat-fixpoint-rel x f) n y)) (exists [z T] ((nat-fixpoint-rel x f) (succ n) z))))

    (have <b> (exists [z T] ((nat-fixpoint-rel x f) (succ n) z))
          :by (<b7> <Hn'> <b6>)))

  (have <c> (forall [n nat] (==> (exists [z T] ((nat-fixpoint-rel x f) n z))
                                 (exists [z T] ((nat-fixpoint-rel x f) (succ n) z))))
        :by <b>)
                    


  (have <d> (forall [n nat] 
              (exists [z T] ((nat-fixpoint-rel x f) n z)))
        :by ((nats/nat-induct (lambda [n nat] 
                                (exists [z T] ((nat-fixpoint-rel x f) n z))))
             <a> <c>))

  (qed <d>))


(comment

;; IMPORTANT BUG BELOW :  Bound variables of terms, e.g. x in FIX
;; can be captured by bound variables inside other definitions,
;; e.g.  the x bound in the definition of ex-def...
;; One possible solution is to use gensyms in definitions...
;; or to be more careful while instantiating definitions
;; (maybe this is the thing to do...)

(try-proof 'nat-recur-rel-ex-thm
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
    (pose A := (exists [z T] (FIX (succ n) z)))

    (have <b6> (forall [y T] (==> (P y) A)) :by <b5>)

    (have <Hn'> (q/ex P) :by Hn)

    (have <b7> (==> (q/ex P) (forall [y T] (==> (P y) A)) A)
          :by (q/ex-elim-rule P A))

))


;;     (have <b> _
;;           :by ((q/ex-elim-rule P
;;                                (exists [z T] (FIX (succ n) z)))
;;                <Hn'> <b6>))



;; ))


;;   "Now we apply the induction principle."
;;   (have <c> (forall [n nat]
;;               (exists [y T] (FIX n y)))
;;         :by ((nats/nat-induct (lambda [n nat]
;;                                 (exists [y T] (FIX n y))))
;;              <a> <b>))
;; )

;;   (qed <c>))




)

