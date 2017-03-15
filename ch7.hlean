/-
Copyright (c) 2017 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");

Theorems and exercises of the HoTT book (Chapter 7)
-/

import .ch2 .ch3 .ch4

open eq prod unit bool sum sigma ua funext nat lift decidable

/- ************************************** -/
/-    Ch.7 Homotopy n-Types               -/
/- ************************************** -/

 variables {A B C : Type} 

 universe variables i j

/- §7.1 (Definition of n-Types)  -/

 inductive neg_two_int : Type :=
 | neg_two : neg_two_int
 | succ : neg_two_int → neg_two_int

 open neg_two_int

 notation `ℤ₋₂` := neg_two_int
 notation `-2` := neg_two
 notation `-1` := succ neg_two
 notation  `-0` := succ (succ neg_two)

 definition is_type : Π (n : ℤ₋₂) (X : Type), Type
 | is_type -2 X := isContr X
 | is_type (succ k) X := Π (x y : X), is_type k (x = y)

 -- Example 7.1.3

 definition is_neg_1_type_eq_isProp (X : Type) :
     is_type -1 X = isProp X :=
 ua (prop_eqv (pi_preserves_prop (λ x, pi_preserves_prop 
 (λ y, isContr_is_prop (x = y)))) (isProp_is_prop X) 
  (pr2 (prop_iff_contr_path X)) (pr1 (prop_iff_contr_path X)))

 definition is_0_type_eq_isSet (X : Type) :
     is_type -0 X = isSet X :=
 ua (pi_preserves_equiv (λ (x : X), pi_preserves_equiv
  (λ (y : X), (idtoeqv (is_neg_1_type_eq_isProp (x = y) )))))

 --

/- §7.2 (Uniqueness of identity proofs and Hedberg's theorem)  -/

 -- Theorem 7.2.5 (Hedberg Theorem)  
 
 -- This proof is  based on Alan Schmitt's coq proof (https://sympa.inria.fr/sympa/arc/coq-club/2016-09/msg00064.html)

 -- If a type has decidable equality, one can define a "collapsing" function (x = y) → (x = y) 

 definition collapse {x y : A} (H : decidable_eq A) :
     (x = y) → (x = y) :=
 λ p, sum.rec_on (H x y) (λ Heq, Heq) (λ Hne, empty.rec_on _ (Hne p))

 -- such as `collapse p = colapse q` holds for any p q : x = y

 definition collapses_eq {x y : A} (H : decidable_eq A) (p q : x = y) :
     collapse H p = collapse H q :=
 begin
  unfold collapse,
  cases (H x y) with Heq Hne,
   reflexivity,
   induction (Hne p)
 end

 -- and any p : x = y can be rewritten in terms of collapse

 definition rewrite_collapse {x y : A} (H : decidable_eq A) (p : x = y) :
   (collapse H (refl x))⁻¹ ⬝ (collapse H p) = p :=
 eq.rec_on p (left_inv _)

 -- now we just need to rewrite p and q in terms of collapse and left-whisker `collapses_eq` to show that p = q

 definition UIP {x y : A} (H : decidable_eq A) (p q : x = y) :
     p = q :=
 (rewrite_collapse H p)⁻¹ ⬝ 
  l_whisker _ (collapses_eq H p q) ⬝ 
 (rewrite_collapse H q)

 -- Theorem 7.2.6

 definition neq_succ {n : ℕ} : ¬ (n = succ n) :=
 by intro H; induction n with n IH; exact (empty.rec _ (down (nat.no_confusion H))); exact (IH (ap pred H))

 definition nat_deceq (n m: ℕ) :
     (n = m) + ¬(n = m) :=
 begin
  revert m, induction n with n IHn, 
  { intro m, induction m with m IHm,
    exact (inl (refl 0)),
    cases IHm with H₁ H₂,
      exact (inr (λ H, empty.rec _ (down (nat.no_confusion (H ⬝ (ap succ H₁)⁻¹))) )),
      exact (inr (λ H, H₂ (ap pred H))) },
  { intro m, induction m with m IHm,
    cases (IHn 0) with H₁,
      exact (inr (λ H, empty.rec _ (neq_succ (H⁻¹ ⬝ (ap succ H₁))) )),
      exact (inr (λ H, empty.rec _ (down (nat.no_confusion H )))),
    cases (IHn m) with H₁ H₂,
      exact (inl (ap succ H₁)),
      exact (inr (λ H, H₂ (ap pred H) )) }
 end
