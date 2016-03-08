/-
Copyright (c) 2015 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");

Theorems and exercises of the HoTT book (Chapter 3)
-/

import .ch2

open prod bool sum unit eq ua nat

/- ************************************** -/
/-    Ch.3 Sets and Logic                 -/
/- ************************************** -/

/- §3.1 (Sets and n-types)  -/

 variables {A B C Z: Type} 

 -- Definition 3.1.1 :

 definition isSet (A : Type) : Type :=
   Π (x y : A) (p q : x = y), p = q

 -- Example 3.1.2

 definition unitalleq (x y : unit) : x = y := unit.rec_on x (unit.rec_on y (refl ⋆))

 definition unitset : isSet(unit) :=
     λ (x y : unit) (p q : x = y), ((transport _ (ua (@unit_equiv x y))⁻¹ (λ x y, unitalleq x y)) p q)

 -- Example 3.1.3

 example : isSet(empty) :=
 λ (x y : empty) (p q : x=y), (empty.rec_on _ x)

 -- Example 3.1.4

 definition emptyalleq (x y : empty) : x = y := empty.rec_on _ x

/- example : isSet(ℕ) :=
 by intro m n p q; induction m; induction n; exact (transport _ (ua (nat_eq 0 0))⁻¹ (λ x y, unitalleq x y) p q);
   exact (transport _ (ua (nat_eq 0 (succ a)))⁻¹ (λ x y, emptyalleq x y) p q); induction n;
   exact (transport _ (ua (nat_eq (succ a) 0))⁻¹ (λ x y, emptyalleq x y) p q)

-/

 -- Type forming operators preserve sets

 -- Product type

 example (H₁ : isSet A) (H₂ : isSet B) :
     isSet (A × B) :=
 λ (x y : A × B) (p q : x = y), 
   have H : (ap pr1 p, ap pr2 p) = (ap pr1 q, ap pr2 q), from
     pair_eq (H₁ (pr1 x) (pr1 y) (ap pr1 p) (ap pr1 q),
     H₂ (pr2 x) (pr2 y) (ap pr2 p) (ap pr2 q)),
 (prod_uniq p)⁻¹ ⬝ (ap pair_eq H) ⬝ prod_uniq q

open funext

 definition funext_uniq {A : Type} {B : A → Type} {f g: Π (x : A), B x} (p : f = g) :
     funext (happly p) = p := sorry

 -- Pi type

 example (B : A → Type) (H : Π (x : A), isSet (B x)) :
     isSet (Π (x : A), B x) := 
 λ f g p q, have eq : happly p = happly q, from funext (λ x, H x (f x) (g x) ((happly p) x) ((happly q) x)),
 (funext_uniq p)⁻¹ ⬝ (ap funext eq) ⬝ funext_uniq q
 
 -- Homotopy n-types

 definition is1type (A : Type) : Type :=
   Π (x y : A) (p q : x = y) (r s : p = q), r = s

 -- Lemma 3.1.8 (Every set is a 1-type)

 definition setis1type (A : Type) :
     isSet A → is1type A :=
 λ f x y p q r s, let g := f x y p in
 (((lu r) ⬝ ((left_inv (g p) ⬝ᵣ r)⁻¹ ⬝ (((conc_assoc (g p)⁻¹ (g p) r)⁻¹ ⬝ ((g p)⁻¹ ⬝ₗ -- right cancelation of g(p)
 ((id_trans_i p r (g p))⁻¹ ⬝ (apd g r)) ⬝ ((apd g s)⁻¹ ⬝ (id_trans_i p s (g p))))) ⬝ -- computation of g(p) ⬝ r = g(p) ⬝ s
 conc_assoc (g p)⁻¹ (g p) s))) ⬝ (left_inv (g p) ⬝ᵣ s)) ⬝ (lu s)⁻¹ -- left cancelation of g(p)

 -- Example 3.1.8 (The universe is not a type)

 definition bnegeq :
     𝟮 ≃ 𝟮 :=
 sigma.mk bneg (qinv_to_isequiv bneg (sigma.mk bneg (λ x, bool.rec_on x idp idp,λ x, bool.rec_on x idp idp) ))

 --
 universe variables i j -- superfluous

 definition ua_comp {A B: Type.{i}} (e : A ≃ B):   --- in ch2, but I don't know why it isn't compiling!
     idtoeqv (ua e) = e := sorry
 
 definition ua_uniq {A B: Type.{i}} (p : A = B):   --- in ch2, but I don't know why it isn't compiling!
     ua (idtoeqv p) = p := sorry

 
definition universe_not_set :
     isSet(Type₀) → 𝟬 :=
 λ H, ff_ne_tt (happly (ap sigma.pr1 (((ua_comp bnegeq)⁻¹ ⬝ (ap idtoeqv (H 𝟮 𝟮 (ua bnegeq) (refl 𝟮)))) ⬝ idp⁻¹)) tt)

 --
 
 /- §3.2 (Propositions as types?)  -/

 notation `¬` A := A → 𝟬

 -- Theorem 3.2.2 (Double negation elimination does not hold generally)

 -- Some useful lemmas

 definition trans_f2u (f : Π (A : Type₀), ¬¬A → A) :
     Π (u : ¬¬𝟮), (transport (λ A, A) (ua bnegeq) (f 𝟮 (transport (λ A : Type₀, ¬¬A) (ua bnegeq)⁻¹ u)) = (f 𝟮) u) :=
 λ u : ¬¬𝟮, happly ((nondep_trans_pi (ua bnegeq) (f 𝟮))⁻¹ ⬝ (apd f (ua bnegeq))) u

 definition trans_dne_lemma (u : ¬¬𝟮) : -- used in ap_ua_lemma
    transport (λ (A : Type₀), ¬¬A) (ua bnegeq)⁻¹ u = u :=
 funext (λ x , empty.rec_on _ (u x) (transport (λ (A : Type₀), ¬¬A ) (ua bnegeq)⁻¹ u) u)

 definition trans_ua_lemma (f : Π (A : Type₀), ¬¬A → A) (u : ¬¬𝟮) :  -- used in ap_ua_lemma
    transport (λ (A : Type₀), A) (ua bnegeq) (f 𝟮 u) = bneg ((f 𝟮) u) :=
 by rewrite [trans_univ (ua bnegeq) (f 𝟮 u) ⬝ trans_idtoequiv (ua bnegeq) (f 𝟮 u)]; apply (calc
   bneg (f 𝟮 u) = sigma.pr1 bnegeq (f 𝟮 u)  : idp
   ...          = sigma.pr1 (idtoeqv (ua bnegeq)) (f 𝟮 u) :  happly (ap sigma.pr1 (ua_comp bnegeq)⁻¹) (f 𝟮 u)
   ...          = sigma.pr1 (idtoeqv (ap (λ (a : Type₀), a) (ua bnegeq))) (f 𝟮 u) :
                    (happly (ap sigma.pr1 (ap idtoeqv (@ap_func_iv Type₀ 𝟮 𝟮 𝟮 (ua bnegeq)))) (f 𝟮 u))⁻¹  )⁻¹

 definition ap_ua_lemma (f : Π (A : Type₀), ¬¬A → A) (u : ¬¬𝟮) :
     (f 𝟮) u = bneg ((f 𝟮) u) :=
 calc
  (f 𝟮) u = transport (λ (A : Type₀), A) (ua bnegeq) (f 𝟮 (transport (λ A : Type₀, ¬¬A) (ua bnegeq)⁻¹ u)) : trans_f2u
  ...     = transport (λ (A : Type₀), A) (ua bnegeq) (f 𝟮 u) : trans_dne_lemma
  ...     = bneg ((f 𝟮) u) : trans_ua_lemma

 definition prop_324 :
     Π (x : 𝟮), ¬(bneg x = x) :=
 λ x, bool.rec_on x (λ p, ff_ne_tt p⁻¹) (λ p, ff_ne_tt p)

 -- Theorem 3.2.2

 definition no_dne (f : Π A, ¬¬A  → A) : 𝟬 :=
 (λ (u : ¬¬𝟮), (prop_324 ((f 𝟮) u)) (ap_ua_lemma f u)⁻¹) (λ (nu : ¬𝟮), nu tt)

 -- Remark 3.2.6 (see ch1.ndne)

 -- Corollary 3.2.7

