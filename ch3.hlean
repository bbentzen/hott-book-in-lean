/-
Copyright (c) 2016 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");

Theorems and exercises of the HoTT book (Chapter 3)
-/

import .ch2 types.bool

open eq prod unit bool sum sigma ua funext nat lift

/- ************************************** -/
/-    Ch.3 Sets and Logic                 -/
/- ************************************** -/

/- §3.1 (Sets and n-types)  -/

 variables {A B P Q Z: Type} 

 -- Definition 3.1.1 :

 definition isSet (A : Type) : Type :=
   Π (x y : A) (p q : x = y), p = q

 -- Example 3.1.2 (𝟭 is a set)

 definition unit_is_set : isSet(𝟭) :=
 λ (x y : 𝟭) (p q : x = y), ((transport _ (ua (@unit_equiv x y))⁻¹ (λ x y, @unit_eq x y x)) p q)

 -- Example 3.1.3 (𝟬 is a set)

 definition empty_is_set : isSet(𝟬) :=
 λ (x y : 𝟬) (p q : x=y), (empty.rec_on _ x)

 -- Example 3.1.4 (ℕ is a set)

 definition nat_is_set : isSet(ℕ) :=
 assert natcode_eq : Π (m n : ℕ) (p q : natcode m n), p = q, from
 begin
  intro m n, revert n, induction m with m IHm,
   {intro n p q, induction n with n IHn,
    apply (@unit_eq p q p), apply (empty.rec_on _ _)},
   {intro n p q, induction n with n IHn,
    apply (empty.rec_on _ _),
    apply IHm n}
 end,
 begin
   intro m n, revert n, induction m with m IHm,
    {intro n p q, induction n with n IHn,
     exact (transport _ (ua (nat_eq 0 0))⁻¹ (λ x y, @unit_eq x y x) p q),
     exact (transport _ (ua (nat_eq 0 (succ n)))⁻¹ (λ x y, empty.rec_on _ x) p q)},
    intro n p q, induction n with n IHn,
    exact (transport _ (ua (nat_eq (succ m) 0))⁻¹ (λ x y, empty.rec_on _ x) p q),
    exact (transport _ (ua (nat_eq (succ m) (succ n)))⁻¹ (λ x y, natcode_eq (succ m) (succ n) x y) p q)
 end

 -- Type forming operators preserve sets

 -- Product type

 definition prod_preserves_sets (H₁ : isSet A) (H₂ : isSet B) :
     isSet (A × B) :=
 λ (x y : A × B) (p q : x = y), 
   have H : (ap pr1 p, ap pr2 p) = (ap pr1 q, ap pr2 q), from
     pair_eq (H₁ (pr1 x) (pr1 y) (ap pr1 p) (ap pr1 q),
     H₂ (pr2 x) (pr2 y) (ap pr2 p) (ap pr2 q)),
 (prod_uniq p)⁻¹ ⬝ (ap pair_eq H) ⬝ prod_uniq q

 -- Sigma type

 definition sigma_preserves_sets (H₁ : isSet A) {B : A → Type} (H₂ : Π (x : A), isSet (B x)) :
     isSet (Σ (x : A), B x) :=
 begin
   intro w w' p q,
   apply ((sigma_uniq p)⁻¹ ⬝ ap sigma_eq (
     show ap_sigma p = ap_sigma q, from
     begin
       cases w with a b, cases w' with a' b', apply (sigma_eq ⟨H₁ a a' (pr1 (ap_sigma p)) (pr1 (ap_sigma q)),
         begin 
           apply ((H₂ a') (transport B (pr1 (ap_sigma q)) b) b' 
           (transport (λ (p : a = a'), transport B p b = b') (H₁ a a' (pr1 (ap_sigma p)) (pr1 (ap_sigma q))) (pr2 (ap_sigma p)))
           (pr2 (ap_sigma q)) )
         end ⟩)
      end) ⬝ sigma_uniq q)
 end

 -- Pi type

 definition pi_preserves_sets (B : A → Type) (H : Π (x : A), isSet (B x)) :
     isSet (Π (x : A), B x) := 
 λ f g p q, have eq : happly p = happly q, from funext (λ x, H x (f x) (g x) ((happly p) x) ((happly q) x)),
 (funext_uniq p)⁻¹ ⬝ (ap funext eq) ⬝ funext_uniq q
 
 -- Homotopy n-types

  definition is_1_Type (A : Type) : Type :=
   Π (x y : A) (p q : x = y) (r s : p = q), r = s

 -- Lemma 3.1.8 (Every set is a 1-type)

 definition set_is_1_type :
     isSet A → is_1_Type A :=
 λ f x y p q r s, let g := f x y p in
 (((lu r) ⬝ ((left_inv (g p) ⬝ᵣ r)⁻¹ ⬝ (((conc_assoc (g p)⁻¹ (g p) r)⁻¹ ⬝ ((g p)⁻¹ ⬝ₗ -- right cancelation of g(p)
 ((id_trans_i p r (g p))⁻¹ ⬝ (apd g r)) ⬝ ((apd g s)⁻¹ ⬝ (id_trans_i p s (g p))))) ⬝ -- computation of g(p) ⬝ r = g(p) ⬝ s
 conc_assoc (g p)⁻¹ (g p) s))) ⬝ (left_inv (g p) ⬝ᵣ s)) ⬝ (lu s)⁻¹ -- left cancelation of g(p)

 -- Example 3.1.8 (The universe is not a type)

 definition bneg_eq :
     𝟮 ≃ 𝟮 :=
 sigma.mk bneg (qinv_to_isequiv bneg (sigma.mk bneg (λ x, bool.rec_on x idp idp,λ x, bool.rec_on x idp idp) ))
 
definition universe_not_set :
     isSet(Type₀) → 𝟬 :=
 λ H, ff_ne_tt (happly (ap sigma.pr1 (((ua_comp bnegeq)⁻¹ ⬝ (ap idtoeqv (H 𝟮 𝟮 (ua bnegeq) (refl 𝟮)))) ⬝ idp⁻¹)) tt)

 --
 
 /- §3.2 (Propositions as types?)  -/

 notation `¬` A := A → 𝟬

 -- Theorem 3.2.2 (Double negation elimination does not hold generally)

 -- Some useful lemmas

 definition trans_f2u (f : Π (A : Type₀), ¬¬A → A) :
     Π (u : ¬¬𝟮), (transport (λ A, A) (ua bneg_eq) (f 𝟮 (transport (λ A : Type₀, ¬¬A) (ua bneg_eq)⁻¹ u)) = (f 𝟮) u) :=
 λ u : ¬¬𝟮, happly ((nondep_trans_pi (ua bneg_eq) (f 𝟮))⁻¹ ⬝ (apd f (ua bneg_eq))) u

 definition trans_dne_lemma (u : ¬¬𝟮) : -- used in ap_ua_lemma
    transport (λ (A : Type₀), ¬¬A) (ua bneg_eq)⁻¹ u = u :=
 funext (λ x , empty.rec_on _ (u x) (transport (λ (A : Type₀), ¬¬A ) (ua bneg_eq)⁻¹ u) u)

 definition trans_ua_lemma (f : Π (A : Type₀), ¬¬A → A) (u : ¬¬𝟮) :  -- used in ap_ua_lemma
    transport (λ (A : Type₀), A) (ua bneg_eq) (f 𝟮 u) = bneg ((f 𝟮) u) :=
 by rewrite [trans_univ (ua bneg_eq) (f 𝟮 u) ⬝ trans_idtoequiv (ua bneg_eq) (f 𝟮 u)]; apply (calc
   bneg (f 𝟮 u) = sigma.pr1 bneg_eq (f 𝟮 u)  : idp
   ...          = sigma.pr1 (idtoeqv (ua bneg_eq)) (f 𝟮 u) :  happly (ap sigma.pr1 (ua_comp bneg_eq)⁻¹) (f 𝟮 u)
   ...          = sigma.pr1 (idtoeqv (ap (λ (a : Type₀), a) (ua bneg_eq))) (f 𝟮 u) :
                    (happly (ap sigma.pr1 (ap idtoeqv (@ap_func_iv Type₀ 𝟮 𝟮 (ua bneg_eq)))) (f 𝟮 u))⁻¹  )⁻¹

 definition ap_ua_lemma (f : Π (A : Type₀), ¬¬A → A) (u : ¬¬𝟮) :
     (f 𝟮) u = bneg ((f 𝟮) u) :=
 calc
  (f 𝟮) u = transport (λ (A : Type₀), A) (ua bneg_eq) (f 𝟮 (transport (λ A : Type₀, ¬¬A) (ua bneg_eq)⁻¹ u)) : trans_f2u
  ...     = transport (λ (A : Type₀), A) (ua bneg_eq) (f 𝟮 u) : trans_dne_lemma
  ...     = bneg ((f 𝟮) u) : trans_ua_lemma

 definition prop_324 :
     Π (x : 𝟮), ¬(bneg x = x) :=
 λ x, bool.rec_on x (λ p, ff_ne_tt p⁻¹) (λ p, ff_ne_tt p)

 -- Theorem 3.2.2

 definition no_dne :
     (Π A, ¬¬A → A) → 𝟬 :=
 λ f, (λ (u : ¬¬𝟮), (prop_324 ((f 𝟮) u)) (ap_ua_lemma f u)⁻¹) (λ (nu : ¬𝟮), nu tt)

 -- Remark 3.2.6 (see ch1.ndne)

 -- Corollary 3.2.7

 definition no_lem : --(g : Π A, A ⊎ ¬ A) : 𝟬  :=      
     (Π A, A + ¬ A) → 𝟬 :=
 λ g, no_dne (λ (A : Type₀) (x : ¬¬A), sum.rec_on (g (A)) (λ y, y) (λ y, empty.rec_on _ (x y)))

 --

 /- §3.3 (Mere propositions)  -/

 -- Definition 3.3.1

 definition isProp (A : Type) : Type :=
   Π (x y : A), x = y

 -- Lemma 3.3.2

 definition unit_is_prop : isProp(𝟭) :=
 λ x y, @unit_eq x y x

 -- Lemma 3.3.3

 definition prop_eqv (H₁ : isProp P) (H₂ : isProp Q) : 
     (P → Q) → (Q → P) → (P ≃ Q) :=
 λ f g, have comp_rule : f ∘ g ~ id Q, from λ q, H₂ (f (g q)) q,
 have uniq_rule : g ∘ f ~ id P, from λ p, H₁ (g (f p)) p,
 ⟨ f, ( ⟨g, comp_rule⟩, ⟨g, uniq_rule⟩ ) ⟩

 definition prop_eqv_unit (p₀ : P) (H : isProp P) :
    P ≃ 𝟭 :=
 let f : P → 𝟭 :=  λ p, ⋆ in let g : 𝟭 → P :=  λ x, p₀ in
 prop_eqv H unit_is_prop f g

 -- Lemma 3.3.4 Every mere proposition is a set

 definition prop_is_set :
     isProp(P) → isSet(P) :=
 λ H x y p q, let g := H x in (((lu p) ⬝ ((left_inv (g x) ⬝ᵣ p)⁻¹ ⬝ (((conc_assoc (g x)⁻¹ (g x) p)⁻¹ ⬝ ((g x)⁻¹ ⬝ₗ -- right cancelation of g(x)
 ((id_trans_i x p (g x))⁻¹ ⬝ (apd g p)) ⬝ ((apd g q)⁻¹ ⬝ (id_trans_i x q (g x))))) ⬝ -- computation of g(x) ⬝ p = g(x) ⬝ q
 conc_assoc (g x)⁻¹ (g x) q))) ⬝ (left_inv (g x) ⬝ᵣ q)) ⬝ (lu q)⁻¹ -- left cancelation of g(x)

  -- Lemma 3.3.5 The types isProp and isSet are mere propositions

 definition isProp_is_prop (P : Type) :
     isProp (isProp(P)) :=
 λ H₁ H₂, funext (λ x, funext (λ y, (prop_is_set H₁ x y (H₁ x y) (H₂ x y))))

 definition isSet_is_prop (A : Type) :
     isProp (isSet(A)) :=
 λ H₁ H₂, funext (λ x, funext (λ y, funext (λ p, funext (λ q, set_is_1_type H₁ x y p q (H₁ x y p q) (H₂ x y p q) ))))

 --

 /- §3.4 (Classical vs. intuitionistic logic)  -/

 definition lem : Type :=
    Π (A : Type), (isProp(A) → (A + ¬ A))
 
 definition dne : Type :=
    Π (A : Type), (isProp(A) → (¬¬ A → A))

 -- Definition 3.4.3

 namespace decidable

 definition decidable (A : Type) : Type := A + ¬ A
    
 definition decidable_family (B : A → Type) : Type := Π (a : A), B (a) + ¬ B (a)

 definition decidable_eq (A : Type) : Type := Π (a b : A), (a = b) + ¬ (a = b)

 end decidable

 --

 /- §3.5 (Subsets and propositional resizing)  -/

 -- Lemma 3.5.1

 definition prop_sigma_eq (P : A → Type) (H : Π (x : A), isProp(P(x))) (u v : Σ (x : A), P x) :
     (pr1 u = pr1 v) → u = v :=
 λ p, sigma_eq ⟨p, begin cases u with u1 u2, cases v with v1 v2, esimp at *, induction p, apply ((H u1) u2 v2) end ⟩
 
 -- Definitions of subset and subtype

 definition subset (P : A → Type) {H : Π (x : A), isProp(P(x))} : Type :=
     Σ (x : A), P x

 notation `{` binder `|` x :(scoped P, subset P) `}`  := x

 --

 /- §3.6 (The logic of mere propositions)  -/

 -- Example 3.6.1

 definition prod_preserves_prop (H₁ : isProp A) (H₂ : isProp B) :
     isProp (A × B) :=
 λ x y, prod.rec_on x (λ a b, prod.rec_on y (λ a' b', pair_eq (H₁ a a', H₂ b b')))

 definition sigma_preserves_prop (H₁ : isProp A) {B : A → Type} (H₂ : Π (x : A), isProp (B x)) :
     isProp (Σ (x : A), B x) :=
 λ w w', sigma.rec_on w (λ w1 w2, sigma.rec_on w' (λ w1' w2', sigma_eq ⟨H₁ w1 w1', H₂ w1' (transport B (H₁ w1 w1') w2) w2' ⟩  ))

 -- Example 3.6.2

 definition pi_preserves_prop {B : A → Type} (H : Π (x : A), isProp (B x)) :
     isProp (Π (x : A), B x) :=
 λ f g, funext (λ x, H x (f x) (g x))

 definition func_preserves_prop (H : isProp B) :
     isProp (A → B) :=
 λ f g, funext (λ x, H (f x) (g x))

 definition neg_preserves_prop (H : isProp A) :
     isProp (¬A) :=
 func_preserves_prop H (λ x y, empty.rec_on _ x)

 -- A + B does not preserve propositions

 definition sum_doesnt_pres_prop :
     (Π (A : Type₀) (B : Type₀) (H₁ : isProp A) (H₂ : isProp B), isProp (A + B)) →  𝟬 :=
 λ f, let H := f 𝟭 𝟭 (λ u v, @unit_eq u v u) (λ u v, @unit_eq u v u) in
 down (encode (inr ⋆) (H (inl ⋆) (inr ⋆)))

 --

 /- §3.7 (Propositional truncation)  -/

 inductive truncation (A : Type) : Type :=
 | mk : A → truncation A

 constant isTrunc (A : Type) : isProp (truncation A) 
 
 notation `║` A `║`  := truncation A
 notation `|` a `|`  := truncation.mk a

 definition lor (P Q : Type) : Type :=
   ║P + Q║

 definition lexists (A : Type) (P : A → Type) : Type :=
   ║(Σ (x : A), P x)║

 notation P `∨` Q  := lor P Q

 notation `∃` binder `,` x :(scoped P, lexists _ P) := x

 notation P `↔` Q  := (P → Q) × (Q → P)

 -- Truncation commutes with the function type

 definition trunc_distrib (f : ║A → B║) :
     (║A║ → ║B║) :=
 λ a, truncation.rec_on a (λ a', truncation.rec_on f (λ f', |f' a'|) )

 --

 /- §3.8 (The axiom of choice)  -/ 

 --

 /- §3.9 (The principle of unique choice)  -/ 

 -- Lemma 3.9.1

 definition prop_eq_trunc (H : isProp P) :
     P ≃ ║P║ :=
 prop_eqv H (isTrunc P) (λ p, |p|) ( λ x, truncation.rec_on x (λ p, p))

 -- Corollary 3.9.2 (The principle of unique choice)

 definition puc {P : A → Type} (H₁ : Π (x : A), isProp (P x)) (H₂ : Π (x : A), ║P x║) :
     Π (x : A), P x :=
 λ x, (pr1 (prop_eq_trunc (H₁ x))⁻¹) (H₂ x)
 
 --

 /- §3.11 (Contractibility)  -/ 

 -- Definition 3.11.1

 definition isContr (A : Type) : Type :=
   Σ (a : A), Π (x : A), a = x

 -- Lemma 3.11.3

 definition contr_iff_pprop (A : Type) :
     isContr A ↔ Σ (a : A), isProp A :=
 (λ c, ⟨pr1 c, (λ x y, ((pr2 c) x)⁻¹ ⬝ ((pr2 c) y) )⟩,
  λ w, ⟨ pr1 w, λ (x : A), (pr2 w) (pr1 w) x⟩ )

 definition pprop_if_unit {A : Type₀}:
     (Σ (a : A), isProp A) ↔ (A ≃ 𝟭) :=
 (λ w, prop_eqv_unit (pr1 w) (pr2 w),
  λ e, ⟨ transport (λ x, x) (ua e)⁻¹ ⋆, transport isProp (ua e)⁻¹ unit_is_prop ⟩)

 definition contr_iff_unit (A : Type) :
     isContr A → (A ≃ 𝟭) :=
 λ c, (λ w, prop_eqv_unit (pr1 w) (pr2 w)) ((pr1 (contr_iff_pprop A)) c)

 -- Lemma 3.11.4

 definition isContr_is_prop (A : Type) :
     isProp (isContr A) :=
 λ c c', sigma.rec_on c (λ a p,  sigma.rec_on c' (λ a' p', (sigma_eq ⟨p a', funext (λ (x : A), 
   (prop_is_set (pr2 ((pr1 (contr_iff_pprop A)) ⟨a,p⟩))) a' x ((transport _ (p a') p) x) (p' x) )⟩) ))

 -- Corollary 3.11.5

 definition contr_to_isContr (A : Type) :
     isContr A → isContr (isContr A) :=
 λ c, pr2 (contr_iff_pprop (isContr A)) ⟨ c, isContr_is_prop A⟩ 

 -- Lemma 3.11.6

 definition pi_preserves_contr {P : A → Type} (c : Π (a : A), isContr (P a)) :
     isContr (Π (a : A), P a) :=
 pr2 (@contr_iff_pprop (Π (a : A), P a)) ⟨ λ a, pr1 (c a), pi_preserves_prop (λ a, pr2 (pr1 (contr_iff_pprop (P a)) (c a))) ⟩

 -- Lemma 3.11.7 (Retractions)

 definition retrac_contr (c : isContr A) (r : A → B) (s : B → A) (ε : Π (y : B), r (s y) = y) :
     isContr B := 
 by induction c with a p; apply ⟨ r a, λ y, ap r (p (s y)) ⬝ ε y ⟩

 -- Lemma 3.11.8

 definition path_contr (a : A) :
     isContr (Σ (x : A), a = x ) := 
 ⟨ ⟨a,refl a⟩, λ w, sigma.rec_on w (λ a' p, sigma_eq ⟨p, eq.rec_on p (refl (refl a))⟩ ) ⟩

 -- If contractible center is in the right

 definition path_contr_r (a : A) :
     isContr (Σ (x : A), x = a ) := 
 ⟨ ⟨a,refl a⟩, λ w, sigma.rec_on w (λ a' p, sigma_eq ⟨ p⁻¹, eq.rec_on p idp ⟩ ) ⟩  

 -- Lemma 3.11.9

 -- (i)

 definition contr_eq_i (P : A → Type) (g : Π (x : A), isContr (P x)) :
     (Σ (x : A), P x) ≃ A := 
 let qinv := λ a, ⟨a, pr1 (g a)⟩ in
 have α : pr1 ∘ qinv ~ id A, from λ x, idp,
 have β : qinv ∘ pr1 ~  id _, from
   λ w, sigma.rec_on w (λ a p, sigma_eq ⟨refl a, (pr2 (g a)) p⟩),
 ⟨(λ x, pr1 x), (⟨qinv, α⟩, ⟨qinv, β⟩)⟩

 -- (ii)

 definition contr_eq_ii (P : A → Type) (c : isContr A) :
     (Σ (x : A), P x) ≃ P (pr1 c) := 
 let contreq := λ w, transport P ((pr2 c) (pr1 w))⁻¹ (pr2 w) in  -- →
 let qinv := λ p, ⟨ pr1 c, p⟩ in                              -- ← 
 have α : Π x : P (pr1 c), contreq (qinv x) = x, from λ x,    
   (happly (ap (transport P)
    (prop_is_set (pr2 ((pr1 (contr_iff_pprop A)) c)) -- this show that ((pr2 c) (pr1 c))⁻¹
    (pr1 c) (pr1 c) ((pr2 c) (pr1 c))⁻¹ (refl (pr1 c)))) x), -- equals refl (pr1 c)
 have β : Π w : (Σ (x : A), P x), (qinv (contreq w)) = w, from
  begin
    intro w, cases w with w1 w2, esimp at *,
    induction ((pr2 c) w1), reflexivity
  end,   
 ⟨contreq, (⟨qinv, α⟩, ⟨qinv, β⟩)⟩

 -- Lemma 3.11.10 (Contractible types as ─2-types)  

 definition prop_iff_contr_path (A : Type) :  
     isProp A ↔ Π (x y : A), isContr (x = y) :=
 (λ H x y, ⟨(H x y), λ p, (prop_is_set H) x y (H x y) p⟩,
  λ c x y, pr1 (c x y) )

 --
 
 /- Selected Exercises -/

 universe variables i

 -- Exercise 3.1

 definition eq_set {A B : Type.{i}} :
     (A ≃ B) → isSet A → isSet B :=
 λ e H, transport _ (ua e) H

 -- Similarly for mere propositions

 definition eq_prop {A B : Type.{i}} :
     (A ≃ B) → isProp A → isProp B :=
 λ e H, transport _ (ua e) H

 -- Exercise 3.2

 definition sum_preserves_sets {A B : Type.{i}}:
     isSet A → isSet B → isSet (A + B) :=
 begin
  intro H₁ H₂ w w' p q, cases w with a b,
  cases w' with a' b',
   exact (eq_prop (@inl_eq A B a a')⁻¹ (H₁ a a') p q), -- inl a = inl a'
   exact (eq_prop (@inlr_eq A B a b')⁻¹ (λ x y : lift 𝟬, empty.rec_on _ (down x)) p q), -- inl a = inr b'
  cases w' with a' b',
   exact sorry, -- same as above, but requires a mirror proof of `sum_eq` fixing inr on the right,
   exact sorry -- which is straightfoward and boring
 end
 
 -- Corollary (𝟮 is a set)

 definition bool_is_set :
     isSet 𝟮 :=
 eq_set bool_eq_unit_unit⁻¹ (sum_preserves_sets unit_is_set unit_is_set)
 
 -- Exercise 3.20 (see `contr_eq_ii` above)
 
 --
