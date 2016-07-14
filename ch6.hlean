/-
Copyright (c) 2016 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");

Theorems and exercises of the HoTT book (Chapter 6)
-/

import .ch1 .ch2 .ch3 .ch4 init.hit

open eq prod unit bool sum sigma ua funext nat lift quotient

/- ************************************** -/
/-    Ch.6 Higher Inductive Types         -/
/- ************************************** -/

 variables {A B C X Z: Type} 

 universe variables i l

/- §6.1 (Introduction)  -/

 -- Definition of S¹

 namespace circle

  definition S1 : Type₀ := quotient (λ (x y : 𝟭), 𝟭)

  definition base : S1 := class_of (λ (x y : 𝟭), 𝟭) ⋆

  definition loop : base = base := eq_of_rel (λ (x y : 𝟭), 𝟭) ⋆

 -- Notation for S¹

  notation `S¹` := S1
 
 --

 /- §6.2 (Induction principles and dependent paths) -/

 -- Induction principle for S¹

 definition rec {P : S¹ → Type.{i}} (b : P base) (l : b =⟨loop⟩ b) (x : S¹) : P x :=
  @quotient.rec 𝟭 (λ (x y : 𝟭), 𝟭) P (λ (a : 𝟭), unit.rec_on a b)
 (λ a a' H, unit.rec_on H (unit.rec_on a (unit.rec_on a' (pathover_of_tr_eq l)))) x

 definition apd_rec_eq_loop {P : S¹ → Type}  (b : P base) (l : b =⟨loop⟩ b) :
     apd (λ x, rec b l x) loop = l :=
 have H : apdo (λ x, rec b l x) loop = (pathover_of_tr_eq l), from
   (@quotient.rec_eq_of_rel 𝟭 (λ (x y : 𝟭), 𝟭) P (λ (a : 𝟭), unit.rec_on a b)
   (λ a a' H, unit.rec_on H (unit.rec_on a (unit.rec_on a' (pathover_of_tr_eq l))))) ⋆ ⋆ ⋆,
 (apdo_to_apd (λ x, rec b l x) loop)⁻¹ ⬝ ap tr_eq_of_pathover H ⬝
 (@cancel_tr_pathover S¹ base base P loop b b l)

 definition rec_on {P : S¹ → Type.{i}} (x : S¹) (b : P base) (l : b =⟨loop⟩ b) : P x :=
  rec b l x

 definition apd_rec_on_eq_loop {P : S¹ → Type}  (b : P base) (l : b =⟨loop⟩ b) :
     apd (λ x, rec_on x b l) loop = l :=
 apd_rec_eq_loop b l

 -- Lemma 6.2.5 (Non-dependent recursor)

 definition ndrec (a : A) (p : a = a) (x : S¹) : A :=
  @circle.rec_on (λ x, A) x a (concat (trans_const loop a) p)

 definition ndrec_ap (a : A) (p : a = a) :
     ap (ndrec a p) loop = p :=
 have H : trans_const loop a ⬝ ap (ndrec a p) loop = trans_const loop a ⬝ p, from
   (apd_eq_trans_const_ap (λ x, A) (ndrec a p) loop)⁻¹ ⬝
   (@apd_rec_on_eq_loop (λ x, A) a (trans_const loop a ⬝ p)),
 unwhisker_left (trans_const loop a) H

 -- Lemma 6.2.8 (Uniqueness principle)
 
 definition uniq (f g : S¹ → A) (p : f base = g base) (q : ap f loop =⟨p⟩ ap g loop) :
     Π (x : S¹), f x = g x :=
 λ x, rec_on x p (id_trans_fun f g loop p -- thm 2.11.3
  ⬝ ( (conc_assoc _ _ _)⁻¹ ⬝  (( (ap f loop)⁻¹ ⬝ₗ -- associativity
 (pr1 (id_trans_equiv p (ap f loop) (ap g loop)) q)⁻¹) ⬝ -- thm 2.11.5
  conc_assoc _ _ _ ⬝ (left_inv (ap f loop) ⬝ᵣ p) ⬝ (lu p)⁻¹)) ) -- cancellation (ap f loop)⁻¹

 -- Universal property

 definition fun_to_sig {A : Type} :
     (S¹ → A) → (Σ (x : A), x = x) :=
 λ g, ⟨ g base, ap g loop ⟩

 definition sig_to_fun {A : Type} :
     (Σ (x : A), x = x) → (S¹ → A) :=
 λ w x, ndrec (pr1 w) (pr2 w) x

 definition upcomp {A : Type} (w : Σ (x : A), x = x) :
   fun_to_sig (sig_to_fun w) = w :=
 sigma_eq ⟨ idp, ndrec_ap _ _⟩

 definition upuniq {A : Type} (f : S¹ → A) :
   sig_to_fun (fun_to_sig f) = f :=
 funext (λ x, rec_on x idp 
  (show (idp =⟨loop⟩ idp), from
    id_trans_fun (sig_to_fun (fun_to_sig f)) f loop idp -- thm 2.11.3
    ⬝ (conc_assoc (ap (sig_to_fun (fun_to_sig f)) loop)⁻¹ idp (ap f loop))⁻¹  --} cancel idp 
    ⬝ ((ap (sig_to_fun (fun_to_sig f)) loop)⁻¹ ⬝ₗ (lu (ap f loop))⁻¹) ⬝        --} 
    (ap path_inv (ndrec_ap (f base) (ap f loop)) ⬝ᵣ (ap f loop)) ⬝ -- since sig_to_fun (fun_to_sig f) ▻ ndrec (f base) (ap f loop)
    left_inv (ap f loop) -- _⁻¹ ⬝ _ = idp
  ))

 -- Lemma 6.2.9 (Universal property)

 definition up (A : Type) :
     (S¹ → A) ≃ (Σ (x : A), x = x) :=
 ⟨fun_to_sig, ( ⟨sig_to_fun, upcomp⟩ , ⟨sig_to_fun, upuniq⟩ ) ⟩

 end circle

 --

/- §6.3 (The interval)  -/

 namespace interval

  definition I : Type₀ := quotient (λ (x y : 𝟮), 𝟭)

  definition zero : I := class_of (λ (x y : 𝟮), 𝟭) ff

  definition one : I := class_of (λ (x y : 𝟮), 𝟭) tt

  definition seg : zero = one := eq_of_rel (λ (x y : 𝟮), 𝟭) ⋆ 

 end interval
 
 --
