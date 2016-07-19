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

  definition I : Type₀ := quotient (λ (x y : 𝟮), x=ff × y=tt)  

  definition zero : I := class_of (λ (x y : 𝟮), x=ff × y=tt) ff

  definition one : I := class_of (λ (x y : 𝟮), x=ff × y=tt) tt

  definition seg : zero = one := eq_of_rel (λ (x y : 𝟮), x=ff × y=tt) (idp,idp)

 -- Induction principle

  definition rec {P : I → Type.{i}} (b₀ : P zero) (b₁ : P one) (s : b₀ =⟨seg⟩ b₁) (x : I) : P x :=
   @quotient.rec 𝟮 (λ (x y : 𝟮), x=ff × y=tt) P (λ (a : 𝟮), bool.rec_on a b₀ b₁)
   (λ a a', (bool.rec_on a  (bool.rec_on a' (λ H, prod.rec_on H (λ H₁ H₂, empty.rec _ (ff_ne_tt H₂)))
    (λ H, prod.rec_on H (λ H₁ H₂, change_path ((λ p q, eq.rec (eq.rec idp q) p) 
     (bool_is_set ff ff idp H₁) (bool_is_set tt tt idp H₂)) (pathover_of_tr_eq s) )  )) 
    (bool.rec_on a' (λ H, prod.rec_on H (λ H₁ H₂, empty.rec _ (ff_ne_tt H₂)))
    (λ H, prod.rec_on H (λ H₁ H₂, empty.rec _ (ff_ne_tt H₁⁻¹)))) ) ) x

 -- Some lemmas (will be organized later)
 
  definition reflseg1 (H₁ : (refl (refl tt)) = (bool_is_set tt tt (refl tt) (refl tt))) :
     (refl seg) = (eq.rec (refl seg) (bool_is_set tt tt (refl tt) (refl tt))) :=
 transport _ H₁ idp

 definition lemma234 (H₁ : (refl (refl tt)) = (bool_is_set tt tt (refl tt) (refl tt)))
   (H₂ : (refl (refl ff)) = (bool_is_set ff ff (refl ff) (refl ff))) :
     refl seg = eq.rec (eq.rec (refl seg) (bool_is_set tt tt (refl tt) (refl tt))) (bool_is_set ff ff (refl ff) (refl ff)) :=
 transport _ (reflseg1 H₁) (transport _ H₂ idp)

  definition testelem2 {P : I → Type.{i}} (b₀ : P zero) (b₁ : P one) (s : b₀ =⟨seg⟩ b₁) :
     pathover (λ (a : eq zero one), pathover P b₀ a b₁) (pathover_of_tr_eq s)
    (eq.rec (eq.rec idp (bool_is_set tt tt (refl tt) (refl tt))) (bool_is_set ff ff (refl ff) (refl ff))) (pathover_of_tr_eq s) :=
 (change_path (lemma234 
    (set_is_1_type bool_is_set tt tt (refl tt) (refl tt) (refl (refl tt)) (bool_is_set tt tt (refl tt) (refl tt)))
    (set_is_1_type bool_is_set ff ff (refl ff) (refl ff) (refl (refl ff)) (bool_is_set ff ff (refl ff) (refl ff)))) 
  (@pathover.idpatho (zero = one) seg (λ (a : eq zero one), pathover P b₀ a b₁) (pathover_of_tr_eq s)) )

 definition teste {P : I → Type.{i}} (b₀ : P zero) (b₁ : P one) (s : b₀ =⟨seg⟩ b₁) :
     (λ a a', (bool.rec_on a  (bool.rec_on a' (λ H, prod.rec_on H (λ H₁ H₂, empty.rec _ (ff_ne_tt H₂)))
    (λ H, prod.rec_on H (λ H₁ H₂, change_path ((λ p q, eq.rec (eq.rec (refl seg) q) p) 
     (bool_is_set ff ff (refl ff) H₁) (bool_is_set tt tt (refl tt) H₂)) (pathover_of_tr_eq s) )  )) 
    (bool.rec_on a' (λ H, prod.rec_on H (λ H₁ H₂, empty.rec _ (ff_ne_tt H₂)))
    (λ H, prod.rec_on H (λ H₁ H₂, empty.rec _ (ff_ne_tt H₁⁻¹)))) ) ) ff tt (refl ff,refl tt) = pathover_of_tr_eq s :=
 begin
   esimp at *, apply transport, exact (ua (pathover_pathover_path ((eq.rec (eq.rec idp (bool_is_set tt tt idp idp)) (bool_is_set ff ff idp idp))) (pathover_of_tr_eq s) (pathover_of_tr_eq s))), exact (testelem2 b₀ b₁ s)
 end



 -- Lemma 6.3.1 (Interval is contractible)

  definition is_contr :
      isContr I :=
  ⟨ zero , sorry⟩

 end interval
 
 --
