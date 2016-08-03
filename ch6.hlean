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
    (λ H, prod.rec_on H (λ H₁ H₂, change_path ((λ p q, eq.rec (eq.rec (refl seg) q) p) 
     (bool_is_set ff ff (refl ff) H₁) (bool_is_set tt tt (refl tt) H₂)) (pathover_of_tr_eq s) )  )) 
    (bool.rec_on a' (λ H, prod.rec_on H (λ H₁ H₂, empty.rec _ (ff_ne_tt H₂)))
    (λ H, prod.rec_on H (λ H₁ H₂, empty.rec _ (ff_ne_tt H₁⁻¹)))) ) ) x

  definition apdo_rec_eq_seg {P : I → Type.{i}} (b₀ : P zero) (b₁ : P one) (s : b₀ =⟨seg⟩ b₁) :
      apdo (λ x, rec b₀ b₁ s x) seg = (pathover_of_tr_eq s) :=
  (@quotient.rec_eq_of_rel 𝟮 (λ (x y : 𝟮), x=ff × y=tt) P (λ (a : 𝟮), bool.rec_on a b₀ b₁)
   (λ a a', (bool.rec_on a  (bool.rec_on a' (λ H, prod.rec_on H (λ H₁ H₂, empty.rec _ (ff_ne_tt H₂)))
   (λ H, prod.rec_on H (λ H₁ H₂, change_path ((λ p q, eq.rec (eq.rec (refl seg) q) p) 
   (bool_is_set ff ff (refl ff) H₁) (bool_is_set tt tt (refl tt) H₂)) (pathover_of_tr_eq s) )  )) 
   (bool.rec_on a' (λ H, prod.rec_on H (λ H₁ H₂, empty.rec _ (ff_ne_tt H₂)))
    (λ H, prod.rec_on H (λ H₁ H₂, empty.rec _ (ff_ne_tt H₁⁻¹)))) ) ) ff tt (refl ff,refl tt)) ⬝  -- concat
  (show _ = pathover_of_tr_eq s, from
    (transport _ (ua (pathover_pathover_path _ _ _) )
     ((λ H₁ H₂, (change_path (transport _
     (show refl seg = (eq.rec (refl seg) (bool_is_set tt tt (refl tt) (refl tt))), from 
       eq.rec_on H₁ idp) 
      (transport _ H₂ idp) )))
    (set_is_1_type bool_is_set tt tt (refl tt) (refl tt) (refl (refl tt)) (bool_is_set tt tt (refl tt) (refl tt))) -- H₁
    (set_is_1_type bool_is_set ff ff (refl ff) (refl ff) (refl (refl ff)) (bool_is_set ff ff (refl ff) (refl ff))) -- H₂
     (@pathover.idpatho (zero = one) seg (λ (a : zero = one), pathover P b₀ a b₁) (pathover_of_tr_eq s)) )) )

  definition apd_rec_eq_seg {P : I → Type} (b₀ : P zero) (b₁ : P one) (s : b₀ =⟨seg⟩ b₁) :
      apd (λ x, rec b₀ b₁ s x) seg = s :=
  (apdo_to_apd (λ x, rec b₀ b₁ s x) seg)⁻¹ ⬝ ap tr_eq_of_pathover (apdo_rec_eq_seg b₀ b₁ s) ⬝
  (@cancel_tr_pathover I zero one P seg b₀ b₁ s)

  definition rec_on {P : I → Type.{i}} (x : I) (b₀ : P zero) (b₁ : P one) (s : b₀ =⟨seg⟩ b₁) : P x :=
  rec b₀ b₁ s x

  definition apd_rec_on_eq_loop {P : I → Type} (b₀ : P zero) (b₁ : P one) (s : b₀ =⟨seg⟩ b₁) :
      apd (λ x, rec_on x b₀ b₁ s) seg = s :=
  apd_rec_eq_seg b₀ b₁ s

  -- Lemma 6.3.1 (Interval is contractible)

  definition is_contr :
      isContr I :=
  ⟨ zero , λ x, rec_on x (refl zero) seg (eq.rec_on seg (refl (refl zero))) ⟩

 -- Lemma 6.3.2

 definition to_funext (f g : A → B) (p : Π (x : A), f x = g x) :
     f = g :=
 let p_tilde :=  λ x i, rec_on i (f x) (g x) (trans_const seg (f x) ⬝ p x) in
 let q := λ i, rec_on i (λ x, p_tilde x i) (λ x, p_tilde x i) (trans_const seg _) in
 ap q seg 

 -- Non-dependent recursor

 definition ndrec (a₀ a₁ : A) (s : a₀ = a₁) (x : I) : A :=
  @interval.rec_on (λ x, A) x a₀ a₁ (concat (trans_const seg a₀) s)

 definition ndrec_ap (a₀ a₁ : A) (s : a₀ = a₁) (x : I) :
     ap (ndrec a₀ a₁ s) seg = s :=
 have H : trans_const seg a₀ ⬝ ap (ndrec a₀ a₁ s) seg = trans_const seg a₀ ⬝ s, from
   (apd_eq_trans_const_ap (λ x, A) (ndrec a₀ a₁ s) seg)⁻¹ ⬝
   ((@apd_rec_on_eq_seg (λ x, A) a₀ a₁ (trans_const seg a₀ ⬝ s))), 
 unwhisker_left (trans_const seg a₀) H 

 end interval

 --

/- §6.4 (Circles and spheres)  -/

 open circle

 -- Lemma 6.4.1

 definition loop_neq_refl :
     loop ≠ refl base :=
 begin
  intro f, 
  apply universe_not_set,
    intro A B p q,
    induction q,
    exact ((transport _ f (ndrec_ap A p))⁻¹ ⬝ idp)
 end

 -- Lemma 6.4.2

 definition neq_refl :
     Σ (f : Π (x : S¹), x = x), f ≠ (λ x, refl x) :=
 ⟨ λ x, circle.rec_on x loop (id_trans_iii loop loop ⬝ ((left_inv loop ⬝ᵣ loop) ⬝ (lu loop)⁻¹)),
  λ f, loop_neq_refl ((happly f) base)⟩ 

 -- Corollary 6.4.3

 -- Due to the lack of cumulative hierarchy of universes, we will need a few lemmas about lifting

 definition lift_eq (A : Type) :
     A ≃ (lift A) :=
 ⟨up, (⟨down,up_down⟩,⟨down,down_up⟩)⟩

 definition univalence_of_ua (A B : Type.{i}) :
     (A = B) = (lift (A ≃ B)) :=
 ua ((lift_eq (A ≃ B))⁻¹ ∘ (⟨idtoeqv, @univalence A B⟩)⁻¹)⁻¹ 

 definition isSet_to_lift_isSet (A : Type) :
     (isSet A) → (isSet (lift A)) :=
 have get_ap : Π (f : isSet A) (a b : A) (p q : up a = up b), ap (up ∘ down) p = ap (up ∘ down) q, from
   (λ f a b p q, (ap_func_iii down up p)⁻¹ ⬝ 
   ((ap (ap up) (f (down (up a)) (down (up b))
    (ap down p) (ap down q))) ⬝ (ap_func_iii down up q) )),
 λ f x y, lift.rec_on x (λ a, lift.rec_on y 
   (λ b p q, (ap_func_iv p)⁻¹ ⬝ (transport (λ (a : lift A → lift A), ap a p = ap a q) 
     (funext up_down) (get_ap f a b p q)) ⬝ (ap_func_iv q)  ))

 definition lift_isSet_to_isSet (A : Type) :
     (isSet (lift A)) → (isSet A) :=
 have get_ap : Π (f : isSet (lift A)) (x y : A) (p q : x = y), ap (down ∘ up) p = ap (down ∘ up) q, from
   (λ f x y p q, (ap_func_iii up down p)⁻¹ ⬝ 
    ap (ap down) (f (up x) (up y) (ap up p) (ap up q)) ⬝ 
    (ap_func_iii up down q)),
 λ f x y p q, (ap_func_iv p)⁻¹ ⬝ transport (λ (a : A → A), ap a p = ap a q) 
  (funext down_up) (get_ap f x y p q) ⬝ (ap_func_iv q)

 definition neg_set_to_lift (A : Type) :
     ¬ (isSet A) → ¬ (isSet (lift A)) :=
 λ g f, g (lift_isSet_to_isSet A f)

 -- We start the proof showing the following:

 definition id_circle_not_prop :
     ¬ isProp (id S¹ = id S¹) :=
 transport (λ X, ¬ (isProp X)) (ua (⟨happly, fun_extensionality⟩)⁻¹) 
 (show ¬ isProp (Π (x : S¹), x = x), from
  (λ f, (pr2 neq_refl) (f (pr1 neq_refl) (λ x, refl x))))

 -- Lemma used below (The first projection of the dependent pair given by
 -- the identity of equivalences induced by identity of functions (first projection) equals itself)

 definition pr1_prop_sigma_eq_on_eqv_eq {A B : Type.{i}} (e₁ e₂ : Σ (f : A → B), isequiv f) (p : pr1 e₁ = pr1 e₂) :
     pr1 (ap_sigma ((prop_sigma_eq biinv_is_prop e₁ e₂ ) p)) = p :=
 begin
   induction e₁ with f e, induction e₂, esimp at *,
   induction (ua ⟨f,e⟩), induction p,
   exact (ap pr1 (sigma_comp _))
 end

 definition eqv_circle_not_Set :
     ¬ isSet (S¹ ≃ S¹) :=
 λ f, (λ g, id_circle_not_prop 
  (show isProp (id S¹ = id S¹), from
    (λ p q,
      let H := (g ((prop_sigma_eq biinv_is_prop (idtoeqv (refl S¹)) (idtoeqv (refl S¹))) p)
               ((prop_sigma_eq biinv_is_prop (idtoeqv (refl S¹)) (idtoeqv (refl S¹))) q)) in
      let α := pr1_prop_sigma_eq_on_eqv_eq (idtoeqv (refl S¹)) (idtoeqv (refl S¹)) in
   calc
     p = pr1 (ap_sigma (prop_sigma_eq biinv_is_prop _ _ p)) : α p
     ... = pr1 (ap_sigma (prop_sigma_eq biinv_is_prop _ _ q)) : pr1 (transport (λ x, x) (ua (path_sigma _ _)) H)
     ... = q : α q )
   ) )
 (f (idtoeqv (refl S¹)) (idtoeqv (refl S¹)))

 -- The universe is not an 1 type

 definition universe_not_1_type :
    ¬ is_1_Type (Type₀) :=
 λ f, (transport (λ X, ¬ (isSet X)) (univalence_of_ua S¹ S¹)⁻¹ (neg_set_to_lift _ eqv_circle_not_Set)) (f S¹ S¹)
 
 -- We define the 2-sphere using suspensions, defined in the next section,
 -- For now we define ap2 and transport2

 -- Lemma 6.4.4

 definition ap2 (f : A → B) {x y : A} {p q : x = y} (r : p = q) :
     ap f p = ap f q :=
 eq.rec idp r

 definition transport2 (P : A → Type) {x y : A} {p q : x = y} (r : p = q) :
     transport P p = transport P q :=
 eq.rec idp r

--

 /- §6.5 (Suspensions)  -/

 namespace suspension

  definition susp (A : Type) : Type := quotient (λ (x y : 𝟭+𝟭), A × (x=(@inl 𝟭 𝟭 ⋆) × y=(@inr 𝟭 𝟭 ⋆)) ) --(λ (x y : 𝟮), (x=ff × y=tt) )

  definition n {A : Type} : susp A := class_of (λ (x y : 𝟭+𝟭), A × (x=(inl ⋆) × y=(inr ⋆)) ) (@inl 𝟭 𝟭 ⋆)

  definition s {A : Type} : susp A := class_of (λ (x y : 𝟭+𝟭), A × (x=(inl ⋆) × y=(inr ⋆)) ) (@inr 𝟭 𝟭 ⋆)

  definition merid {A : Type} (a : A) : @n A = @s A := --eq_of_rel (λ (x y : 𝟮), x=ff × y=tt) (refl ff, refl tt)
   eq_of_rel (λ (x y : 𝟭+𝟭), A × (x=(inl ⋆) × y=(inr ⋆)) ) (a, (refl (inl ⋆),refl (inr ⋆)))

  -- Induction principle for suspensions
 
  definition rec {A : Type} {P : susp A → Type.{i}} (bₙ : P n) (bₛ : P s) (m : Π (a : A), bₙ =⟨merid a⟩ bₛ) (x : susp A) : P x :=
   @quotient.rec (𝟭+𝟭) (λ (x y : 𝟭+𝟭), A × (x=(inl ⋆) × y=(inr ⋆)) ) P
    (λ (a : 𝟭+𝟭), sum.rec_on a (λ u, unit.rec_on u bₙ) (λ u, unit.rec_on u bₛ))
    begin
      intro a a' H, induction H with H₁ H₂, induction a, induction a' with a',
       esimp at *, induction a, induction a',
        exact (empty.rec_on _ (down (pr1 (sum_equiv (inr ⋆)) (pr2 (H₂))))),
       esimp at *, induction a, induction a_1,
        begin
         apply change_path,
           exact (transport (λ (a : A × inl ⋆ = inl ⋆ × inr ⋆ = inr ⋆), 
              merid H₁ = eq_of_rel (λ (x y : 𝟭 + 𝟭), A × x = inl ⋆ × y = inr ⋆) a) (show (H₁, (refl (inl ⋆),refl (inr ⋆))) = (H₁,H₂),
            from 
              pair_eq (refl H₁, (pair_eq (transport isSet (ua bool_eq_unit_unit) bool_is_set (inl ⋆) (inl ⋆) (refl (inl ⋆)) (pr1 H₂),
               transport isSet (ua bool_eq_unit_unit) bool_is_set (inr ⋆) (inr ⋆) (refl (inr ⋆)) (pr2 H₂)))  )
              ) idp),
         exact (pathover_of_tr_eq (m H₁))
        end,
       esimp at *, induction a, induction a', induction a, esimp at *,
        exact (empty.rec_on _ (down (pr1 (sum_equiv (inr ⋆)) (pr2 (H₂))))),
      induction a, esimp at *,
        exact (empty.rec_on _ (down (pr1 (sum_equiv (inr ⋆)) (pr1 (H₂))⁻¹ )))
    end x

  definition apdo_rec_eq_merid {P : susp A → Type} (bₙ : P n) (bₛ : P s) (m : Π (a : A), bₙ =⟨merid a⟩ bₛ) (a : A) :
     apdo (λ x, rec bₙ bₛ m x) (merid a) = (pathover_of_tr_eq (m a)) :=
  let idp_eq_pair_etc :=
     pr1 (typeq_sym (path_pair idp _)) 
     (set_is_1_type (transport isSet (ua.ua bool_eq_unit_unit) bool_is_set) (@inl 𝟭 𝟭 ⋆) (inl ⋆) (refl (inl ⋆)) (refl (inl ⋆)) idp 
     (transport isSet (ua bool_eq_unit_unit) bool_is_set (inl star) (inl star) (refl (inl star)) (refl (inl star)))
      ⬝ (prod_beta1 _)⁻¹ , 
     set_is_1_type (transport isSet (ua.ua bool_eq_unit_unit) bool_is_set) (@inr 𝟭 𝟭 ⋆) (inr ⋆) (refl (inr ⋆)) (refl (inr ⋆)) idp 
     (transport isSet (ua bool_eq_unit_unit) bool_is_set (inr ⋆) (inr ⋆) (refl (inr ⋆)) (refl (inr ⋆))) ⬝ (prod_beta2 _)⁻¹) in
  (@quotient.rec_eq_of_rel (𝟭+𝟭) (λ (x y : 𝟭+𝟭), A × (x=(inl ⋆) × y=(inr ⋆)) ) P
   (λ (a : 𝟭+𝟭), sum.rec_on a (λ u, unit.rec_on u bₙ) (λ u, unit.rec_on u bₛ))
    _ (@inl 𝟭 𝟭 ⋆) (@inr 𝟭 𝟭 ⋆) (a,(refl (inl ⋆), refl (inr ⋆))) ) ⬝ -- concat
  (show _ = pathover_of_tr_eq (m a), from
   (transport _ (ua (pathover_pathover_path _ _ _) ) 
     (change_path 
       (show refl (merid a) = _, from 
           transport _ (idp_eq_pair_etc) idp
        )
       (pathover.idpatho (pathover_of_tr_eq (m a)))) )  
   )

  definition apd_rec_eq_merid {P : susp A → Type} (bₙ : P n) (bₛ : P s) (m : Π (a : A), bₙ =⟨merid a⟩ bₛ) (a : A) :
      apd (λ x, rec bₙ bₛ m x) (merid a) = m a :=
  (apdo_to_apd (λ x, rec bₙ bₛ m x) (merid a))⁻¹ ⬝ ap tr_eq_of_pathover (apdo_rec_eq_merid bₙ bₛ m a) ⬝
  (@cancel_tr_pathover (susp A) n s P (merid a) bₙ bₛ (m a))

  definition rec_on {A : Type} {P : susp A → Type.{i}} (x : susp A) (bₙ : P n) (bₛ : P s) (m : Π (a : A), bₙ =⟨merid a⟩ bₛ) : P x :=
  rec bₙ bₛ m x

  definition apd_rec_on_eq_merid {P : susp A → Type} (bₙ : P n) (bₛ : P s) (m : Π (a : A), bₙ =⟨merid a⟩ bₛ) (a : A) :
      apd (λ x, rec_on x bₙ bₛ m) (merid a) = m a :=
  apd_rec_eq_merid bₙ bₛ m a

 -- Non-dependent recursor

 definition ndrec (b₀ b₁ : B) (m : Π (a : A), b₀ = b₁) (x : susp A) : B :=
  @suspension.rec_on A (λ x, B) x b₀ b₁ (λ a, concat (trans_const (merid a) b₀) (m a))

 definition ndrec_ap (b₀ b₁ : B) (m : Π (a : A), b₀ = b₁) (a : A) :
     ap (ndrec b₀ b₁ m) (merid a) = m a :=
 have H : trans_const (merid a) b₀ ⬝ ap (ndrec b₀ b₁ m) (merid a) = trans_const (merid a) b₀ ⬝ m a, from
   (apd_eq_trans_const_ap (λ x, B) (ndrec b₀ b₁ m) (merid a))⁻¹ ⬝ 
   ((@apd_rec_on_eq_merid A (λ x, B) b₀ b₁ (λ a, trans_const (merid a) b₀ ⬝ m a)) a), 
 unwhisker_left (trans_const (merid a) b₀) H 

 -- Lemma 6.5.1

 definition susp_bool_to_circle :
    susp 𝟮 → S¹ :=
 λ x, suspension.ndrec base base (λ a : 𝟮, bool.rec_on a loop (refl base)) x

 definition circle_to_susp_bool :
    S¹ →  susp 𝟮 :=
 λ x, circle.ndrec n (concat (merid ff) (merid tt)⁻¹) x

 definition susp_bool_to_circle_eq :
    susp 𝟮 ≃ S¹ :=
 ⟨susp_bool_to_circle,
  (⟨circle_to_susp_bool, λ x, circle.rec_on x (refl base)
    ((id_trans_fun (susp_bool_to_circle ∘ circle_to_susp_bool) (id S¹) loop (refl base)) ⬝ 
      (conc_assoc _ _ _)⁻¹ ⬝ ((ap (susp_bool_to_circle ∘ circle_to_susp_bool) loop)⁻¹ ⬝ₗ 
      (refl base ⬝ₗ (ap_func_iv loop)) ⬝ (lu loop)⁻¹) ⬝
      ((ap path_inv (((ap_func_iii circle_to_susp_bool susp_bool_to_circle loop)⁻¹ ⬝ 
      (ap (ap susp_bool_to_circle) (circle.ndrec_ap n (merid ff ⬝ (merid tt)⁻¹))) ⬝ 
      (ap_func_i susp_bool_to_circle (merid ff) (merid tt)⁻¹)) ⬝ 
      ((ap susp_bool_to_circle (merid ff) ⬝ₗ (ap_func_ii susp_bool_to_circle (merid tt)) ⬝ 
       (ap path_inv (suspension.ndrec_ap base base (λ a, bool.rec_on a loop (refl base)) tt))) ⬝ 
         (suspension.ndrec_ap base base (λ a, bool.rec_on a loop (refl base)) ff)))) ⬝ᵣ loop) ⬝ left_inv loop )
     ⟩,
    ⟨circle_to_susp_bool, 
      λ x, suspension.rec_on x (refl n) (merid tt) (λ b, bool.rec_on b 
       ((id_trans_fun (circle_to_susp_bool ∘ susp_bool_to_circle) (id (susp 𝟮)) (merid ff) (refl n)) ⬝ -- ff
        ((((ap path_inv ((ap_func_iii susp_bool_to_circle circle_to_susp_bool (merid ff))⁻¹ ⬝
        (ap (ap circle_to_susp_bool) (suspension.ndrec_ap base base (λ a, bool.rec_on a loop (refl base)) ff)) ⬝ 
        (circle.ndrec_ap n (concat (merid ff) (merid tt)⁻¹))) ⬝
        (con_inv (merid ff) (merid tt)⁻¹) ⬝ (inv_canc (merid tt) ⬝ᵣ (merid ff)⁻¹)) ⬝ᵣ (refl n)) ⬝ᵣ 
        (ap (id (susp 𝟮)) (merid ff))) ⬝
        ((ru (concat (merid tt) (merid ff)⁻¹)) ⬝ᵣ (ap (id (susp 𝟮)) (merid ff)))⁻¹ ⬝ 
        (conc_assoc (merid tt) (merid ff)⁻¹ (ap (id (susp 𝟮)) (merid ff)))⁻¹  ⬝ 
        ((merid tt) ⬝ₗ ((merid ff)⁻¹ ⬝ₗ (ap_func_iv (merid ff)))) ⬝ 
         (merid tt ⬝ₗ (left_inv (merid ff)))) )
       ((id_trans_fun (circle_to_susp_bool ∘ susp_bool_to_circle) (id (susp 𝟮)) (merid tt) (refl n)) ⬝ -- tt
        ((((((ap path_inv ((ap_func_iii susp_bool_to_circle circle_to_susp_bool (merid tt))⁻¹ ⬝ 
        (ap (ap circle_to_susp_bool) (suspension.ndrec_ap base base 
         (λ a, bool.rec_on a loop (refl base)) tt)))) ⬝ᵣ (refl n)) ⬝
        (lu (refl n))⁻¹) ⬝ᵣ (ap (id (susp 𝟮)) (merid tt)))) ⬝ 
        (lu (ap (id (susp 𝟮)) (merid tt)))⁻¹ ⬝ 
         ap_func_iv (merid tt)) )
    ) ⟩)⟩

 -- n-Spheres definition

 definition n_sphere : ℕ → Type₀
 | n_sphere zero := 𝟮
 | n_sphere (succ k) := susp (n_sphere k)

 -- Lemma 6.5.3

 definition Map (A : Type) (a₀ : A) (B : Type) (b₀ : B) : Type :=
  Σ (f : A → B), f (a₀) = b₀ 

 definition map_to_fun (A : Type) (B : Type) (b₀ : B) :
     Map (A + 𝟭) (inr ⋆) B b₀ → (A → B) :=
 λ m a, (pr1 m) (inl a)

 definition fun_to_map (A : Type) (B : Type) (b₀ : B) :
     (A → B) → (Map (A + 𝟭) (inr ⋆) B b₀)  :=
 λ f, ⟨λ x, @sum.rec_on A 𝟭 (λ (x : A + 𝟭), B) x f (λ u, b₀), (refl b₀) ⟩

 definition map_eq_fun (A : Type) (B : Type) (b₀ : B) :
     Map (A + 𝟭) (inr ⋆) B b₀ ≃ (A → B) :=
 ⟨map_to_fun A B b₀, (⟨fun_to_map A B b₀,(λ f, refl f)⟩ , 
   ⟨fun_to_map A B b₀ , 
     λ m, sigma.rec_on m (λ f p,
      sigma_eq ⟨funext (λ x, @sum.rec_on A 𝟭 (λ (x : A + 𝟭), 
      @sum.rec_on A 𝟭 (λ (x : A + 𝟭), B) x (λ a, f (inl a)) (λ u, b₀) = f x)
      x (λ a, refl (f (inl a)) ) (λ u, unit.rec_on u p⁻¹)), 
         eq.rec_on p
         (show (transport (λ (f' : A + 𝟭 → B), f' (inr ⋆) = f (inr ⋆))
          (funext (λ (x : A + 𝟭), @sum.rec_on A 𝟭 (λ (x : A + 𝟭), 
          @sum.rec_on A 𝟭 (λ (x : A + 𝟭), B) x (λ a, f (inl a)) (λ u, f (inr ⋆)) = f x) 
          x (λ (a : A), refl (f (inl a))) (λ (u : 𝟭), unit.rec_on u (refl (f (inr star)))⁻¹ )))
          (refl (f (inr ⋆)))) = refl (f (inr ⋆)), from
             transport _ (show (λ (x : A + 𝟭), @sum.rec_on A 𝟭 (λ (x : A + 𝟭), B) x (λ a, f (inl a)) (λ u, f (inr ⋆)) ) = f, from
                begin apply funext, intro x, cases x, esimp at *, esimp at *, induction a, reflexivity end)
              (transport _ ((funext_uniq (refl _))⁻¹ ⬝ 
                (ap funext (begin apply funext, intro x, cases x, esimp at *, induction a, esimp at * end))) idp)
          ) 
       ⟩)
 ⟩ ) ⟩

  end suspension

---------

 namespace two_sphere

  definition S2 : Type₀ := quotient (λ (x y : 𝟭), S¹)

  definition base : S2 := class_of (λ (x y : 𝟭), S¹) ⋆

  definition reflb : base = base := eq_of_rel (λ (x y : 𝟭), S¹) circle.base

  definition surf_fun : S¹ → base = base := λ (x : S¹), eq_of_rel (λ (x y : 𝟭), S¹) x --(circle.ndrec circle.base loop x)

  definition surf : reflb = reflb := ap surf_fun loop

  -- Notation for S²

  notation `S²` := S2

  -- Lemma 6.4.4

  definition ap2 {x y : A} (f : A → B) {p q : x = y} (r : p = q) :
      ap f p = ap f q :=
  eq.rec idp r

  definition transport2 (P : A → Type) {x y : A} {p q : x = y} (r : p = q) :
      transport P p = transport P q :=
  eq.rec idp r

  definition apd2 {x y : A} {P : A → Type} (f : Π (x : A), P(x)) {p q : x = y} (r : p = q) :
      transport (λ (p : x = y), f x =⟨p⟩ f y) r (apd f p) = apd f q :=
  eq.rec (eq.rec idp p) r

  -- Induction principle for S²

  definition change_fam {x y : A} {P : A → Type.{i}} {Q : A → Type.{i}} (p : x = y) (u : P x) (v : P y) (f : Π (x : A), P x → Q x) 
  (α : P = Q) (H : transport P p u = v) : transport Q p (f x u) = (f y v) :=
  by induction p; induction α; esimp at *; apply (ap (f x) H)

  definition rec {P : S² → Type.{i}} (b : P base) (l : b =⟨reflb⟩ b) (s : l =⟨surf⟩ l) (x : S²) : P x :=
  @quotient.rec 𝟭 (λ (x y : 𝟭), S¹) P (λ (a : 𝟭), unit.rec_on a b)
 (λ a a' H, unit.rec_on a (unit.rec_on a' (circle.rec_on H
  (show pathover P b (eq_of_rel (λ (x y : 𝟭), S¹) circle.base) b, from (pathover_of_tr_eq l))
  (change_fam loop l l (λ x, pathover_of_tr_eq) 
   (funext (λ (a : S¹), (ua (@pathover_equiv_tr_eq S² P base base (eq_of_rel (λ (x y : 𝟭), S¹) a) b b))⁻¹))
   (transport (λ α, α = l) (trans_ap_fun surf_fun (λ (p : base = base), (transport P p b) = b) loop l)⁻¹ s) ) ) 
      )) x

 --
