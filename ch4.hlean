/-
Copyright (c) 2016 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");

Theorems and exercises of the HoTT book (Chapter 4)
-/

import .ch2 .ch3 

open eq prod unit bool sum sigma ua funext nat lift

/- ************************************** -/
/-    Ch.4 Equivalences                   -/
/- ************************************** -/

/- §4.1 (Quasi-inverses)  -/

 variables {A B C X Z: Type} 

 universe variables i j

 -- Lemma 4.1.1 

 -- Useful lemmas of preservation of equality by type formers

 definition prod_preserves_equiv {A B : Type.{i}} {A' B' : Type.{j}} (e₁ : A ≃ B) (e₂ : A' ≃ B') :
     A × A' ≃  B × B' :=
 by induction (ua e₁); induction (ua e₂); apply typeq_refl _

 definition sigma_preserves_equiv {X : Type} {A B : X → Type} (H : Π (x : X), A x ≃ B x ) :
     (Σ (x : X), A x)  ≃  Σ (x : X), B x :=
 let sigeq := λ w, ⟨(pr1 w), (pr1 (H (pr1 w))) (pr2 w) ⟩ in
 let siginv := λ w', ⟨(pr1 w'),
    pr1 (isequiv_to_qinv (pr1 (H (pr1 w'))) (pr2 (H (pr1 w')))) (pr2 w') ⟩ in
 have comp : sigeq ∘ siginv ~ id _, from
  λ w', sigma.rec_on w' (λ w1' w2', sigma_eq ⟨ refl w1',
  (pr1 (pr2 (isequiv_to_qinv (pr1 (H w1')) (pr2 (H w1'))))) w2' ⟩),
 have uniq : siginv ∘ sigeq ~ id _, from
  λ w, sigma.rec_on w (λ w1 w2, sigma_eq ⟨refl w1,
  (pr2 (pr2 (isequiv_to_qinv (pr1 (H w1)) (pr2 (H w1))))) w2 ⟩),
 ⟨sigeq, (⟨siginv, comp⟩, ⟨siginv, uniq⟩)⟩

 -- The "funext" version of quasi-inverse

 definition funext_qinv {A B : Type.{i}} (f : A → B) :
     (Σ (g : B → A), f ∘ g = id B × g ∘ f = id A)  ≃  Σ (g : B → A), f ∘ g ~ id B × g ∘ f ~ id A :=
 have pair_qinv :
   Π (f : A → B) (g : B → A), (f ∘ g = id B × g ∘ f = id A)  ≃  (f ∘ g ~ id B × g ∘ f ~ id A),
 from λ f g, prod_preserves_equiv ⟨happly, fun_extensionality⟩ ⟨happly, fun_extensionality⟩,
 sigma_preserves_equiv (pair_qinv f)
 
 -- Sigma commutes with the product type

 definition sig_prod_comm :     
     (Σ (g : A → A), (g = id A) × (g = id A))  ≃ (Σ (g : A → A) (p : g = id A), (g = id A)) :=
 let f_sig_prod := λ w, ⟨pr1 w, ⟨pr1 (pr2 w), pr2 (pr2 w)⟩⟩ in
 let g_sig_prod := λ h, ⟨ pr1 h, ( pr1 (pr2 h), pr2 (pr2 h) ) ⟩ in
 have η : Π (h : Σ (g : A → A) (p : g = id A), (g = id A)), f_sig_prod (g_sig_prod h) = h, from 
  begin intro h, cases h with h1 h2, cases h2, reflexivity end,
 have ε : Π (w : Σ (g : A → A), (g = id A) × (g = id A)), g_sig_prod (f_sig_prod w) = w, from 
  begin intro w, cases w with w1 w2, cases w2, reflexivity end,
 ⟨f_sig_prod, (⟨g_sig_prod,η⟩,⟨g_sig_prod,ε⟩)⟩

 -- Lemma 4.1.1

 definition qinv_eq {A B : Type.{i}} (e : A ≃ B) :
     qinv (pr1 e) ≃ (Π (x : A), x = x) :=
 have qinv_id : qinv (id A) ≃ (Π (x : A), x = x), from -- proof for f ≡ id, we will transport it over ua_comp
 ((funext_qinv (id A))⁻¹ ∘ sig_prod_comm) ∘ @sigma_assoc (A → A) (λ g, g = id A) (λ h, pr1 h = id A) ∘ 
 (contr_eq_ii (λ h, pr1 h = id A) (@path_contr_r (A → A) (id A))) ∘ ⟨@happly A _ (id A) (id A), fun_extensionality⟩,
 transport _ (ua_comp e) (eq.rec_on (ua e) qinv_id) -- follows by induction on (ua e) ⇒ pr1 e = pr1 (ua (refl A)) = id 

 --

 /- §4.2 (Half adjoint equivalences)  -/ 

 -- Definition 4.2.1 (Half adjoint equivalence)

 definition ishae (f : A → B) : Type :=
     Σ (g : B → A) (ε : f ∘ g ~ id B) (η : g ∘ f ~ id A), Π (x : A), ap f (η x) = ε (f x)

 -- Lemma 4.2.2 (The coherence conditions are logically equivalent)

 definition tau_implies_tau' {f : A → B} {g : B → A} (ε : f ∘ g ~ id B) (η : g ∘ f ~ id A) (τ : Π (x : A), ap f (η x) = ε (f x)) :
     Π (y : B), ap g (ε y) = η (g y) :=
 assume (y : B),
 have nat_ε : ap (f ∘ g) (ε y) = ε (f (g y)), from -- naturality of ε 
   ((ap (f ∘ g) (ε y)) ⬝ₗ (right_inv (ε y))⁻¹) ⬝ 
    conc_assoc (ap (f ∘ g) (ε y)) (ε y) (ε y)⁻¹ ⬝ 
    ((@hom_ap B B (f (g y)) y (f ∘ g) (id B) ε (ε y)) ⬝ᵣ (ε y)⁻¹) ⬝ 
    ((ε (f (g y)) ⬝ₗ ap_func_iv (ε y)) ⬝ᵣ (ε y)⁻¹) ⬝ 
    (conc_assoc (ε (f (g y))) (ε y) (ε y)⁻¹)⁻¹ ⬝ (ε (f (g y)) ⬝ₗ right_inv (ε y)),
 have ap_τ' : ap (g ∘ f) (ap g (ε y)) = ap (g ∘ f) (η (g y)), from 
   (ap_func_iii f g (ap g (ε y)))⁻¹ ⬝        -- we just instantiate τ with (g y) 
    ap (ap g) (ap_func_iii g f (ε y)) ⬝      -- and apply g
    ap (ap g) (nat_ε ⬝ (τ (g y))⁻¹) ⬝
    ap_func_iii f g (η (g y)),
 (ap_func_iv (ap g (ε y)))⁻¹ ⬝  -- cancelation of (g ∘ f) through transport along η
 transport (λ h, ap h (ap g (ε y)) = ap h (η (g y))) (funext η) ap_τ' ⬝
 ap_func_iv (η (g y))

 -- Theorem 4.2.3 (Having a Quasi-inverse implies a Half adjoint equivalence)

 -- Defining τ demands a great deal of computation, so we do it separetly to help the elaborator

 definition ap_ap_eq {x y : A} {p q : x = y} (f : A → B) (α : p = q) :
     ap f p = ap f q :=
 begin induction α, reflexivity end

 definition tau_coro244 (f : A → B) (g : B → A) (ε : f ∘ g ~ id B) (η : g ∘ f ~ id A) (a : A) :
     ap f (η (g (f a))) ⬝ ε (f a) = (ε (f (g (f a)))) ⬝ ap f (η a) :=
 ((ap_ap_eq f (@hom_ap_id A a (g ∘ f) η)) ⬝ᵣ (ε (f a))) ⬝     -- corollary 2.4.4 
 (((ap_ap_eq f (ap_func_iii f g (η a)))⁻¹ ⬝ (ap_func_iii g f (ap f (η a)))) ⬝ᵣ (ε (f a))) ⬝ -- lemma 2.2.2 (iv) [ap and ∘ commutes]
 (@hom_ap B B (f (g (f a))) (f a) (f ∘ g) (id B) ε (ap f (η a))) ⬝ -- application of lemma 2.4.3
 ((ε (f (g (f a)))) ⬝ₗ ap_func_iv (ap f (η a))) -- cancellation of id B

 definition comp1_423 (f : A → B) (g : B → A) (ε : f ∘ g ~ id B) (η : g ∘ f ~ id A) (a : A) :
     (ε (f (g (f a))))⁻¹ ⬝ (ε (f (g (f a)))) ⬝ ap f (η a) = ap f (η a) :=
 ((left_inv (ε (f (g (f a)))) ⬝ᵣ ap f (η a)) ⬝ (lu (ap f (η a)) )⁻¹)

 definition comp2_423 (f : A → B) (g : B → A) (ε : f ∘ g ~ id B) (η : g ∘ f ~ id A) (a : A) :
    (ε (f (g (f a))))⁻¹ ⬝ (ap f (η (g (f a))) ⬝ ε (f a)) = (ε (f (g (f a))))⁻¹ ⬝ ((ε (f (g (f a)))) ⬝ ap f (η a)) :=
 (ε (f (g (f a))))⁻¹  ⬝ₗ tau_coro244 f g ε η a

 definition comp3_423 (f : A → B) (g : B → A) (ε : f ∘ g ~ id B) (η : g ∘ f ~ id A) (a : A) :
   (ε (f (g (f a))))⁻¹ ⬝ ap f (η (g (f a))) ⬝ ε (f a) = (ε (f (g (f a))))⁻¹ ⬝ ((ε (f (g (f a)))) ⬝ ap f (η a)) :=
 (conc_assoc (ε (f (g (f a))))⁻¹ (ap f (η (g (f a)))) (ε (f a)) )⁻¹ ⬝  comp2_423 f g ε η a

 -- Definition of τ

 definition tau_qinv (f : A → B) (g : B → A) (ε : f ∘ g ~ id B) (η : g ∘ f ~ id A) :
     Π (a : A), ap f (η a) = (ε (f (g (f a))))⁻¹ ⬝ ap f (η (g (f a))) ⬝ ε (f a) :=
 λ a, (comp3_423 f g ε η a ⬝ conc_assoc (ε (f (g (f a))))⁻¹ (ε (f (g (f a)))) (ap f (η a)) ⬝ comp1_423 f g ε η a)⁻¹

 -- Theorem 4.2.3 

 definition qinv_to_ishae (f : A → B) :
     qinv f → ishae f :=
 λ e, sigma.rec_on e (λ g w, prod.rec_on w (λ ε η, ⟨g, ⟨ (λ b, (ε (f (g b)))⁻¹ ⬝ ap f (η (g b)) ⬝ ε b) , ⟨η, tau_qinv f g ε η ⟩⟩⟩ ))

 -- The type ishae is a mere proposition

 -- Definition 4.2.4 (Fiber of a map)

 definition fib (f : A → B) (y : B) : Type :=
   Σ (x : A), f x = y

 -- Lemma 4.2.5

 -- Preservation of equivalence by equality and equivalence of inverse paths

 definition eq_preserves_equiv {x y : A} (p q r : x = y) (α : p = q) : 
     (p = r) ≃ (q = r) :=
 by induction α; apply typeq_refl

 definition inv_is_equiv (x y : A) :  
     (x = y) ≃ (y = x) :=
 ⟨(λ p, p⁻¹), ( ⟨(λ p, p⁻¹), λ p, eq.rec idp p ⟩, ⟨(λ p, p⁻¹), λ p, eq.rec idp p ⟩)⟩

 -- This version of lu makes explicit our use of path_conc

 definition lu' {x y : A} (p : x = y) :     
     p = path_conc (refl x) p :=
 eq.rec_on p (refl (refl x)) 

-- Lemma 4.2.5

 definition fib_equiv (f : A → B) (y : B) (h h' : fib f y) :
     h = h' ≃ Σ (γ : pr1 h = pr1 h'), ap f γ ⬝ pr2 h' = pr2 h :=
 have H : Π γ, transport (λ (x : A), f x = y) (γ : pr1 h = pr1 h') (pr2 h) = pr2 h'  ≃  ap f γ⁻¹ ⬝ pr2 h = pr2 h', from
  begin
   intro γ, cases h with a b, cases h' with a' b', esimp at *,
   induction γ, induction b, apply typeq_refl
  end,
 have aps_eq : Π γ, (ap f γ⁻¹ ⬝ pr2 h = pr2 h') ≃ (ap f γ ⬝ pr2 h' = pr2 h), from
 begin
  intro γ, cases h with a b, cases h' with a' b', esimp at *,
  induction γ, induction b, unfold path_inv, esimp at *,
  apply (inv_is_equiv (refl (f a)) b' ∘
    eq_preserves_equiv b' (refl (f a) ⬝ b') (refl (f a)) (lu' b') )
 end,
 (sigma_equiv ∘ (sigma_preserves_equiv H)) ∘ sigma_preserves_equiv aps_eq
 
 -- Theorem 4.2.6

 definition fib_contr (f : A → B) (y : B) (h : ishae f) :
     isContr (fib f y) :=
 begin
  cases h with g h, cases h with ε h, cases h with η τ, apply ⟨(⟨ g y, ε y ⟩ : fib f y),
  show Π (w : fib f y), ⟨g y, ε y⟩ = w, from
    begin
      intro x, cases x with x p,
      apply (transport (λ x, x) (ua (fib_equiv f y ⟨g y, ε y⟩ ⟨x,p⟩))⁻¹ -- transport along lemma 4.2.5:
      ⟨ (ap g p)⁻¹ ⬝ (η x),  -- : g y = x
       by induction p;
       apply ((ap (ap f) (lu' ((η x))))⁻¹ ⬝ τ x) ⟩) -- : ap f ((ap g p)⁻¹ ⬝ (η x)) ⬝ p = ε (f x)
    end⟩ 
 end

 -- Definition 4.2.7 (Left and right inverses)

 definition linv (f : A → B) : Type :=
     Σ (g : B → A), g ∘ f ~ id A

 definition rinv (f : A → B) : Type :=
     Σ (g : B → A), f ∘ g ~ id B

 -- Lemma 4.2.8 

 definition comp_qinv_left (f : A → B) (e : qinv f) :
     qinv (λ (h : C → A), f ∘ h) :=
 sigma.rec_on e (λ g e, prod.rec_on e (λ η ε,
 ⟨(λ (h : C → B), g ∘ h),
  (begin intro h, apply funext, intro x, apply (η (h x)) end, 
   begin intro h, apply funext, intro y, apply (ε (h y)) end ) ⟩ ) )

 definition comp_qinv_right (f : A → B) (e : qinv f) :
     qinv (λ (h : B → C), h ∘ f) :=
 sigma.rec_on e (λ g e, prod.rec_on e (λ η ε,
 ⟨(λ (h : A → C), h ∘ g),
  (begin intro h,
    apply ((comp_assoc f g h)⁻¹ ⬝ funext (h ~ₗ ε)) end, 
   begin intro h,
    apply ((comp_assoc g f h)⁻¹ ⬝ funext (h ~ₗ η)) end ) ⟩ ) )

 -- Lemma 4.2.9

 definition linv_contr {A B : Type.{i}} (f : A → B) (e : qinv f) :
     isContr (linv f) :=
 have linveq : (Σ (g : B → A), g ∘ f = id A)  ≃  Σ (g : B → A), g ∘ f ~ id A, from
   sigma_preserves_equiv (λ g, ⟨happly, fun_extensionality⟩),
 have fib_linv : fib (λ (h : B → A), h ∘ f) (id A) = linv f, from
   transport (λ x, _ = x) (ua linveq) idp,
 transport isContr fib_linv (fib_contr (λ (h : B → A), h ∘ f) (id A)
  (qinv_to_ishae _ (comp_qinv_right f e)))

 --
