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
