/-
Copyright (c) 2015 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");

Theorems and exercises of the HoTT book (Chapter 4)
-/

import .ch2 --.ch3 

open eq prod unit bool sum sigma ua funext nat lift

/- ************************************** -/
/-    Ch.4 Equivalences                   -/
/- ************************************** -/

/- §4.1 (Quasi-inverses)  -/

 variables {A B C X Z: Type} 

 universe variables i j

 -- Lemma 4.1.1 

 -- Unseful lemmas of preservation of equality by type formers

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
 
 --
