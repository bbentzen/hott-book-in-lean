/-
Copyright (c) 2015 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");

Theorems and exercises of the HoTT book (ch 2)
-/

import .ch1 types.bool

open eq prod sum sigma

/- ************************************** -/
/-    Ch.2 Homotopy Type Theory           -/
/- ************************************** -/


/- §2.1 Types are Higher Groupoids  -/

 variables {A B C D Z: Type} 

 -- Lemma 2.1.1 "Paths can be reversed" :

 definition  path_inv {x y : A} (p : x = y) :                
     y = x :=
 eq.rec_on p (refl x)

 -- Lemma 2.1.2 "Paths can be composed" :

 definition path_conc {x y z: A} (p : x = y) (q : y = z) :     
     x = z :=
 eq.rec_on q p   
 
 -- Notation for conc and inv:
 
 notation  q `⬝` p  := path_conc q p
 notation  p `⁻¹` := path_inv p

 notation [parsing-only]  p `⁻¹'` := path_inv p

 -- Lemma 2.1.4 (i) "The constant path is a unit for composition" :

 definition ru {x y : A} (p : x = y) :     
     p = p ⬝ refl y   :=
 refl p                                                

 definition lu {x y : A} (p : x = y) :     
     p = refl x ⬝ p :=
 eq.rec_on p (refl (refl x))                         

 -- Lemma 2.1.4 (ii) "Inverses are well-behaved" :

 definition left_inv {x y : A} (p : x = y)  :      
     p⁻¹ ⬝ p = refl y   :=
 eq.rec_on p (refl (refl x) )

 definition right_inv {x y : A} (p : x = y)  :      
      p ⬝ p⁻¹ = refl x :=
 eq.rec_on p (refl (refl x) )

 -- Lemma 2.1.4 (iii) "Double application of inverses cancel out" :

 definition inv_canc {x y : A} (p : x = y)  : 
     ( p⁻¹ )⁻¹ = p :=
 eq.rec_on p (refl (refl x))
 
 -- Lemma 2.1.4 (iii) "composition is associative" :

 definition conc_assoc {x y z w: A} (p : x = y) (q : y = z) (r : z = w)  :
     p ⬝ (q ⬝ r)  = (p ⬝ q) ⬝ r :=
 eq.rec_on r (eq.rec_on q  (refl ( p ⬝ refl y ⬝ refl y )) )

 -- Theorem 2.1.6 Eckmann-Hilton 

 -- Whiskering

 definition r_whisker {x y z : A} {p q : x = y} (r : y = z) (α : p = q) :
     p ⬝ r = q ⬝ r :=
 by induction r; apply ((ru p)⁻¹ ⬝ α ⬝ ru q)

 definition l_whisker {x y z : A} (q : x = y) {r s : y = z} (β : r = s) :
     q ⬝ r = q ⬝ s :=
 by induction q; apply ((lu r)⁻¹ ⬝ β ⬝ lu s)

 notation   α `⬝ᵣ` r  := r_whisker r α
 notation   q `⬝ₗ` β  := l_whisker q β

 definition unwhisker_right {x y z : A} {p q : x = y} (r : y = z) (h : p ⬝ r = q ⬝ r) :
     p = q :=
 (eq.rec_on r (refl p ))⁻¹ ⬝ (h ⬝ᵣ r⁻¹) ⬝ (eq.rec_on r (refl q))

 definition unwhisker_left {x y z : A} {r s : y = z} (q : x = y) (h : q ⬝ r = q ⬝ s) :
     r = s :=
 (conc_assoc q⁻¹ q r ⬝ (left_inv q ⬝ᵣ r) ⬝ (lu r)⁻¹)⁻¹ ⬝
 (q⁻¹ ⬝ₗ h) ⬝ (conc_assoc q⁻¹ q s ⬝ (left_inv q ⬝ᵣ s) ⬝ (lu s)⁻¹)

 definition whisker_comm (a b c: A) (p q : a = b) (r s : b = c) (α : p = q) (β : r = s):
     (α ⬝ᵣ r) ⬝ (q ⬝ₗ β) = (p ⬝ₗ β) ⬝ (α ⬝ᵣ s) :=
 by induction α; induction β; induction p; induction r; apply idp

 -- Eckmann-Hilton

 definition eckmann_hilton (a : A) (α β : refl a = refl a) :
     α ⬝ β = β ⬝ α  :=
 calc
   α ⬝ β = (α ⬝ᵣ refl a) ⬝ (refl a ⬝ₗ β) : begin rewrite (α ⬝ₗ (lu β)), exact (lu _ ⬝ conc_assoc _ _ _) end
   ...  = (refl a ⬝ₗ β) ⬝ (α ⬝ᵣ refl a) : whisker_comm
   ...  = β ⬝ α : begin rewrite (β ⬝ₗ (lu α)), exact (lu _ ⬝ conc_assoc _ _ _)⁻¹ end

 -- Definition 2.1.7 Pointed types

 definition pointed : Type := Σ (A : Type), A

 --

/- §2.2 (Functions are functors)  -/

 -- Lemma 2.2.1 "Functions are continuous"

 definition ap {x y : A} (f : A → B) (p : x = y) : 
     f x = f y :=
 eq.rec_on p (refl (f x)) 

 -- Lemma 2.2.2 (i)-(iv) 

 -- (i) ap behaves functorially:

 definition ap_func_i {x y z : A} (f : A → B) (p : x = y) (q : y = z) :
     ap f ( p ⬝ q ) = (ap f p) ⬝ (ap f q) := 
 eq.rec_on q (eq.rec_on p (refl ((ap f (refl x)) ⬝ (ap f (refl x)))  ) )

 definition ap_func_ii {x y z : A} (f : A → B) (p : x = y) :
    ap f ( p⁻¹ ) = (ap f p)⁻¹ :=
 eq.rec (refl (ap f (refl x))) p

 definition ap_func_iii {x y z : A} (f : A → B) (g : B → A) (p : x = y) :
    ap g ( ap f p ) = (ap (g ∘ f) p) :=
 eq.rec (refl (ap (g ∘ f) (refl x))) p
 
 definition ap_func_iv {x y z : A} (p : x = y) :
    ap (id A) ( p ) = p :=
 eq.rec (refl (refl x)) p

 --

/- §2.3 (Type families are fibrations) -/

 -- Lemma 2.3.1 "Transport"

 definition transport {x y : A} (P : A → Type) (p : x = y) :
     P x → P y :=       
 assume u : P x , eq.rec_on p u

 -- Lemma 2.3.2 "Path Lifting property" :

 definition path_lifting {x y : A} (P : A → Type) (p : x = y) (u : P x) :
     (x , u) = (y , (transport _ p u)) :=
 eq.rec_on p (refl (x , u))

 -- Lemma 2.3.4 "Dependent maps" :

 definition apd {x y : A} {P : A → Type} (f : Π (x : A), P(x)) (p : x = y) :
     transport P p (f x) = f y := 
 eq.rec_on p (refl (f x)) 

 -- Lemma 2.3.5 "Transport over constant families"

 definition trans_const {x y : A} (p : x = y) (b : B) :      
     transport _ p b = b := 
 eq.rec_on p (refl b) 

 -- Lemma 2.3.8 :

 definition apd_eq_trans_const_ap {x y : A} (P : A → Type) (f :A → B) (p : x = y) :
     apd f p = trans_const p (f x) ⬝ ap f p := 
 eq.rec_on p (refl (refl (f x)) )

 -- Lemma 2.3.9 "Composition of transport equals composition of their underlying paths" : 

  definition comp_trans_comp_path {x y z : A} (P : A → Type) (p : x = y) (q : y = z) (u : P x) :
     transport P q (transport P p u) = transport P (p ⬝ q) u :=
 eq.rec_on q (eq.rec_on p refl u)

 -- Lemma 2.3.10 :

 definition trans_ap_fun {x y : A} (f : A → B) (P : B → Type) (p : x = y) (u : P (f x)) : 
     transport (P ∘ f) p u = transport P (ap f p) u :=
 eq.rec_on p (refl u)

 -- Lemma 2.3.11 :

 definition lemma_2_3_11 {x y : A} {P Q : A → Type} (f : Π (x : A), P(x) → Q(x)) (p : x = y) (u : P x) :
     transport Q p (f x u) = f y (transport P p u) := 
 eq.rec_on p (refl (f x u))

 --

/- §2.4 (Homotopies and equivalences) -/

 infix `~` := homotopy

 -- id is a unit for function composition

 definition id_ru (f : A → B) :
     f ∘ id A ~ f :=
 assume (x : A), refl (f x)

 definition id_lu (f : A → B) :
     id B ∘ f ~ f :=
 assume (x : A), refl (f x) 

 -- Lemma 2.4.2 "Homotopy is an equivalence relation" :

 definition hom_refl (f : A → B) :                               
     f ~ f :=                                                    
 λ x, (refl (f x))                                               
                                                                
 definition hom_sym {f g : A → B} (H : f ~ g) :                  
     g ~ f :=                                                    
 λ x, (H x)⁻¹                                                    
                                                                
 definition hom_trans {f g h : A → B} (H₁: f ~ g) (H₂: g ~ h) :  
     f ~ h :=                                                    
 λ x, (H₁ x) ⬝ (H₂ x)                                            

  notation   H `⁻¹`  := hom_sym H
  notation   H₁ `~~` H₂  := hom_trans H₁ H₂

 -- Lemma 2.4.3 "Homotopies are natural transformations" :

 definition hom_ap {x y : A} (f g : A → B) (H : f ~ g) (p : x = y) :
    ap f p ⬝ H y =  H x ⬝ ap g p :=
 eq.rec_on p (lu (H x ⬝ ap g (refl x)))⁻¹ 

 -- Corollary 2.4.4 :

  definition lem_hom_ap_id {x : A} (f : A → A) (H : f ~ id A)  :
    H (f x) ⬝ ap (λ(x : A), x) (H x) = H (f x) ⬝ H x :=
 l_whisker (H (f x)) (eq.rec_on (H x) (refl (refl (f x))))

definition hom_ap_id' {x : A} (f : A → A) (H : f ~ id A )  :
     H (f x) = ap f (H x) :=
 (unwhisker_right (H x) ((hom_ap f (λx : A, x) H (H x)) ⬝  (lem_hom_ap_id f H) ))⁻¹

-- Equivalences

 definition qinv {A B : Type} (f : A → B) : Type :=
     Σ (g : B → A), (f ∘ g ~ id B) × (g ∘ f ~ id A)

 definition id_qinv :
     qinv (id A) :=
 sigma.mk (id A) (prod.mk (λ x : A, refl x) (λ x : A, refl x))

 definition ex_2_4_8 {x y z : A} (p: x = y) :
     qinv (λ q : y = z, p ⬝ q) :=
 sigma.mk (λ q : x = z, p⁻¹ ⬝ q) 
   (prod.mk
     (λ q : x = z, (conc_assoc p p⁻¹ q) ⬝ (r_whisker q ( right_inv p)) ⬝ (lu q)⁻¹)
     (λ q : y = z,(conc_assoc p⁻¹ p q) ⬝ (r_whisker q ( left_inv p)) ⬝ (lu q)⁻¹)  )

 definition trans_id_right {x y : A}(P : A → Type) (p: x = y) (u : P y) :
      transport P (p⁻¹ ⬝ p) u = u :=
 eq.rec_on p refl (transport P (refl y) u)

 definition trans_id_left {x y : A}(P : A → Type) (p: x = y) (u : P x) :
      transport P (p ⬝ p⁻¹) u = u :=
 eq.rec_on p refl (transport P (refl x) u)

 definition ex_2_4_9 {x y : A} (p: x = y) (P : A → Type) : 
     qinv (λ u : P x, transport P p u) :=
 ⟨(λ u : P y, transport P p⁻¹ u), ((λ u : P y, comp_trans_comp_path P p⁻¹ p u ⬝ trans_id_right _ p u),
 (λ u : P x, comp_trans_comp_path P p p⁻¹ u ⬝ trans_id_left _ p u)  )⟩ 

 -- definition of isequiv

 definition isequiv {A B : Type} (f : A → B) : Type :=
     ( Σ (g : B → A), f ∘ g ~ id B ) × ( Σ (h : B → A), h ∘ f ~ id A ) 

 -- (i) Quasi-inverse  →  Equivalence

 definition qinv_to_isequiv (f : A → B) :
     qinv f → isequiv f :=
 assume e : qinv f, prod.mk 
( sigma.rec_on e (λ(g : B → A) (α : (f ∘ g ~ id B) × (g ∘ f ~ id A) ), ⟨g, pr1 α⟩ ) )
( sigma.rec_on e (λ(h : B → A) (β : (f ∘ h ~ id B) × (h ∘ f ~ id A) ), ⟨h, pr2 β⟩ ) )

 -- (ii) Equivalence  →  Quasi-Inverse

 definition hom_r_whisker {f g : B →  C} (α : f ~ g) (h : A → B) :
     f ∘ h ~ g ∘ h :=
 assume (x : A), α (h x)

 definition hom_l_whisker (h : B → C) {f g : A →  B} (β : f ~ g) :
     h ∘ f ~ h ∘ g :=
 assume (x : A),
 calc
   h (f x) = h (f x) : rfl
   ... = h (g x) : β x

 notation   α `~ᵣ` h  := hom_r_whisker α h
 notation   h `~ₗ` β  := hom_l_whisker h β 

 definition hom_comp_assoc (f : A → B) (g : B → C) (h : C → D) :  h ∘ (g ∘ f) ~ (h ∘ g) ∘ f :=    -- Superfluous, given univalence
 λ (x : A), refl (h (g (f x)))

 definition isequiv_to_qinv (f : A → B) :
     isequiv f → qinv f :=
 assume e : isequiv f, sigma.rec_on (pr1 e) (λ (g : B → A) (α : (f ∘ g ~ id B)), 
 sigma.rec_on (pr2 e) (λ (h : B → A) (β : (h ∘ f ~ id A)), 
   have γ : g ~ h, from (β ~ᵣ g ~~ id_lu g)⁻¹  ~~ (h ~ₗ α  ~~ id_ru h),
   have β' : g ∘ f ~ id A, from assume (x : A), (γ (f x)) ⬝ (β x),
 sigma.mk g (α, β')  ) )

 -- Type Equivalences

 definition typeq (A : Type) (B : Type) : Type :=
     Σ (f : A → B), isequiv f

 notation A `≃` B := typeq A B

 -- Lemma 2.4.12 "Type equivalence is an equivalence relation on Type Universes"

 definition typeq_refl (A : Type) :
     A ≃ A :=
 ⟨ id A , (prod.mk (sigma.mk (id A) (λ x : A, refl x)) (sigma.mk (id A) (λ x : A, refl x))) ⟩

 definition typeq_sym (H : A ≃ B):
     B ≃ A :=
 sigma.rec_on H (λ (f : A → B) (e : isequiv f), 
   have e' : qinv f, from (isequiv_to_qinv f) e,
   sigma.rec_on e' (λ (g : B → A) (p : (f ∘ g ~ id B) × (g ∘ f ~ id A)),
     sigma.mk g (prod.mk (sigma.mk f (pr2 p)) (sigma.mk f (pr1 p)))  )  )  

 definition typeq_trans (H₁ : A ≃ B) (H₂ : B ≃ C) :
     A ≃ C :=
 sigma.rec_on H₁ (λ (f : A → B) (e₁ : isequiv f),
   sigma.rec_on H₂ (λ (g : B → C) (e₂ : isequiv g),
   have e₁' : qinv f, from (isequiv_to_qinv f) e₁,
   have e₂' : qinv g, from (isequiv_to_qinv g) e₂,  
     sigma.rec_on e₁' (λ (f' : B → A) (p₁ : (f ∘ f' ~ id B) × (f' ∘ f ~ id A)),
       sigma.rec_on e₂' (λ (g' : C → B) (p₂ : (g ∘ g' ~ id C) × (g' ∘ g ~ id B)),
       have q₁ : (g ∘ f) ∘ (f' ∘ g') ~ id C, from
         ((hom_comp_assoc f' f g) ~ᵣ g')⁻¹ ~~ (((g ~ₗ (pr1 p₁)) ~~ id_ru g) ~ᵣ g') ~~ (pr1 p₂),
       have q₂ : (f' ∘ g') ∘ (g ∘ f) ~ id A, from
         (f' ~ₗ (hom_comp_assoc f g g')) ~~ (f' ~ₗ (((pr2 p₂) ~ᵣ f) ~~ id_lu f)) ~~ (pr2 p₁),
       sigma.mk (g ∘ f) (prod.mk (sigma.mk (f' ∘ g') q₁) (sigma.mk (f' ∘ g')  q₂))   ) ) ) )

 --

/- §2.6 (Cartesian Product Types) -/

 definition pair_eq {x y : A × B} :
     (pr1 x = pr1 y) × (pr2 x = pr2 y) → x = y :=
 by intro s; cases s with p q; cases x with a b; cases y with a' b'; esimp at *; induction p; induction q; apply idp

 -- Propositional Computation and Uniqueness rules

 definition prod_beta {x y : A × B} (s : (pr1 x = pr1 y) × (pr2 x = pr2 y)) : 
     (ap pr1 (pair_eq s), ap pr2 (pair_eq s)) = s :=
 by cases s with p q; cases x with a b; cases y with a' b'; esimp at *; induction p; induction q; esimp at *

 definition prod_uniq {x y : A × B} (r : x = y) :
   pair_eq (ap pr1 r, ap pr2 r) = r :=
 by induction r; cases x; apply idp

 -- Theorem 2.6.2

 definition pair_equiv {x y : A × B} :
      x = y  ≃  (pr1 x = pr1 y) × (pr2 x = pr2 y) :=
 ⟨ (λ x, (ap pr1 x, ap pr2 x)), ( ⟨pair_eq, λ s, prod_beta s⟩, ⟨pair_eq, λ r, prod_uniq r⟩ ) ⟩ 

 -- Higher Groupoid Structure

 definition prod_refl {z : A × B} :
   refl z = pair_eq ( ap pr1 (refl z), ap pr2 (refl z)) :=
 by cases z; apply idp

 definition prod_inv {x y : A × B} (p : x = y) :
   p⁻¹ = pair_eq ( ap pr1 (p⁻¹), ap pr2 (p⁻¹)) :=
 by induction p; cases x; apply idp

 definition prod_comp {x y z: A × B} (p : x = y) (q : y = z):
   p ⬝ q = pair_eq ( ap pr1 p, ap pr2 p) ⬝ pair_eq ( ap pr1 q, ap pr2 q) :=
 by induction p; induction q; cases x with a b; apply idp

 -- Theorem 2.6.4

 definition trans_prod {z w : Z} (A B: Z → Type) (p : z = w) (x : A z × B z) :
     transport (λ z, A z × B z) p x = (transport A p (pr1 x), transport B p (pr2 x))  :=
 eq.rec_on p (uppt x)

 -- Theorem 2.6.5 

 definition func_prod {A' B' : Type} (g : A → A') (h : B → B') :  -- g and h induces a func_prod
     A × B → A' × B' :=
 λ (x : A × B), (g(pr1 x), h(pr2 x))
 
 definition prod_ap_func {x y : A × B} {A' B' : Type} (g : A → A') (h : B → B') (p : pr1 x = pr1 y) (q : pr2 x = pr2 y):
     ap (func_prod g h) (pair_eq (p,q)) = pair_eq (ap g(p), ap h(q)) :=
 prod.rec_on x (λ a b , prod.rec_on y (λ a' b' p, eq.rec_on p (λ q, eq.rec_on q idp ))) p q

 --

/- §2.7 (Sigma Types) -/
 
 definition ap_sigma {P : A → Type} {w w' : Σ (x:A), P x} :
     w = w' → ⟨Σ (p : pr1 w = pr1 w'), transport P p (pr2 w) = pr2 w'⟩ :=
 by intro r; induction r; cases w with w1 w2; esimp at *; fapply sigma.mk; exact refl w1; apply idp

 definition sigma_eq {P : A → Type} {w w' : Σ (x:A), P x} :
     ⟨Σ (p : pr1 w = pr1 w'), transport P p (pr2 w) = pr2 w'⟩ → w = w'  :=
 by intro s; cases w; cases w'; cases s with p q; esimp at *; induction p; induction q; apply idp

 -- Propositional Computation and Uniqueness rules

 definition sigma_comp {P : A → Type} {w w' : Σ (x:A), P x} (r : Σ (p : pr1 w = pr1 w'), transport P p (pr2 w) = pr2 w'):
   ap_sigma (sigma_eq r) = r :=
 by cases w with w1 w2; cases w' with w1' w2'; cases r with p q; esimp at *; induction p; induction q; apply idp

 definition sigma_uniq {P : A → Type} {w w' : Σ (x:A), P x} (p : w = w'):
   sigma_eq (ap_sigma p) = p :=
 by induction p; cases w; apply idp

 -- Theorem 2.7.2

 definition sigma_equiv {P : A → Type} {w w' : Σ (x:A), P x} :
   w = w' ≃ Σ (p : pr1 w = pr1 w'), transport P p (pr2 w) = pr2 w' :=
 ⟨ ap_sigma, ( ⟨sigma_eq, λ s, sigma_comp s⟩, ⟨sigma_eq, λ r, sigma_uniq r⟩ ) ⟩ 

 -- Corollary 2.7.3

 definition eta_sigma {P : A → Type} (z : Σ (x : A), P x) :
     z = ⟨pr1 z, pr2 z⟩ :=
 by cases z; esimp at *

 -- Theorem 2.7.4

 definition sigma_trans {P : A → Type} {Q : (Σ (x : A), P x) → Type} {x y : A} (p : x = y) (u : P x) (z : Q ⟨x, u⟩) :
     transport (λ x,  (Σ (u : P x), Q ⟨x, u⟩)) p ⟨u,z⟩ = ⟨transport P p u, transport Q (sigma_eq ⟨p, refl (transport P p u)⟩) z⟩ :=
 by induction p; apply refl ⟨u,z⟩

 -- Higher Groupoid Structure

 definition sigma_refl {P : A → Type} {z : Σ (x : A), P x} :
   refl z = sigma_eq ⟨ ap pr1 (refl z), refl (transport P (ap pr1 (refl z)) (pr2 z)) ⟩  :=
 by cases z; apply idp

 definition sigma_inv {P : A → Type} {x y : Σ (x : A), P x} (p : x = y) :
     p⁻¹ = (sigma_eq (ap_sigma p⁻¹)) :=
 by induction p; cases x; apply idp

 definition sigma_com {P : A → Type} {x y z: Σ (x : A), P x} (p : x = y) (q : y = z):
   p ⬝ q = sigma_eq (ap_sigma (p ⬝ q)) :=
 by induction p; induction q; cases x; apply idp

 --

/- §2.8 (Unit Types) -/

 open unit

 notation `⋆` := star

 definition eq_star {x y : unit} :
     (x = y) → unit   :=
 λ (p : x = y), ⋆

 definition unit_eq {x y : unit} :
     unit → (x = y)  :=
 λ u: unit, unit.rec_on x ( unit.rec_on y (refl ⋆))

 -- Theorem 2.8.1. 

 definition unit_equiv {x y : unit} :
     x = y ≃ unit :=
 have comp_rule : eq_star ∘ unit_eq ~ id unit, from λ u : unit, unit.rec_on u (refl ⋆),
 have uniq_rule : unit_eq ∘ eq_star ~ id (x = y), from λ (p : x = y), unit.rec_on x (unit.rec_on y (λ p, eq.rec_on p (refl (refl ⋆)) ) ) p,
 ⟨ eq_star, ( ⟨unit_eq, comp_rule⟩, ⟨unit_eq, uniq_rule⟩ ) ⟩

 -- Higher Groupoid Structure

 definition unit_refl {u : unit} :
   refl u = unit_eq (eq_star (refl u)) :=
 by cases u; apply refl (refl ⋆)

 definition unit_inv {x y : unit} (p : x = y) :
   p⁻¹ = unit_eq (eq_star (p⁻¹)) :=
 by induction p; cases x; apply refl (refl ⋆)
 
 definition unit_comp {x y z: unit} (p : x = y) (q : y = z) :
   p ⬝ q = @unit_eq x y (eq_star (p)) ⬝ unit_eq (eq_star (q)) :=  
 by induction p; induction q; cases x; apply refl (refl ⋆)

 --

/- §2.9 (Π-types and the function extensionality axiom) -/

 namespace funext

 definition happly {A : Type}  {B : A → Type} {f g: Π (x : A), B x} :
     f = g  →  Π x : A, f x = g x :=
 λ p x, eq.rec_on p (refl (f x))

 axiom fun_extensionality {A : Type}  {B : A → Type} {f g: Π (x : A), B x} :
     isequiv (@happly A B f g)

 definition funext [reducible] {A : Type}  {B : A → Type} {f g: Π (x : A), B x} :
     (Π x : A, f x = g x) → f = g :=
 by cases fun_extensionality with p q; cases p with funext comp; exact funext

 -- Propositional Computational rules

/- definition funext_comp {A : Type} {B : A → Type} {f g: Π (x : A), B x} (h : Π x : A, f x = g x) :
     happly (funext h) = h :=
 by cases @fun_extensionality A B f g with p q; cases p with funext comp; exact comp -/

 -- Higher Groupoid Structure

/- definition pi_refl {A : Type}  {B : A → Type} {f : Π (x : A), B x} :  
     refl f = funext (happly (refl f) ) :=             
 by apply idp -/

 -- Transporting non-dependent and dependent functions

 definition nondep_trans_pi {X : Type} {A B : X → Type} {x₁ x₂ : X} (p : x₁ = x₂) (f : A x₁ → B x₁) :
     transport (λ (x₁ : X), (A x₁) → (B x₁)) p f = (λ x, transport B p (f (transport A p⁻¹ x))) :=
 eq.rec (refl f) p

 definition trans_pi {X : Type} {A : X → Type} {B : Π (x : X), (A x → Type)} {x₁ x₂ : X} (p : x₁ = x₂) (f : Π (a : A x₁), B x₁ a) (a : A x₂) :
     (transport (λ (x₁ : X), (Π (a : A x₁), (B x₁ a))) p f) a =
     transport (λ (w : Σ (x : X), A x), B (pr1 w) (pr2 w)) (sigma_eq ⟨p⁻¹, refl (transport A p⁻¹ a)⟩)⁻¹ (f (transport A p⁻¹ a)) :=
 by induction p; apply idp

 -- Lemma 2.9.6

 definition nondep_eq {X : Type} {A B : X → Type} {x y : X} (p : x = y) (f : A x → B x) (g : A y → B y):
     (transport (λ x, A x → B x) p f = g) ≃  (Π (a : A x), (transport B p (f a)) = g (transport A p a)) :=
 by induction p; fapply sigma.mk; exact happly; apply fun_extensionality

 -- Lemma 2.9.7
 
 definition dep_eq {X : Type} {A : X → Type} {B : Π (x : X), (A x → Type)} {x y : X} (p : x = y) (f : Π (a : A x), B x a)
 (g : Π (a : A y), B y a) (a : A y) :
     (transport (λ (x₁ : X), (Π (a : A x₁), (B x₁ a))) p f = g) ≃
     (Π (a : A x), transport (λ (w : Σ (x : X), A x), B (pr1 w) (pr2 w)) (sigma_eq ⟨p, refl (transport A p a)⟩) (f a) = g (transport A p a)) :=
 by induction p; fapply sigma.mk; exact happly; apply fun_extensionality

 end funext

 --

/- §2.10 (Universes and the Univalence axiom) -/
 
 namespace ua
 
 universe variables i j

 definition idtoeqv {A B : Type.{i}} :
     (A = B) → (A ≃ B)  :=
 λ (p : A = B), eq.rec_on p ⟨id A, (qinv_to_isequiv (id A) (id_qinv))⟩
 
 axiom univalence  {A B : Type.{i}}:
     isequiv (@idtoeqv A B)

 definition ua [reducible] {A B: Type.{i}} :
     (A ≃ B) → (A = B)  :=
 by cases univalence with p q; cases p with ua comp_rule; exact ua
 
 -- Propositional and Computational rules

/- definition ua_comp {A B: Type.{i}} (e : A ≃ B):
     idtoeqv (ua e) = e :=
  by cases @univalence A B with p q; cases p with ua comp; exact comp

 definition ua_eta {A B: Type.{i}} :--(p : A = B) :
     ua ∘ (idtoeqv ) ~ id (A = B) :=
  by cases univalence with p q; cases q with ua eta; exact eta  

 -- Higher Groupoid Structure
 
 definition ua_refl {A : Type.{i}} :
     refl A = ua ⟨id A, qinv_to_isequiv _ id_qinv⟩ :=
 refl (refl A)  -/

 -- Lemma 2.10.5
 
 definition trans_univ {A : Type} {B : A → Type} {x y : A} (p : x = y) (u : B x) : 
     transport B p u = transport (λ (X : Type), X) (ap B p) u :=
 by induction p; apply idp

 definition trans_idtoequiv {A : Type} {B : A → Type} {x y : A} (p : x = y) (u : B x) : 
     transport (λ (X : Type), X) (ap B p) u = pr1 (idtoeqv (ap B p)) u :=
 by induction p; apply idp

 end ua

 --

/- §2.11 (Identity type) -/

 -- Theorem 2.11.1

 open funext

 definition id_eq {a a' : A} (f : A → B) (h : isequiv f) :
     isequiv (@ap A B a a' f ) :=
 have h' : qinv f, from (isequiv_to_qinv f) h,
  sigma.rec_on h'
   (λ finv p, prod.rec_on p (λ α β,
   have α' : (Π (q : f a = f a'), ap f((β a)⁻¹ ⬝ ap finv q ⬝ β a') = q), from λ (q : f a = f a'),      -- book suggs. lemmas 2.2.2 and 2.4.3
     calc
       ap f((β a)⁻¹ ⬝ ap finv q ⬝ β a') = ap f((β a)⁻¹ ⬝ ap finv q ⬝ β a') : idp
       --... = ((α (f a))⁻¹ ⬝ (α (f a))) ⬝ ap f (β a)⁻¹ ⬝ ap f (ap finv q ⬝ β a') : 
       --... = ((α (f a))⁻¹ ⬝ (α (f a))) ⬝ ap f (β a)⁻¹ ⬝ ap f (ap finv q ⬝ β a') ⬝ ((α (f a'))⁻¹ ⬝ (α (f a'))) : (refl (refl _))
       --... = ap f ((β a)⁻¹ ⬝ (ap finv q ⬝ β a')) : (path_inv (conc_assoc (path_inv (β a)) (ap finv q) (β a')))
       ... = ap f ((β a)⁻¹ ⬝ ap finv q) ⬝ ap f (β a') : ap_func_i f _ _
       ... = ap f (β a)⁻¹ ⬝ ap f (ap finv q) ⬝ ap f (β a') : (ap_func_i f _ _) ⬝ᵣ ap f (β a')
       --... = ap f (β a)⁻¹ ⬝ ap (f ∘ finv) q ⬝ ap f (β a') : ap_func_iii finv f q
       --... = ap f (β a)⁻¹ ⬝ ap (id B) q ⬝ ap f (β a') : α
       ... = q : sorry  , -- don't erase this comma!
   have β' : (Π (p : a = a'), (β a)⁻¹ ⬝ ap finv (ap f p) ⬝ β a' = p), from           -- right inverse
     λ (p : a = a'), eq.rec_on p (eq.rec_on (β a) (refl (refl (finv (f a)))) ),
  qinv_to_isequiv (ap f) ⟨λ q, (β a)⁻¹ ⬝ ap finv q ⬝ β a', (α',β')⟩))

 example {w w' : A × B} (p q : w = w') :
     p = q ≃ (ap pr1 p = ap pr1 q) × (ap pr2 p = ap pr2 q) :=
 typeq_trans ⟨ap (λ x, (ap pr1 x, ap pr2 x)) , id_eq _ ( ⟨pair_eq, λ s, prod_beta s⟩, ⟨pair_eq, λ r, prod_uniq r⟩ ) ⟩ pair_equiv

 example {B : A → Type} {f g: Π (x : A), B x} {p q : f = g}  :
     p = q ≃ Π (x : A), (happly p x = happly q x) :=                 
 typeq_trans ⟨ap happly, id_eq happly fun_extensionality ⟩ ⟨happly, fun_extensionality⟩

 -- Lemma 2.11.2

 definition id_trans_i {x₁ x₂ : A} (a : A) (p : x₁ = x₂) (q : a = x₁):
     transport (λ x, a = x) p q = q ⬝ p :=
 by induction p; induction q; apply refl (refl a)
 
 definition id_trans_ii {x₁ x₂ : A} (a : A) (p : x₁ = x₂) (q : x₁ = a):
     transport (λ x, x = a) p q = p⁻¹ ⬝ q :=
 by induction p; induction q; apply refl (refl x₁)

 definition id_trans_iii {x₁ x₂ : A} (p : x₁ = x₂) (q : x₁ = x₁):
     transport (λ x, x = x) p q = p⁻¹ ⬝ q ⬝ p :=
 eq.rec_on p (calc
   transport (λ x, x = x) (refl x₁) q = q : idp
   ... = (refl x₁)⁻¹ ⬝ q  : lu
   ... = ((refl x₁)⁻¹ ⬝ q) ⬝ (refl x₁) : ru )

 -- Theorem 2.11.3 (More general form of the previous lemma iii)

 definition id_trans_fun {a a' : A} (f g : A → B) (p : a = a') (q : f (a) = g (a)):
     transport (λ x, f x = g x) p q = (ap f p)⁻¹ ⬝ q ⬝ (ap g p) :=
 eq.rec_on p (calc
   transport (λ x, f x = g x) (refl a) q = q : idp
   ... = (refl (f a))⁻¹ ⬝ q  : lu
   ... = ((refl (f a))⁻¹ ⬝ q) ⬝ (refl (g a)) : ru )

 -- Theorem 2.11.4 (Dependent version of the previous theorem)

 definition id_trans_dfun {a a' : A} {B : A → Type} (f g : Π (x : A), B x) (p : a = a') (q : f (a) = g (a)) :
     transport (λ x, f x = g x) p q = (apd f p)⁻¹ ⬝ ap (transport B p) q ⬝ (apd g p) :=
 eq.rec_on p (calc
   transport (λ x, f x = g x) (refl a) q = q : idp
   ... = ap (transport B (refl a)) q : (λ x y (q : x = y), eq.rec_on q (refl (refl x))) (f a) (g a) q
   ... = (refl (f a))⁻¹ ⬝ ap (transport B (refl a)) q  : lu
   ... = ((refl (f a))⁻¹ ⬝ ap (transport B (refl a)) q) ⬝ (refl (g a)) : ru )

  -- Theorem 2.11.5

 definition id_trans_equiv {a a' : A} (p : a = a') (q : a = a) (r : a' = a'):
     (transport (λ x, x = x) p q = r) ≃ (q ⬝ p = p ⬝ r) :=
 by induction p; apply ua.idtoeqv; exact (calc
   (transport (λ x, x = x) (refl a) q = r) = (q ⬝ refl a = r) : idp
   ... = (q ⬝ refl a = refl a ⬝ r) : lu )

 --

 /- §2.12 (Coproducts) -/

 section coproduct

 open lift

 universe variables i j  parameters {A' : Type.{i}} {B' : Type.{j}} {a₀ : A'}

 definition code : --{A : Type.{i}} {B : Type.{j}} {a₀ : A} :
     A' + B' → Type
 | code (inl a) := (a₀ = a)
 | code (inr b) := lift empty

 definition encode : Π (x : A' + B') (p : inl (a₀) = x), code x
 | encode x p := transport code p (refl a₀)

 definition decode (x : A' + B') (c : code x) : inl (a₀) = x :=
 by cases x with l r; exact ap inl (c); exact (empty.rec_on _ (down c))

 -- Propositional Computation and Uniqueness rules

 definition sum_uniq (x : A' + B') (p : inl (a₀) = x) :
    decode x (encode x p) = p :=
 by induction p; apply idp

 definition sum_beta (x : A' + B') (c : code x) :
    encode x (decode x c) = c :=
 by cases x; exact (calc
   encode (inl a) (decode (inl a) c) = transport code (ap inl (c)) (refl a₀) : idp
   ... = transport (code ∘ inl) (c) (refl a₀) : (trans_ap_fun inl code (c) (refl a₀))⁻¹ 
   ... = transport (λ a : A', (a₀ = a)) (c) (refl a₀) : idp
   ... = (refl a₀) ⬝ (c) : id_trans_i   -- check lean's library
   ... = c : lu );
 exact (empty.rec_on _ (down c))

 -- Theorem 2.12.5 

 definition code_equiv (x : A' + B') :
     (inl a₀ = x) ≃ code x :=
 ⟨ encode x, ( ⟨decode x, sum_beta x⟩, ⟨decode x, sum_uniq x⟩ ) ⟩ 

 definition inl_eq (a₁ : A') : 
     (inl a₀ = inl a₁ ) ≃ (a₀ = a₁) :=
 code_equiv (inl a₁)

 definition inl_inr_neq (a₁ : B') : 
     (inl a₀ = inr a₁ ) ≃ lift empty :=
 code_equiv (inr a₁)

 -- Transport of coproducts

 definition trans_inl {X : Type} {A B : X → Type} {x₁ x₂ : X} (p : x₁ = x₂) (a : A x₁) :
     transport (λ x, A x + B x) p (inl a) = inl (transport A p a) :=
 by induction p; apply (refl (inl a))

 definition trans_inr {X : Type} {A B : X → Type} {x₁ x₂ : X} (p : x₁ = x₂) (b : B x₁) :
     transport (λ x, A x + B x) p (inr b) = inr (transport B p b) :=
 by induction p; apply (refl (inr b))

 end coproduct
 
 --

 /- §2.13 (Natural numbers) -/

 open nat

 definition natcode [reducible] : 
     ℕ → ℕ → Type₀
 | natcode 0 0 := unit
 | natcode (succ m) 0 := empty
 | natcode 0 (succ n) := empty
 | natcode (succ m) (succ n) := natcode m n

 definition r : Π (n : ℕ), natcode n n
 | r 0 := ⋆
 | r (succ n) := r n

 definition natencode (m n : ℕ) : 
     (m = n) → natcode m n :=
 λ p, transport (natcode m) p (r m)

 definition natdecode : Π (m n : ℕ), natcode m n → (m = n)
 | natdecode 0        0 c  := refl 0
 | natdecode (succ i) 0 c  := empty.rec_on _ c
 | natdecode 0  (succ j) c := empty.rec_on _ c
 | natdecode (succ i) (succ j) c := ap succ (natdecode i j c)

 -- Propositional Computation and Uniqueness rules

/- definition nat_uniq (m n : ℕ) (p : m = n) :
     natdecode m n (natencode m n p) = p :=
 by induction p; induction m; reflexivity; rewrite [↑natencode,↑natdecode,↑r,v_0]

-- decode (succ i) (succ i) r(i) = refl (succ i)

--; apply (ap succ v_0)
--  definition nat_uniq: Π (m n : ℕ) (p : m = n),
-- | nat_uniq 0 0 (refl 0)  := idp
-- | nat_uniq (succ i) (succ i) (refl (succ i))  := ap succ (nat_uniq i i (refl i))

 -- Theorem 2.13.1 (Nat is equivalent to its encoding)

 definition nat_comp : Π (m n : ℕ) (c : natcode m n),
     natencode m n (natdecode m n c) = c
 | nat_comp 0        0 c  := @unit_eq (r 0) c c
 | nat_comp (succ i) 0 c  := empty.rec_on _ c
 | nat_comp 0  (succ j) c := empty.rec_on _ c
 | nat_comp (succ i) (succ j) c := calc
     natencode (succ i) (succ j) (natdecode (succ i) (succ j) c) = transport (natcode (succ i)) (ap succ (natdecode i j c)) (r (succ i)) : idp
     ... = transport (λ x, natcode (succ i) (succ x)) (natdecode i j c) (r (succ i)) : sorry
     ... = natencode i j (natdecode i j c) : sorry
     ... = c : idp
-/

 -- Theorem 2.13.1

 definition nat_eq (m n : ℕ) : 
   (m = n) ≃ natcode m n :=
 sorry

 --
 
 /- §2.14 (Example: equality of structures) -/

 open ua

 definition semigroupStr (A : Type) : Type :=
 Σ (m : A → A → A), Π (x y z : A), m x (m y z) = m (m x y) z

 definition semigroup : Type :=
 Σ (A : Type), semigroupStr A

 -- §2.14.1 Lifting Equivalences

 universe variables i j

 example {A B : Type.{i}} (e : A ≃ B) (g : semigroupStr A) : semigroupStr B :=
 transport semigroupStr (ua e) g
 
  /- §2.15 (Universal Properties) -/

 definition umpprod :
     (X → A × B) → (X → A) × (X → B) :=
 λ u, (λ x, pr1 (u x) , λ x, pr2 (u x) )

 -- Theorem 2.15.2

 definition prodinv :
 (X → A) × (X → B) → (X → A × B) := λ fg, λ x, ((pr1 fg) x, (pr2 fg) x)

