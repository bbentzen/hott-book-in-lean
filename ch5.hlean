/-
Copyright (c) 2016 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");

Theorems and exercises of the HoTT book (Chapter 5)
-/

import .ch2 .ch3 

open eq prod unit bool sum sigma ua funext nat lift

/- ************************************** -/
/-    Ch.5 Induction                      -/
/- ************************************** -/

/- §5.1 (Introduction to inductive types)  -/

 variables {A B C X Z: Type} 

 -- Theorem 5.1.1
 
 definition uniq_nat_rec {E : ℕ → Type} (f g : Π (x : ℕ), E x) (e₀ : E 0) (eₛ : Π (x : ℕ), E x → E (succ x))
  (H₁ : f 0 = e₀) (H₂ : g 0 = e₀) (H₃ : Π n, f (succ n) = eₛ n (f n)) (H₄ : Π n, g (succ n) = eₛ n (g n)) :
     f = g :=
 begin
  apply funext, intro n, induction n with n IH,
  apply (H₁ ⬝ H₂⁻¹), apply (H₃ n ⬝ ap (eₛ n) IH ⬝ (H₄ n)⁻¹)
 end

 --

/- §5.2 (Uniqueness of inductive types)  -/

 inductive list (A : Type) : Type :=
 | nil : list A
 | cons : A → list A → list A

 definition nat_to_list :
     ℕ → list 𝟭 :=
 by intro n; induction n with n IH; apply list.nil; apply (list.cons ⋆ IH)

 definition list1_eq_nat :
     list 𝟭 ≃ ℕ :=
 let f := λ a, list.rec_on a 0 (λ u a H, succ H) in ⟨f,
  (⟨nat_to_list, show (Π (n : ℕ), f (nat_to_list n) = n), from
     begin
       intro n,induction n with n IH, 
       apply idp, apply (ap succ IH)
     end⟩, 
   ⟨nat_to_list, show (Π (a : list 𝟭), nat_to_list (f a) = a), from
     begin
      intro a,induction a with u a H,
      apply idp, induction u, apply (ap (list.cons ⋆) H)
     end
  ⟩ ) ⟩ 

 --

/- §5.3 (W-types)  -/

 universe variables i j

 inductive wtype {A : Type.{i}} (B : A → Type.{j}) : Type.{max i j} :=
 | sup : Π (a : A), (B a → wtype B) → wtype B

 notation `W` binders `, ` x:(scoped P, wtype P) := x

 open wtype

 -- ℕ with W-types

 definition nat' : Type₀ := W (b : 𝟮), bool.rec_on b 𝟬 𝟭

 notation `ℕ'` := nat'

 definition zero' : ℕ' := 
  sup ff (λ (x : 𝟬), empty.rec_on _ x)

 definition succ' : ℕ' → ℕ' := 
  λ n, sup tt (λ (x : 𝟭), n)

 -- List with W-types

 definition list' (A : Type₀) : Type₀ := W (a : 𝟭 + A), sum.rec_on a (λ u, 𝟬) (λ a, 𝟭)

 definition nil' {A : Type₀} : list' A :=
   sup (inl(⋆)) (λ (x : 𝟬), empty.rec_on _ x)

 definition cons' {A : Type₀} : A → list' A → list' A := 
  λ a u, sup (inr(a)) (λ (x : 𝟭), u)

 -- Definition of double

 definition double' : ℕ' → ℕ' :=
 begin
  intro n, induction n with b u IH,
  induction b, apply zero', apply (succ' (succ' (IH ⋆)))
 end

 -- Theorem 5.3.1. 
 
 definition uniq_w_rec {B : A → Type} {E : (W (a : A), B a) → Type} (g h : Π (w : W (a : A), B a), E w) (e : Π (a : A) (f : B a → W (a : A), B a), (Π (b : B a), E (f b)) → E (sup a f)) (H₁ : Π (a : A) (f : B a → W (a : A), B a), g (sup a f) = e a f (λ b, g (f b)) )
  (H₂ : Π (a : A) (f : B a → W (a : A), B a), h (sup a f) = e a f (λ b, h (f b)) ) :
     g = h :=
 sorry
 
 --
