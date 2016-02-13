/-
Copyright (c) 2015 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");

Theorems and exercises of the HoTT book (Chapter 1)
-/

/- ************************************** -/
/-        Ch.1    Type Theory             -/
/- ************************************** -/

open prod bool sum eq

variables {A B C D: Type} 

definition id (A : Type) : A → A := λ (x : A), x

/- §1.5 (Product uniqueness principle)  -/

 definition uppt (x : A × B) :
     x = (pr1  x, pr2 x) :=
 prod.rec_on x (λ a b, refl _)

/- §1.8 (Boolean uniqueness principle)  -/

 definition bbuni (x : bool) :
     sum (x=ff) (x=tt) :=
 bool.rec_on x (inl (refl ff)) (inr (refl tt)) 

/- §1.11 (Proposition-as-types example) -/

 definition de_morgan (p : (A → empty) × (B → empty)) : 
    ( A + B ) → empty :=
 prod.rec_on p (λ x y, 
  (λ (z : A + B),  sum.rec_on z (λ a, x a) (λ b, y b) ) )

/-- Ch.1 Exercises --/

 definition comp (g : B → C) (f : A → B) : A → C := λ (x : A), g (f (x))

 notation  g `∘` f  := comp g f
 
 -- Exercise 1

 definition comp_assoc (f : A → B) (g : B → C) (h : C → D) :  h ∘ (g ∘ f) = (h ∘ g) ∘ f :=   
 refl (h ∘ (g ∘ f))

---
