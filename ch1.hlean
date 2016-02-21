/-
Copyright (c) 2015 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");

Theorems and exercises of the HoTT book (Chapter 1)
-/

/- ************************************** -/
/-        Ch.1    Type Theory             -/
/- ************************************** -/

 open eq

 variables {A B C D: Type} 

/- §1.4 Dependent function types (Π-Types) -/

 definition swap (A B C: Type) : (A → B → C) → (B → A → C) :=
   λ f b a, f a b

 --

/- §1.5 Product types -/
 
 open prod unit

 notation `𝟭` := unit
 notation `⋆` := star

 -- Product uniqueness principle

 definition uppt (x : A × B) :
     x = (pr1  x, pr2 x) :=
 prod.rec_on x (λ a b, refl _)

--

/- §1.6 Dependent pair types (Σ-Types) -/

 open sigma
 
 definition ac (A B : Type) (R : A → B → Type) :
   (Π (x : A), Σ (y : B), R x y ) → (Σ (f : A → B), Π (x : A), R x (f x))  :=
 λ g, ⟨ λ x, pr1 (g x), λ x, pr2 (g x)⟩

 definition magma : Type := Σ (A : Type), A → A → A

 definition pointedmagma : Type := (Σ (A : Type), A → A → A) × A

 --

/- §1.7 Coproduct types -/

 open sum empty

 notation `𝟬` := empty

 --

/- §1.8 The type of booleans -/

 open bool

 notation `𝟮` := bool

 definition upbool (x : 𝟮) :
     (x = ff) + (x = tt) :=
 bool.rec_on x (inl (refl ff)) (inr (refl tt)) 

 --

/- §1.9 The natural numbers  -/

 open nat

 definition double : Π (x : ℕ ), ℕ
 | double 0 := 0
 | double (succ n) := succ (succ (double n))

 definition add (m n : ℕ) : ℕ :=
   nat.rec m (λ n add_n, succ (add_n)) n

 definition assoc (i j k : ℕ) :
     i + (j + k) = (i + j) + k :=
 by induction k with k IH; reflexivity;
   apply (calc
     i + (j + (succ k)) = i + (succ (j + k)) : idp
     ... = succ (i + (j + k)) : idp
     ... = succ ((i + j) + k) : IH)

/- §1.11 Proposition-as-types -/

 definition dmorganpt: 
    (A → 𝟬) × (B → 𝟬) → ( A + B ) → 𝟬 :=
 λ p, prod.rec_on p (λ x y, (λ (z : A + B),  sum.rec_on z (λ a, x a) (λ b, y b) ) )

 definition dmorgansum: 
    (A + B → 𝟬) → (A → 𝟬) × (B → 𝟬) :=
 λ p, ( λ a, p (inl a) , λ b, p (inr b) )

 example (P Q : A → Type) : 
    (Π (x : A), P (x) × Q (x) ) → (Π (x : A), P (x)) × (Π (x : A), Q (x)) :=
 λ p, ( λ x, pr1 (p x), λ x, pr2 (p x) )

 definition leq (n m : ℕ) : Type₀ := Σ (k : ℕ), n + k = m

 notation n `≤` m := leq n m

 definition less (n m : ℕ) : Type₀ := Σ (k : ℕ), n + (succ k) = m
 
 notation n `<` m := less n m

 definition semigroup : Type := Σ (A : Type), A → A → A

/- Exercises -/

 -- 1.1 Given functions f : A ! B and g : B ! C, define their composite g ∘ f : A → C. Show that we have h ∘ (g ∘ f) = (h ∘ g) ∘ f.

 definition comp (g : B → C) (f : A → B) : A → C := λ (x : A), g (f (x))

 notation  g `∘` f  := comp g f
 
 definition comp_assoc (f : A → B) (g : B → C) (h : C → D) :
   h ∘ (g ∘ f) = (h ∘ g) ∘ f := idp

 --

 -- 1.11 Show that for any type A, we have ¬¬¬A → ¬A.

 definition ndne :
   (((A → 𝟬) → 𝟬) → 𝟬) → (A → 𝟬) :=
 λ p a, p ((λ a p, p a) a)

 --

 -- 1.13 Using the proposition-as-types, derive the double negation of the principle of excluded middle, i.e. prove (not (not (P or not P)))

 definition dnlem :
  ((A + (A → 𝟬)) → 𝟬) → 𝟬 :=
 λ p, (pr2 (dmorgansum p)) (pr1 (dmorgansum p))

 --

 -- 1.15 Show that the indiscernability of identicals follows from path induction

 example (a b : A) (P : A → Type) : a = b → P a → P b :=
   λ p u, eq.rec_on p u

 --

 /-- Other useful lemmas --/

  definition id (A : Type) : A → A := λ (x : A), x

  definition ant (m : ℕ) : ℕ :=
   nat.rec 0 (λ m ant_m, ant_m) m

