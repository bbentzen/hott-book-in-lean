/-
Copyright (c) 2015 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");

Theorems and exercises of the HoTT book (Chapter 3)
-/

import .ch2

open prod bool sum unit eq ua nat

/- ************************************** -/
/-    Ch.3 Sets and Logic                 -/
/- ************************************** -/

/- §3.1 (Sets and n-types)  -/

 variables {A B C Z: Type} 

 -- Definition 3.1.1 :

 definition isSet (A : Type) : Type :=
   Π (x y : A) (p q : x = y), p = q

 -- Example 3.1.2

 definition unitalleq (x y : unit) : x = y := unit.rec_on x (unit.rec_on y (refl ⋆))

 definition unitset : isSet(unit) :=
     λ (x y : unit) (p q : x = y), ((transport _ (ua (@unit_equiv x y))⁻¹ (λ x y, unitalleq x y)) p q)

 -- Example 3.1.3

 example : isSet(empty) :=
 λ (x y : empty) (p q : x=y), (empty.rec_on _ x)

 -- Example 3.1.4

 definition emptyalleq (x y : empty) : x = y := empty.rec_on _ x

/- example : isSet(ℕ) :=
 by intro m n p q; induction m; induction n; exact (transport _ (ua (nat_eq 0 0))⁻¹ (λ x y, unitalleq x y) p q);
   exact (transport _ (ua (nat_eq 0 (succ a)))⁻¹ (λ x y, emptyalleq x y) p q); induction n;
   exact (transport _ (ua (nat_eq (succ a) 0))⁻¹ (λ x y, emptyalleq x y) p q)

-/

 -- 

