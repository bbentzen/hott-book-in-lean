/-
Copyright (c) 2017 Bruno Bentzen. All rights reserved.
Released under the Apache License 2.0 (see "License");

Miscellaneous results
-/

-- Contractability:

-- Every contractable type A induce a contractible path A=A:
 
  definition contr_implies_loop_contr :
     isContr(A) → isContr(A = A) :=
 λ H, ⟨ refl A,
  λ p, ua_refl ⬝ ap ua
    (show typeq_refl A = idtoeqv p, from
      sigma_eq ⟨funext (λ x, ((pr2 H) x)⁻¹ ⬝ (pr2 H) (pr1 (idtoeqv p) x) ) ,
      (biinv_is_prop (pr1 (idtoeqv p))) _ (pr2 (idtoeqv p)) ⟩)
 ⬝ (ua_uniq p) ⟩ 

-- Every path type of a contractible type is contractible:

definition contr_implies_paths_contr :
     isContr(A) → Π (x y : A), isContr(x = y) :=
λ H, λ x y, ⟨ ((pr2 H) x)⁻¹ ⬝ (pr2 H) y , λ p, eq.rec_on p (left_inv _) ⟩

--
