/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GradedMatrixComplex
import Verification.ZeroWeightMatrixBlock

/-!
# Positive Matrix Restriction

Restricting an isolated constant block leaves literal positive-weight
matrix products unchanged. This is the algebra needed before assigning the
positive blocks K_j and the isolated block the separate object Z.
-/

namespace Verification.PositiveMatrixRestriction

open Verification.PathCoefficientRing Verification.ZeroWeightMatrixBlock

variable {ι κ ν : Type} [Fintype ι] [DecidableEq ι]

noncomputable def restrict (v : ι → ℕ) (w : κ → ℕ) (M : Matrix ι κ Coeff) :
    Matrix {i // 0<v i} {j // 0<w j} Coeff := fun i j=>M i.val j.val

theorem constant_column (z : ι) (F : Matrix ι ι Coeff)
    (hF : F*constantProjection z=constantProjection z) (i : ι) (hi : i≠z) : F i z=0 := by
  have he := congrArg (fun M : Matrix ι ι Coeff=>M i z) hF
  simpa [constantProjection,Matrix.mul_diagonal,Matrix.diagonal_apply,hi] using he

theorem positive_inclusion (w : ι → ℕ) (v : κ → ℕ) (z : ι)
    (hwz : w z=0) (hu : ∀i,w i=0 → i=z)
    (F : Matrix ι ι Coeff) (A : Matrix ι κ Coeff)
    (hF : F*constantProjection z=constantProjection z)
    (hA : ∀i k,w i≠v k → A i k=0)
    (i : ι) (k : κ) (hi : 0<w i) (hk : v k=0) : (F*A) i k=0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : w j=0
  · rw [hu j hj,constant_column z F hF i (by intro he;subst i;omega),zero_mul]
  · rw [hA j k (by omega),mul_zero]

theorem positive_retraction (w : ι → ℕ) (v : κ → ℕ) (z : ι)
    (hwz : w z=0) (hu : ∀i,w i=0 → i=z)
    (F : Matrix ι ι Coeff) (B : Matrix κ ι Coeff)
    (hF : F*constantProjection z=constantProjection z)
    (hB : ∀k i,v k≠w i → B k i=0)
    (k : κ) (j : ι) (hk : 0<v k) (hj : w j=0) : (B*F) k j=0 := by
  rw [hu j hj,Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i=z
  · subst i
    rw [hB k z (by omega),zero_mul]
  · rw [constant_column z F hF i hi,mul_zero]

omit [Fintype ι] [DecidableEq ι] in
theorem product [Fintype κ] (v : ι → ℕ) (w : κ → ℕ) (u : ν → ℕ)
    (M : Matrix ι κ Coeff) (N : Matrix κ ν Coeff)
    (hm : ∀i k,0<v i → w k=0 → M i k=0) :
    restrict v w M*restrict w u N=restrict v u (M*N) := by
  classical
  ext i j
  change (∑k : {k // 0<w k},M i.val k.val*N k.val j.val)=∑k,M i.val k*N k j.val
  apply Verification.GradedMatrixComplex.sum_supported (fun k=>0<w k)
    (fun k=>M i.val k*N k j.val)
  intro k hk
  rw [hm i.val k i.property (by omega),zero_mul]

omit [Fintype ι] in
theorem identity (w : ι → ℕ) : restrict w w (1 : Matrix ι ι Coeff)=1 := by
  classical
  ext i j
  change (1 : Matrix ι ι Coeff) i.val j.val=(1 : Matrix _ _ Coeff) i j
  by_cases he : i=j
  · subst j;simp
  · have hv : i.val≠j.val := fun h=>he (Subtype.ext h)
    simp [Matrix.one_apply,he,hv]

omit [Fintype ι] [DecidableEq ι] in
theorem degree (v : ι → ℕ) (w : κ → ℕ) (M : Matrix ι κ Coeff)
    (hm : PathGradedMatrices.Homogeneous (fun i=>(v i:ℤ)) (fun j=>(w j:ℤ)) M) :
    PathGradedMatrices.Homogeneous (fun i : {i // 0<v i}=>((v i.val-1:ℕ):ℤ))
      (fun j : {j // 0<w j}=>((w j.val-1:ℕ):ℤ)) (restrict v w M) := by
  intro i j
  have hi:=i.property
  have hj:=j.property
  convert hm i.val j.val using 1
  dsimp only
  omega

#print axioms restrict
#print axioms constant_column
#print axioms positive_inclusion
#print axioms positive_retraction
#print axioms product
#print axioms identity
#print axioms degree

end Verification.PositiveMatrixRestriction
