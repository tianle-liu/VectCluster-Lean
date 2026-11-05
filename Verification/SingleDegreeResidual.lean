/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PerturbedHomologyModel
import Verification.PureDegreeSurvivors

/-!
# Single Degree Residual

A degree-one residual differential with both supports in a degree-zero
projector is literally zero. Its homology is that same fixed module.
-/

namespace Verification.SingleDegreeResidual

open CategoryTheory Verification.GradedPerturbation Verification.PerturbedHomologyModel

variable {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem differential_zero (d : ι → ℤ) (P S : Matrix ι ι R)
    (hd : Homogeneous d 1 S) (hPS : P*S=S) (hSP : S*P=S)
    (hP : ∀ i j,d i ≠ 0 → P i j=0) : S=0 := by
  ext i j
  by_cases hi : d i=0
  · rw [← hSP,Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : d k=0
    · rw [hd i k (by omega),zero_mul]
    · rw [hP k j hk,mul_zero]
  · rw [← hPS,Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    rw [hP i k hi,zero_mul]

noncomputable def homologyIso (d : ι → ℤ) (P S : Matrix ι ι R)
    (hd : Homogeneous d 1 S) (hPS : P*S=S) (hSS : S*S=0) (hS : S=0) (p : ℤ) :
    (fixedComplex d P S hd hPS hSS).homology p ≅ ModuleCat.of R (fixedModule d P p) := by
  subst S
  exact Verification.PureDegreeSurvivors.zeroHomologyIso d P p

#print axioms differential_zero
#print axioms homologyIso

end Verification.SingleDegreeResidual
