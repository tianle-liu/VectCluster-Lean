/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathGradedFullReduction
import Verification.IsolatedPerturbationSummand

/-!
# Path Reduction Constant Block

The already constructed full-rho perturbation leaves every isolated
constant block literally fixed. No coefficient action on that block is used.
-/

namespace Verification.PathReductionConstantBlock

open Verification.PathCoefficientRing Verification.PathGradedFullReduction
  Verification.GradedPerturbation Verification.FinitePerturbation

variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable (d : ι → ℤ) (w : ι → ℕ) (A D : Matrix ι ι Coeff)
variable (P : Verification.WeightedPureContraction.Data d w A)
variable (hd : Homogeneous d 1 D) (hD : D*D=0)
variable (b : ℕ) (hw : ∀i,w i≤b) (hV : ∀i j,w i≤w j → (D-A) i j=0)
variable (E : Matrix ι ι Coeff) (hA : E*A=0 ∧ A*E=0)
  (hH : E*P.homotopy=0 ∧ P.homotopy*E=0) (hDE : E*D=0 ∧ D*E=0)

include hA hH hDE in
theorem isolated :
    let F := reduction d w A D P hd hD b hw hV
    (E*F.homotopy=0 ∧ F.homotopy*E=0) ∧
    (E*F.inclusion=E ∧ F.inclusion*E=E) ∧
    (E*F.retraction=E ∧ F.retraction*E=E) := by
  have hEV : E*(D-A)=0 := by rw [Matrix.mul_sub,hDE.1,hA.1,sub_self]
  have hVE : (D-A)*E=0 := by rw [Matrix.sub_mul,hDE.2,hA.2,sub_self]
  let q := leftWeightUnit P.homotopy (D-A) w b hw P.weight_preserving hV
  exact ⟨IsolatedPerturbationSummand.homotopy_isolated P.homotopy (D-A) E hH.1 hH.2 q,
    IsolatedPerturbationSummand.inclusion_isolated A P.homotopy (D-A) E hA.1 hA.2 hH.1 hH.2 hVE q,
    IsolatedPerturbationSummand.retraction_isolated A P.homotopy (D-A) E hA.1 hA.2 hH.1 hH.2 hEV q rfl⟩

#print axioms isolated

end Verification.PathReductionConstantBlock
