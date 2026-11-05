/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GradedSurvivorBasis

/-!
# Graded Fixed Projection

The actual projection from all finite coordinates onto one degree of an
idempotent's fixed module.
-/

namespace Verification.GradedFixedProjection

open Verification.GradedPerturbation Verification.GradedSurvivorBasis

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def projection (d : ι → ℤ) (P : Matrix ι ι R)
    (hd : Homogeneous d 0 P) (hP : P*P=P) (p : ℤ) :
    (ι → R) →ₗ[R] Verification.PerturbedHomologyModel.fixedModule d P p :=
  (LinearEquiv.ofEq _ _ (fixedModule_cut d P hd p)).toLinearMap.comp
    (Verification.SurvivorBaseChange.projection (cut d p P) (cut_square d P hd hP p))

theorem projection_val (d : ι → ℤ) (P : Matrix ι ι R)
    (hd : Homogeneous d 0 P) (hP : P*P=P) (p : ℤ) (x : ι → R) :
    (projection d P hd hP p x).val=(cut d p P).mulVec x := rfl

theorem projection_fixed (d : ι → ℤ) (P : Matrix ι ι R)
    (hd : Homogeneous d 0 P) (hP : P*P=P) (p : ℤ)
    (x : Verification.PerturbedHomologyModel.fixedModule d P p) :
    projection d P hd hP p x.val=x := by
  apply Subtype.ext
  rw [projection_val]
  change Matrix.toLin' (cut d p P) x.val=x.val
  rw [cut_apply]
  change Verification.GradedHomologyTF.degreePart d p (P.mulVec x.val)=x.val
  rw [x.property.2]
  exact Verification.GradedHomologyTF.degreePart_fixed d p ⟨x.val,x.property.1⟩

#print axioms projection
#print axioms projection_val
#print axioms projection_fixed

end Verification.GradedFixedProjection
