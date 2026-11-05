/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LowerConeRetraction

/-!
# Rectangular Residual Retraction

Replace an actual zero residual projector by a proved rectangular free
basis splitting. All chain and homotopy equations are retained literally.
-/

namespace Verification.RectangularResidualRetraction

open Verification.LowerConeRetraction

variable {R ι κ : Type} [CommRing R] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]
variable (d : ι → ℤ) (D P : Matrix ι ι R) (F : Data d D P)
variable (A : Matrix ι κ R) (B : Matrix κ ι R)
variable (hAB : A*B=P) (hBA : B*A=1) (hzero : F.differential=0)

include hAB hBA in
theorem retraction_inclusion : (B*F.retraction)*(F.inclusion*A)=1 := by
  calc
    (B*F.retraction)*(F.inclusion*A)=B*(F.retraction*F.inclusion)*A := by simp only [Matrix.mul_assoc]
    _=B*P*A := by rw [F.retract]
    _=(B*A)*(B*A) := by rw [←hAB];simp only [Matrix.mul_assoc]
    _=1 := by rw [hBA,Matrix.one_mul]

omit [DecidableEq κ] in
include hAB in
theorem homotopy_identity : (F.inclusion*A)*(B*F.retraction)=1-D*F.homotopy-F.homotopy*D := by
  calc
    (F.inclusion*A)*(B*F.retraction)=F.inclusion*((A*B)*F.retraction) := by simp only [Matrix.mul_assoc]
    _=F.inclusion*F.retraction := by rw [hAB,F.retraction_support]
    _=1-D*F.homotopy-F.homotopy*D := F.homotopy_identity

omit [Fintype κ] [DecidableEq κ] in
include hzero in
theorem inclusion_chain : D*(F.inclusion*A)=0 := by
  rw [←Matrix.mul_assoc,F.inclusion_chain,hzero,Matrix.mul_zero,Matrix.zero_mul]

omit [Fintype κ] [DecidableEq κ] in
include hzero in
theorem retraction_chain : (B*F.retraction)*D=0 := by
  rw [Matrix.mul_assoc,F.retraction_chain,hzero,Matrix.zero_mul,Matrix.mul_zero]

#print axioms retraction_inclusion
#print axioms homotopy_identity
#print axioms inclusion_chain
#print axioms retraction_chain

end Verification.RectangularResidualRetraction
