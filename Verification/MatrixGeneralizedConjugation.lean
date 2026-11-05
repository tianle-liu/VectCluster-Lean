/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Matrix Generalized Conjugation

Generalized inverses transport along a proved finite coefficient
intertwiner, using the literal source and target matrices.
-/

namespace Verification.MatrixGeneralizedConjugation

variable {R ι κ : Type*} [CommRing R]
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

noncomputable def transport (E : (ι → R) ≃ₗ[R] (κ → R)) (G : Matrix κ κ R) : Matrix ι ι R :=
  LinearMap.toMatrix' (E.symm.toLinearMap.comp ((Matrix.toLin' G).comp E.toLinearMap))

theorem generalized (E : (ι → R) ≃ₗ[R] (κ → R)) (A : Matrix ι ι R) (B G : Matrix κ κ R)
    (hE : (Matrix.toLin' B).comp E.toLinearMap=E.toLinearMap.comp (Matrix.toLin' A))
    (hG : B*G*B=B) : A*transport E G*A=A := by
  have he (x : ι → R) : B.mulVec (E x)=E (A.mulVec x) := LinearMap.congr_fun hE x
  have hi (y : κ → R) : A.mulVec (E.symm y)=E.symm (B.mulVec y) := by
    apply E.injective
    rw [← he,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  change (A*transport E G*A).mulVec x=A.mulVec x
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec]
  change A.mulVec (Matrix.toLin' (LinearMap.toMatrix' _) (A.mulVec x))=A.mulVec x
  rw [Matrix.toLin'_toMatrix']
  change A.mulVec (E.symm (G.mulVec (E (A.mulVec x))))=A.mulVec x
  rw [hi,← he,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,hG,he,LinearEquiv.symm_apply_apply]

#print axioms transport
#print axioms generalized

end Verification.MatrixGeneralizedConjugation
