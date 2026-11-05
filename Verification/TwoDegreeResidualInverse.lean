/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.TwoDegreeMatrixSupport

/-!
# Two Degree Residual Inverse

An actual left inverse of the residual first map extends to a generalized
inverse of the full ambient residual matrix; no unsupported coordinates enter.
-/

namespace Verification.TwoDegreeResidualInverse

open Verification.GradedPerturbation Verification.PerturbedHomologyModel
  Verification.GradedFixedProjection Verification.TwoDegreeMatrixSupport
  Verification.TwoDegreeFixedComplex

variable {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι]

noncomputable def inverseMatrix (d : ι → ℤ) (P : Matrix ι ι R)
    (hdP : Homogeneous d 0 P) (hPP : P*P=P)
    (L : fixedModule d P 0 →ₗ[R] fixedModule d P (-1)) : Matrix ι ι R :=
  LinearMap.toMatrix' ((fixedModule d P (-1)).subtype.comp
    (L.comp (projection d P hdP hPP 0)))

theorem generalized (d : ι → ℤ) (P S : Matrix ι ι R)
    (hd : Homogeneous d 1 S) (hdP : Homogeneous d 0 P) (hPP : P*P=P)
    (hPS : P*S=S) (hSP : S*P=S)
    (hP : ∀ i j,d i ≠ -1 → d i ≠ 0 → P i j=0)
    (L : fixedModule d P 0 →ₗ[R] fixedModule d P (-1))
    (hL : L.comp (firstMap d P S hd hPS)=LinearMap.id) :
    S*inverseMatrix d P hdP hPP L*S=S := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  let a := projection d P hdP hPP (-1) x
  let b : fixedModule d P 0 := ⟨S.mulVec x,image_degree d P S hd hPS hSP hP x,by
    rw [Matrix.mulVec_mulVec,hPS]⟩
  have hab : firstMap d P S hd hPS a=b := by
    apply Subtype.ext
    change S.mulVec (projection d P hdP hPP (-1) x).val=S.mulVec x
    rw [projection_val,Matrix.mulVec_mulVec,source_cut d P S hd hPS hSP hP]
  have hl : L b=a := by
    rw [← hab]
    exact LinearMap.congr_fun hL a
  change (S*inverseMatrix d P hdP hPP L*S).mulVec x=S.mulVec x
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec]
  change S.mulVec (Matrix.toLin' (LinearMap.toMatrix' _) (S.mulVec x))=S.mulVec x
  rw [Matrix.toLin'_toMatrix']
  change S.mulVec (L (projection d P hdP hPP 0 b.val)).val=b.val
  rw [projection_fixed,hl]
  exact congrArg Subtype.val hab

theorem inverse_degree (d : ι → ℤ) (P : Matrix ι ι R)
    (hdP : Homogeneous d 0 P) (hPP : P*P=P)
    (L : fixedModule d P 0 →ₗ[R] fixedModule d P (-1)) :
    Homogeneous d (-1) (inverseMatrix d P hdP hPP L) := by
  intro i j hij
  by_cases hi : d i = -1
  · have hj : d j ≠ 0 := by omega
    have hz : projection d P hdP hPP 0 (Pi.single j 1)=0 := by
      apply Subtype.ext
      rw [projection_val,Matrix.mulVec_single_one]
      funext k
      change (if d k=0 then P k j else 0)=0
      by_cases hk : d k=0
      · rw [if_pos hk,hdP k j (by omega)]
      · rw [if_neg hk]
    simp only [inverseMatrix,LinearMap.toMatrix'_apply,LinearMap.comp_apply,Submodule.subtype_apply]
    rw [show (fun k : ι => if k=j then (1:R) else 0)=Pi.single j 1 by
      funext k; simp [Pi.single_apply,eq_comm]]
    rw [hz,map_zero]
    rfl
  · simp only [inverseMatrix,LinearMap.toMatrix'_apply,LinearMap.comp_apply,Submodule.subtype_apply]
    exact (L (projection d P hdP hPP 0 (fun k => if k=j then 1 else 0))).property.1 i hi

#print axioms inverseMatrix
#print axioms generalized
#print axioms inverse_degree

end Verification.TwoDegreeResidualInverse
