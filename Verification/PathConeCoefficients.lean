/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathSplitConeData
import Verification.PathEndpointCoordinates
import Mathlib.Data.Matrix.Block

/-!
# Path Cone Coefficients

Converting the actual recursive split module into a literal finite block
matrix. The off-diagonal block is computed from the original connecting map.
-/

namespace Verification.PathConeCoefficients

open Verification.PathEndpointCoordinates Verification.PathSplitConeData

variable {R C O : Type*} [CommRing R]
variable [AddCommGroup C] [Module R C] [AddCommGroup O] [Module R O]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

noncomputable def pairCoordinates (E : C ≃ₗ[R] (ι → R)) (F : O ≃ₗ[R] (κ → R)) :
    (C × O) ≃ₗ[R] (ι ⊕ κ → R) :=
  (E.prodCongr F).trans (LinearEquiv.sumArrowLequivProdArrow ι κ R R).symm

noncomputable def rectangularMatrix (E : C ≃ₗ[R] (ι → R)) (F : O ≃ₗ[R] (κ → R))
    (T : O →ₗ[R] C) : Matrix ι κ R :=
  LinearMap.toMatrix' (E.toLinearMap.comp (T.comp F.symm.toLinearMap))

omit [Fintype ι] [DecidableEq ι] in
theorem rectangular_mulVec (E : C ≃ₗ[R] (ι → R)) (F : O ≃ₗ[R] (κ → R))
    (T : O →ₗ[R] C) (x : κ → R) :
    (rectangularMatrix E F T).mulVec x=E (T (F.symm x)) := by
  exact LinearMap.congr_fun (Matrix.toLin'_toMatrix' _) x

theorem matrixOf_mulVec (E : C ≃ₗ[R] (ι → R)) (D : C →ₗ[R] C) (x : ι → R) :
    (matrixOf E D).mulVec x=E (D (E.symm x)) :=
  rectangular_mulVec E E D x

/-- The original transported block operator has these exact four matrix blocks. -/
theorem block_matrix (E : C ≃ₗ[R] (ι → R)) (F : O ≃ₗ[R] (κ → R))
    (DC : C →ₗ[R] C) (DO : O →ₗ[R] O) (T : O →ₗ[R] C) :
    matrixOf (pairCoordinates E F) (block DC DO T)=
      Matrix.fromBlocks (matrixOf E DC) (rectangularMatrix E F T) 0 (matrixOf F DO) := by
  classical
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  change (matrixOf (pairCoordinates E F) (block DC DO T)).mulVec x=_
  rw [matrixOf_mulVec]
  change _=(Matrix.fromBlocks (matrixOf E DC) (rectangularMatrix E F T) 0 (matrixOf F DO)).mulVec x
  rw [Matrix.fromBlocks_mulVec,matrixOf_mulVec,rectangular_mulVec,matrixOf_mulVec,Matrix.zero_mulVec,zero_add]
  funext i
  cases i with
  | inl i =>
    change E (DC (E.symm (x ∘ Sum.inl))+T (F.symm (x ∘ Sum.inr))) i=
      (E (DC (E.symm (x ∘ Sum.inl)))+E (T (F.symm (x ∘ Sum.inr)))) i
    rw [map_add]
  | inr i => rfl

omit [Fintype ι] [DecidableEq ι] in
/-- A proved actual intertwiner gives equality of the two transported matrices. -/
theorem matrixOf_equivalence (G : C ≃ₗ[R] O) (F : O ≃ₗ[R] (κ → R))
    (D : C →ₗ[R] C) (E : O →ₗ[R] O)
    (h : G.toLinearMap.comp D=E.comp G.toLinearMap) :
    matrixOf (G.trans F) D=matrixOf F E := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  change (matrixOf (G.trans F) D).mulVec x=(matrixOf F E).mulVec x
  rw [matrixOf_mulVec,matrixOf_mulVec]
  change F (G (D (G.symm (F.symm x))))=F (E (F.symm x))
  have hh := LinearMap.congr_fun h (G.symm (F.symm x))
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply] at hh
  rw [hh]

#print axioms pairCoordinates
#print axioms rectangularMatrix
#print axioms rectangular_mulVec
#print axioms matrixOf_mulVec
#print axioms block_matrix
#print axioms matrixOf_equivalence

end Verification.PathConeCoefficients
