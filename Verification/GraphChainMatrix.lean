/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphChainCochain
import Verification.GraphCoverGrading

/-!
# Graph Chain Matrix

Actual finite graph-chain matrices and the literal coordinate conjugacy
between their transposes and the already defined independence cochains.
-/

namespace Verification.GraphChainMatrix

open Classical
open Verification.GraphCover Verification.GraphSimplexChains
  Verification.GraphBlocks Verification.GraphBlockComplex
  Verification.GraphCoverMatrices Verification.GraphCoverGrading
  Verification.GraphChainCochain Verification.GradedPerturbation

variable {R : Type} [CommRing R] {V C : Type}
  [Fintype V] [LinearOrder V] [DecidableEq C]
  (G : SimpleGraph V) (c : V → C) (T : Finset V)

/-- The original augmented boundary matrix, independently defined by signed deletion. -/
noncomputable def chainMatrix : Matrix (Simplex G T) (Simplex G T) R :=
  coefficientMatrix G T (boundary G T)

theorem chainMatrix_entry (J K : Simplex G T) :
    chainMatrix (R := R) G T J K=basisBoundary (R := R) G T K J := by
  rw [chainMatrix,coefficientMatrix_apply]
  simp only [boundary,Finsupp.linearCombination_single,one_smul]

theorem chainMatrix_square : chainMatrix (R := R) G T*chainMatrix G T=0 := by
  rw [chainMatrix,←map_mul]
  change coefficientMatrix G T ((boundary (R := R) G T).comp (boundary G T))=0
  rw [boundary_squared,map_zero]

theorem chainMatrix_degree : Homogeneous (degree G T) 1 (chainMatrix (R := R) G T) := by
  intro J K h
  rw [chainMatrix_entry]
  apply basisBoundary_degree G T K J
  intro he
  apply h
  simp only [degree]
  omega

/-- Augmented chain degree n-1 is represented by cochain degree -n. -/
noncomputable def chainComplex : CochainComplex (ModuleCat R) ℤ :=
  matrixComplex (degree G T) (chainMatrix G T) (chainMatrix_degree G T) (chainMatrix_square G T)

/-- Actual cochain coefficients, reindexed by the exact chain simplex and made into finite functions. -/
noncomputable def cochainCoordinates :
    (SimplexIndex G c (T,∅) →₀ R) ≃ₗ[R] (Simplex G T → R) :=
  (Finsupp.domLCongr (chainCochainIndex G c T).symm).trans
    (Finsupp.linearEquivFunOnFinite R R _)

omit [LinearOrder V] in
theorem cochainCoordinates_apply (f : SimplexIndex G c (T,∅) →₀ R) (J : Simplex G T) :
    cochainCoordinates G c T f J=f (chainCochainIndex G c T J) := by
  change (Finsupp.domLCongr (R := R) (chainCochainIndex G c T).symm f) J=_
  simp only [Finsupp.domLCongr_apply, Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply, Equiv.symm_symm]

theorem cochainCoordinates_single (J : Simplex G T) (r : R) :
    cochainCoordinates G c T (Finsupp.single (chainCochainIndex G c T J) r)=Pi.single J r := by
  simp only [cochainCoordinates,LinearEquiv.trans_apply,Finsupp.domLCongr_single,
    Equiv.symm_apply_apply,Finsupp.linearEquivFunOnFinite_single]

/-- Literal finite-coordinate comparison, on every coefficient, of the original two operators. -/
theorem cochainCoordinates_differential :
    (Matrix.toLin' (chainMatrix (R := R) G T).transpose).comp (cochainCoordinates G c T).toLinearMap=
      (cochainCoordinates G c T).toLinearMap.comp (simplexDifferential R G c (T,∅)) := by
  apply Finsupp.lhom_ext
  intro K r
  obtain ⟨K,rfl⟩ := (chainCochainIndex G c T).surjective K
  have hs : Finsupp.single (chainCochainIndex G c T K) r=
      r • Finsupp.single (chainCochainIndex G c T K) (1 : R) := by simp
  rw [hs,map_smul,map_smul]
  congr 1
  funext J
  change ((chainMatrix (R := R) G T).transpose).mulVec
    (cochainCoordinates G c T (Finsupp.single (chainCochainIndex G c T K) 1)) J=_
  rw [cochainCoordinates_single,Matrix.mulVec_single_one]
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [cochainCoordinates_apply]
  simp only [simplexDifferential,Finsupp.linearCombination_single,one_smul,
    Matrix.transpose_transpose]
  rw [chainMatrix_entry,incidence_transpose]

#print axioms chainMatrix
#print axioms chainMatrix_entry
#print axioms chainMatrix_square
#print axioms chainMatrix_degree
#print axioms chainComplex
#print axioms cochainCoordinates
#print axioms cochainCoordinates_apply
#print axioms cochainCoordinates_single
#print axioms cochainCoordinates_differential

end Verification.GraphChainMatrix
