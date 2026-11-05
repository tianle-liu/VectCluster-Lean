/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphLowBoundary
import Verification.GradedHomologyTF

/-!
# Graph Low Homology

Reduced H₋₁ and H₀ of the actual graph-chain matrix complex are torsion-free.
The low boundary preimages are transported through the literal finite basis,
then projected into the required incoming degree.
-/

namespace Verification.GraphLowHomology

open Classical CategoryTheory
open Verification.GraphCover Verification.GraphSimplexChains Verification.GraphCoverMatrices
  Verification.GraphCoverGrading Verification.GraphChainMatrix Verification.GraphLowBoundary
  Verification.GradedPerturbation Verification.PerturbedHomologyModel Verification.GradedHomologyTF

variable {R V : Type} [CommRing R] [IsDomain R] [Fintype V] [LinearOrder V]
  (G : SimpleGraph V) (T : Finset V)

omit [IsDomain R] in
/-- Literal coefficient identity for the independently defined boundary matrix. -/
theorem boundary_matrix (x : Simplex G T →₀ R) :
    (chainMatrix (R := R) G T).mulVec x=boundary G T x := by
  simpa only [chainMatrix,coefficientMatrix,LinearMap.toMatrixAlgEquiv_apply,
    Finsupp.basisSingleOne_repr] using
    (boundary (R := R) G T).toMatrix_mulVec_repr Finsupp.basisSingleOne Finsupp.basisSingleOne x

/-- The low-dimensional saturation proof survives the actual Finsupp-to-function coordinates. -/
theorem low_matrix_saturated (n : ℕ) (hn : n ≤ 1) (a : R) (ha : a ≠ 0)
    (x : degreeModule (R := R) (degree G T) (-(n : ℤ)))
    (hy : ∃ y : Simplex G T → R, (chainMatrix (R := R) G T).mulVec y=a • x.val) :
    ∃ y : Simplex G T → R, (chainMatrix (R := R) G T).mulVec y=x.val := by
  let e := Finsupp.linearEquivFunOnFinite R R (Simplex G T)
  let f := e.symm x.val
  have hf : ∀ J, J.val.card ≠ n → f J=0 := by
    intro J hJ
    exact x.property J (by simp only [degree]; omega)
  obtain ⟨y,hy⟩ := hy
  have hby : ∃ z, boundary G T z=a • f := by
    refine ⟨e.symm y,?_⟩
    apply e.injective
    change (boundary G T (e.symm y) : Simplex G T → R)=_
    rw [←boundary_matrix]
    change (chainMatrix (R := R) G T).mulVec (e (e.symm y))=e (a • e.symm x.val)
    rw [e.apply_symm_apply,map_smul,e.apply_symm_apply]
    exact hy
  have hl : ∃ z, boundary G T z=f := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl
    · exact zero_boundary_saturated G T a ha f hf hby
    · exact one_boundary_saturated G T a ha f hf hby
  obtain ⟨z,hz⟩ := hl
  refine ⟨e z,?_⟩
  change (chainMatrix (R := R) G T).mulVec (z : Simplex G T → R)=x.val
  rw [boundary_matrix,hz]
  exact e.apply_symm_apply x.val

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [IsDomain R] [Fintype V] [LinearOrder V] in
/-- Saturation in one actual homogeneous component supplies its categorical homology TF. -/
theorem homology_tf_of_degree_saturation (deg : ι → ℤ) (D : Matrix ι ι R)
    (hd : Homogeneous deg 1 D) (hsq : D*D=0) (p : ℤ)
    (hsat : ∀ (a : R), a ≠ 0 → ∀ (x : degreeModule (R := R) deg p),
      (∃ y, D.mulVec y=a • x.val) → ∃ y, D.mulVec y=x.val) :
    NoZeroSMulDivisors R ((matrixComplex deg D hd hsq).homology p) := by
  let K := matrixComplex deg D hd hsq
  let S := K.sc' (p-1) p (p+1)
  have hs : NoZeroSMulDivisors R S.homology := by
    apply shortComplex_tf_of_boundaries S
    intro a ha x _ hax
    have hy : ∃ y, D.mulVec y=a • x.val := by
      obtain ⟨y,hy⟩ := hax
      change (K.d (p-1) p) y=a • x at hy
      rw [matrixComplex_d deg D hd hsq (p-1) p (by omega)] at hy
      exact ⟨y.val,congrArg Subtype.val hy⟩
    obtain ⟨y,hy⟩ := hsat a ha x hy
    refine ⟨⟨degreePart deg (p-1) y,degreePart_mem deg (p-1) y⟩,?_⟩
    change (K.d (p-1) p) _=x
    rw [matrixComplex_d deg D hd hsq (p-1) p (by omega)]
    apply Subtype.ext
    change Matrix.toLin' D (degreePart deg (p-1) y)=x.val
    rw [degreePart_differential deg D hd,show p-1+1=p by omega]
    change degreePart deg p (D.mulVec y)=_
    rw [hy,degreePart_fixed]
  letI := hs
  let e := (K.homologyIsoSc' (p-1) p (p+1) (by simp) (by simp)).toLinearEquiv
  exact Function.Injective.noZeroSMulDivisors e e.injective e.map_zero e.map_smul

/-- The actual reduced graph homology in dimensions -1 and 0 is torsion-free. -/
theorem low_homology_tf (n : ℕ) (hn : n ≤ 1) :
    NoZeroSMulDivisors R ((chainComplex (R := R) G T).homology (-(n : ℤ))) :=
  homology_tf_of_degree_saturation (degree G T) (chainMatrix G T)
    (chainMatrix_degree G T) (chainMatrix_square G T) (-(n : ℤ))
    (low_matrix_saturated G T n hn)

#print axioms boundary_matrix
#print axioms low_matrix_saturated
#print axioms homology_tf_of_degree_saturation
#print axioms low_homology_tf

end Verification.GraphLowHomology
