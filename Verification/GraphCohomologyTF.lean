/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphBlockComplex
import Verification.NatFinsuppHomology

/-!
# Graph Cohomology TF

The intermediate all-induced independence-cohomology TF condition, expressed
on the literal augmented cochain complexes already constructed. Labeled color
blocks are identified with those same induced complexes before TF is transported.
-/

namespace Verification.GraphCohomologyTF

open Classical CategoryTheory
open Verification.GraphBlocks Verification.GraphBlockComplex

variable {R : Type} [CommRing R] [IsDomain R]
  {V C : Type} [Fintype V] [Fintype C] [LinearOrder V] [LinearOrder C]
  (G : SimpleGraph V) (c : V → C)

/-- TF of actual augmented cohomology for every induced vertex set. -/
def CochainGraphTF : Prop := ∀ (T : Finset V) (p : ℕ),
  NoZeroSMulDivisors R ((simplexComplex R G c (T,∅)).homology p)

omit [Fintype V] [Fintype C] [LinearOrder V] in
/-- Empty frozen set leaves exactly the selected induced vertex set. -/
theorem available_empty (T : Finset V) : available c T ∅=T := by
  simp [available]

/-- The literal simplex-index bijection to the corresponding induced vertex set. -/
def availableIndexEquiv (SF : Finset V × Finset C) :
    SimplexIndex G c SF ≃ SimplexIndex G c (available c SF.1 SF.2,∅) where
  toFun J := ⟨J.val,J.property.1,by rw [available_empty]; exact J.property.2⟩
  invFun J := ⟨J.val,J.property.1,by simpa only [available_empty] using J.property.2⟩
  left_inv J := by apply Subtype.ext; rfl
  right_inv J := by apply Subtype.ext; rfl

omit [Fintype V] [Fintype C] in
theorem availableIndex_add (SF : Finset V × Finset C) (J : SimplexIndex G c SF)
    (i : V) (hi : simplexCanAdd G c SF J i)
    (hj : simplexCanAdd G c (available c SF.1 SF.2,∅) (availableIndexEquiv G c SF J) i) :
    availableIndexEquiv G c SF (addSimplex G c SF J i hi)=
      addSimplex G c (available c SF.1 SF.2,∅) (availableIndexEquiv G c SF J) i hj := by
  apply Subtype.ext
  rfl

omit [IsDomain R] [Fintype C] in
theorem availableBasis_differential (SF : Finset V × Finset C) (J : SimplexIndex G c SF) :
    Finsupp.domLCongr (R := R) (availableIndexEquiv G c SF)
      (simplexBasisDifferential R G c SF J)=
    simplexBasisDifferential R G c (available c SF.1 SF.2,∅) (availableIndexEquiv G c SF J) := by
  unfold simplexBasisDifferential
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hh : simplexCanAdd G c SF J i ↔
      simplexCanAdd G c (available c SF.1 SF.2,∅) (availableIndexEquiv G c SF J) i := by
    simp only [simplexCanAdd,available_empty]
    rfl
  by_cases hi : simplexCanAdd G c SF J i
  · have hj := hh.mp hi
    simp only [dif_pos hi,dif_pos hj,Finsupp.domLCongr_single,availableIndex_add]
    rfl
  · have hj := mt hh.mpr hi
    simp only [dif_neg hi,dif_neg hj,map_zero]

omit [IsDomain R] [Fintype C] in
theorem available_differential (SF : Finset V × Finset C) :
    (Finsupp.domLCongr (R := R) (availableIndexEquiv G c SF)).toLinearMap.comp
      (simplexDifferential R G c SF)=
    (simplexDifferential R G c (available c SF.1 SF.2,∅)).comp
      (Finsupp.domLCongr (R := R) (availableIndexEquiv G c SF)).toLinearMap := by
  apply Finsupp.lhom_ext
  intro J r
  simp only [LinearMap.comp_apply,simplexDifferential,Finsupp.linearCombination_single,
    LinearEquiv.coe_coe,map_smul,availableBasis_differential,Finsupp.domLCongr_single]

/-- A color block and its induced independence cochain complex are actually chain-isomorphic. -/
noncomputable def availableComplexIso (SF : Finset V × Finset C) :
    simplexComplex R G c SF ≅ simplexComplex R G c (available c SF.1 SF.2,∅) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => (degreeReindex R (simplexDegree G c SF)
      (simplexDegree G c (available c SF.1 SF.2,∅))
      (availableIndexEquiv G c SF) (fun _ => rfl) p).toModuleIso)
    (by
      intro p q hpq
      have he : p+1=q := hpq
      subst q
      simp only [simplexComplex,gradedComplex,CochainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      apply Subtype.ext
      exact (LinearMap.congr_fun (available_differential G c SF) f.val).symm)

omit [IsDomain R] [Fintype C] in
/-- No extra TF hypothesis is added for the labeled `(S,F)` blocks. -/
theorem block_tf (h : CochainGraphTF (R := R) G c) (SF : Finset V × Finset C) (p : ℕ) :
    NoZeroSMulDivisors R ((simplexComplex R G c SF).homology p) := by
  letI := h (available c SF.1 SF.2) p
  let e : ((simplexComplex R G c SF).homology p) ≃ₗ[R]
      ((simplexComplex R G c (available c SF.1 SF.2,∅)).homology p) :=
    ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) p).mapIso
    (availableComplexIso (R := R) G c SF)).toLinearEquiv
  exact Function.Injective.noZeroSMulDivisors e e.injective e.map_zero e.map_smul

omit [IsDomain R] in
/-- The proved finite product decomposition transfers actual induced graph TF. -/
theorem monomial_tf (h : CochainGraphTF (R := R) G c) (p : ℕ) :
    NoZeroSMulDivisors R ((monomialComplex R G c).homology p) := by
  letI := fun SF => block_tf G c h SF p
  let e := (uncompressedHomologyIso R G c p).toLinearEquiv
  exact Function.Injective.noZeroSMulDivisors e e.injective e.map_zero e.map_smul

/-- The full literal monomial differential has TF total kernel/image homology. -/
theorem monomial_total_tf (h : CochainGraphTF (R := R) G c) :
    NoZeroSMulDivisors R (Verification.IntegralSplitting.Homology
      (monomialDifferential (G := G) (c := c) R)) := by
  apply Verification.NatFinsuppHomology.total_tf (monomialDegree G c)
    (monomialDifferential R) (monomialDifferential_degree R G c)
    (monomialDifferential_square R G c)
  exact monomial_tf G c h

#print axioms CochainGraphTF
#print axioms available_empty
#print axioms availableIndexEquiv
#print axioms availableIndex_add
#print axioms availableBasis_differential
#print axioms available_differential
#print axioms availableComplexIso
#print axioms block_tf
#print axioms monomial_tf
#print axioms monomial_total_tf

end Verification.GraphCohomologyTF
