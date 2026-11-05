/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathZeroWeightIndex
import Verification.ZeroWeightMatrixBlock
import Verification.PathReductionConstantBlock

/-!
# Path Constant Block

The actual zero-weight Z summand is isolated by the full-rho path
contraction, at every path length. The formal coefficient action is therefore
needed only on the positive-weight Milnor--Witt objects.
-/

namespace Verification.PathConstantBlock

open Classical Verification.PathCoefficientRing Verification.PathEndpointCoordinates
  Verification.PathStratumGrading Verification.PathWeightFiltration Verification.PathZeroWeightIndex
  Verification.ZeroWeightMatrixBlock Verification.PathPureSpecialization
  Verification.PathFullComplex Verification.PathGradedFullReduction

noncomputable def zConstant (n : ℕ) := constantProjection (R:=Coeff) (zIndex n)
noncomputable def yConstant (a : ℕ) := constantProjection (R:=Coeff) (yIndex a)

theorem z_differential (r : Coeff) (n : ℕ) :
    zConstant n*(zMatrix g r n).transpose=0 ∧ (zMatrix g r n).transpose*zConstant n=0 := by
  have hd := transpose_degree _ _ (Verification.PathStratumGrading.zMatrix_degree g r n)
  have hn : ∀i : Verification.PathNormalizedBasis.NormalIndex Verification.PathEndpointWords.RightNormal n,
      -degree i≤0 := by intro i;change -(i.1.val.card:ℤ)≤0;omega
  exact ⟨annihilate_left (zIndex n) _
    (differential_row _ weight (zIndex n) _ hd hn (zIndex_degree n) (zIndex_weight n) (z_unique n)
      (zChain_weight g r n)),
    annihilate_right (zIndex n) _ (differential_column _ (zIndex n) _ hd hn (zIndex_degree n))⟩

theorem y_differential (r : Coeff) (a : ℕ) :
    yConstant a*(yMatrix g r a).transpose=0 ∧ (yMatrix g r a).transpose*yConstant a=0 := by
  have hd := transpose_degree _ _ (Verification.PathStratumGrading.yMatrix_degree g r a)
  have hn : ∀i : Verification.PathNormalizedBasis.NormalIndex Verification.PathEndpointWords.BothNormal (2*a),
      -degree i≤0 := by intro i;change -(i.1.val.card:ℤ)≤0;omega
  exact ⟨annihilate_left (yIndex a) _
    (differential_row _ weight (yIndex a) _ hd hn (yIndex_degree a) (yIndex_weight a) (y_unique a)
      (yChain_weight g r a)),
    annihilate_right (yIndex a) _ (differential_column _ (yIndex a) _ hd hn (yIndex_degree a))⟩

theorem z_pure_homotopy (n : ℕ) :
    zConstant n*(zData n).homotopy=0 ∧ (zData n).homotopy*zConstant n=0 :=
  ⟨annihilate_left (zIndex n) _ (homotopy_row _ weight (zIndex n) _ (zData n).homotopy_degree
    (zIndex_weight n) (z_unique n) (zData n).weight_preserving),
   annihilate_right (zIndex n) _ (homotopy_column _ weight (zIndex n) _ (zData n).homotopy_degree
    (zIndex_weight n) (z_unique n) (zData n).weight_preserving)⟩

theorem y_pure_homotopy (a : ℕ) :
    yConstant a*(yData a).homotopy=0 ∧ (yData a).homotopy*yConstant a=0 :=
  ⟨annihilate_left (yIndex a) _ (homotopy_row _ weight (yIndex a) _ (yData a).homotopy_degree
    (yIndex_weight a) (y_unique a) (yData a).weight_preserving),
   annihilate_right (yIndex a) _ (homotopy_column _ weight (yIndex a) _ (yData a).homotopy_degree
    (yIndex_weight a) (y_unique a) (yData a).weight_preserving)⟩

theorem z_full_isolated (n : ℕ) :
    (zConstant n*(zReduction n).homotopy=0 ∧ (zReduction n).homotopy*zConstant n=0) ∧
    (zConstant n*(zReduction n).inclusion=zConstant n ∧ (zReduction n).inclusion*zConstant n=zConstant n) ∧
    (zConstant n*(zReduction n).retraction=zConstant n ∧ (zReduction n).retraction*zConstant n=zConstant n) :=
  PathReductionConstantBlock.isolated _ _ _ _ _ _ _ _ _ _ _
    (z_differential 0 n) (z_pure_homotopy n) (z_differential rho n)

theorem y_full_isolated (a : ℕ) :
    (yConstant a*(yReduction a).homotopy=0 ∧ (yReduction a).homotopy*yConstant a=0) ∧
    (yConstant a*(yReduction a).inclusion=yConstant a ∧ (yReduction a).inclusion*yConstant a=yConstant a) ∧
    (yConstant a*(yReduction a).retraction=yConstant a ∧ (yReduction a).retraction*yConstant a=yConstant a) :=
  PathReductionConstantBlock.isolated _ _ _ _ _ _ _ _ _ _ _
    (y_differential 0 a) (y_pure_homotopy a) (y_differential rho a)

#print axioms zConstant
#print axioms yConstant
#print axioms z_differential
#print axioms y_differential
#print axioms z_pure_homotopy
#print axioms y_pure_homotopy
#print axioms z_full_isolated
#print axioms y_full_isolated

end Verification.PathConstantBlock
