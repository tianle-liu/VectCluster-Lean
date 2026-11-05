/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathPureInduction
import Verification.FilteredZeroReduction
import Verification.PathPureMatrixWeight
import Verification.PathMatrixPerturbation
import Verification.PathWeightBounds

/-!
# Path Full Homology

All-length vanishing and the closed-form finite free homology of the
original full-rho path chain matrices, over every commutative coefficient
ring satisfying g²=1 and (1+g)rho=0.
-/

namespace Verification.PathFullHomology

open Classical CategoryTheory Verification.GradedPerturbation
  Verification.PathStratumGrading Verification.PathWeightFiltration Verification.PathFullComplex
  Verification.PathEndpointCoordinates Verification.PathNormalizedBasis Verification.PathEndpointWords

variable {R : Type} [CommRing R]

noncomputable def zWeighted (g : R) (hg : g*g=1) (n : ℕ) :
    Verification.WeightedPureContraction.Data (fun x => -degree x) weight (zMatrix g 0 n).transpose :=
  Verification.WeightedPureContraction.ofPure _ _ _ (Verification.PathPureInduction.zData g hg n)
    (fun i j hij => Verification.PathPureMatrixWeight.z_matrix_exact_weight g n j i hij.symm)

noncomputable def yWeighted (g : R) (hg : g*g=1) (m : ℕ) :
    Verification.WeightedPureContraction.Data (fun x => -degree x) weight (yMatrix g 0 m).transpose :=
  Verification.WeightedPureContraction.ofPure _ _ _ (Verification.PathPureInduction.yData g hg m)
    (fun i j hij => Verification.PathPureMatrixWeight.y_matrix_exact_weight g m j i hij.symm)

noncomputable def zHomologyIso (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0) (n : ℕ) (p : ℤ) :
    (zChainComplex g ρ n hg hr).homology p ≅ (zChainComplex g 0 n hg (by simp)).homology p :=
  Verification.FilteredZeroReduction.homologyIso _ _ _ _ (zWeighted g hg n)
    (transpose_degree _ _ (zMatrix_degree g ρ n)) (transpose_square _ (zMatrix_squared g ρ n hg hr))
    (n+1) (Verification.PathWeightBounds.z_weight_bound n)
    (fun i j hij => by simpa only [Matrix.transpose_sub] using
      Verification.PathMatrixPerturbation.z_chain_difference_strict g ρ n i j hij) p

noncomputable def yHomologyIso (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0) (m : ℕ) (p : ℤ) :
    (yChainComplex g ρ m hg hr).homology p ≅ (yChainComplex g 0 m hg (by simp)).homology p :=
  Verification.FilteredZeroReduction.homologyIso _ _ _ _ (yWeighted g hg m)
    (transpose_degree _ _ (yMatrix_degree g ρ m)) (transpose_square _ (yMatrix_squared g ρ m hg hr))
    (2*m) (Verification.PathWeightBounds.y_weight_bound m)
    (fun i j hij => by simpa only [Matrix.transpose_sub] using
      Verification.PathMatrixPerturbation.y_chain_difference_strict g ρ m i j hij) p

theorem z_vanishing (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0) (n : ℕ) (p : ℤ) (hp : p ≠ 0) :
    Limits.IsZero ((zChainComplex g ρ n hg hr).homology p) :=
  (zHomologyIso g ρ hg hr n p).isZero_iff.mpr (Verification.PathPureInduction.z_vanishing g hg n p hp)

theorem y_vanishing (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0) (m : ℕ) (p : ℤ) (hp : p ≠ 0) :
    Limits.IsZero ((yChainComplex g ρ m hg hr).homology p) :=
  (yHomologyIso g ρ hg hr m p).isZero_iff.mpr (Verification.PathPureInduction.y_vanishing g hg m p hp)

noncomputable def zBasis (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0) (n : ℕ) :
    Basis (Fin (n+2)) R ((zChainComplex g ρ n hg hr).homology 0) :=
  (Verification.PathFirstHomology.zHomologyBasis g hg n).map (zHomologyIso g ρ hg hr n 0).symm.toLinearEquiv

noncomputable def yBasis (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0) (m : ℕ) :
    Basis (Fin (m+1)) R ((yChainComplex g ρ m hg hr).homology 0) :=
  (Verification.PathFirstHomology.yHomologyBasis g hg m).map (yHomologyIso g ρ hg hr m 0).symm.toLinearEquiv

theorem z_finrank [Nontrivial R] (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0) (n : ℕ) :
    Module.finrank R ((zChainComplex g ρ n hg hr).homology 0)=n+2 := by
  simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis (zBasis g ρ hg hr n)

theorem y_finrank [Nontrivial R] (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0) (m : ℕ) :
    Module.finrank R ((yChainComplex g ρ m hg hr).homology 0)=m+1 := by
  simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis (yBasis g ρ hg hr m)

#print axioms zWeighted
#print axioms yWeighted
#print axioms zHomologyIso
#print axioms yHomologyIso
#print axioms z_vanishing
#print axioms y_vanishing
#print axioms zBasis
#print axioms yBasis
#print axioms z_finrank
#print axioms y_finrank

end Verification.PathFullHomology
