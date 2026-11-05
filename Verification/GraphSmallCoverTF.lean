/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphLowHomology
import Verification.FiniteHomologyFacts
import Verification.GraphCoverCancellation

/-!
# Graph Small Cover TF

The low-cover freeness conclusion: when a cover has independence number at
most two, its actual finite cancellation leaves no incoming differential above
chain dimension one. The two remaining low homology groups are handled by the
explicit edge and augmentation saturation proofs.
-/

namespace Verification.GraphSmallCoverTF

open Classical
open Verification.GraphCover Verification.GraphCoverOrder Verification.GraphCoverGrading
  Verification.GraphCoverMatrices Verification.GraphCoverCancellation Verification.GraphChainMatrix
  Verification.GraphLowHomology Verification.FiniteHomologyFacts
  Verification.GradedPerturbation Verification.PerturbedHomologyModel

variable {R V : Type} [CommRing R] [IsDomain R] [Fintype V] [LinearOrder V]
  (G : SimpleGraph V) (C T : Finset V) (hC : Covers G C) (hord : CoverOrdered C)

omit [IsDomain R] in
/-- The graph-cover source and the original graph chain complex have the same actual matrix. -/
theorem chainComplex_eq_coverSource :
    chainComplex (R := R) G T=graphComplex (R := R) G C T hC hord := by
  unfold chainComplex graphComplex sourceComplex
  simp only [chainMatrix,boundaryMatrix_split G C T]

include hC hord in
set_option maxHeartbeats 800000 in
/-- All other degrees inherit TF from the finite survivor complex. -/
theorem outside_low_homology_tf (ha : coverRank G C ≤ 2) (p : ℤ)
    (hp : p ≤ -2 ∨ 0 < p) :
    NoZeroSMulDivisors R ((chainComplex (R := R) G T).homology p) := by
  have hs : NoZeroSMulDivisors R ((survivorComplex (R := R) G C T hC hord).homology p) := by
    rcases hp with hp | hp
    · letI : Subsingleton ((survivorComplex (R := R) G C T hC hord).X (p-1)) :=
        survivorComplex_supported G C T hC hord (p-1) (Or.inl (by omega))
      letI : NoZeroSMulDivisors R ((survivorComplex (R := R) G C T hC hord).X p) :=
        inferInstanceAs (NoZeroSMulDivisors R
          (fixedModule (degree G T) (projectionMatrix (R := R) G C T hC) p))
      exact homology_tf_of_no_incoming _ p
    · letI := survivorComplex_supported (R := R) G C T hC hord p (Or.inr hp)
      exact homology_tf_of_zero_at _ p
  letI := hs
  let e := ((coverHomotopyEquiv (R := R) G C T hC hord).toHomologyIso p).toLinearEquiv
  have ht : NoZeroSMulDivisors R ((graphComplex (R := R) G C T hC hord).homology p) :=
    Function.Injective.noZeroSMulDivisors e e.injective e.map_zero e.map_smul
  rw [chainComplex_eq_coverSource (R := R) G C T hC hord]
  exact ht

include hC hord in
/-- Actual integral graph homology is TF in every degree for such a cover.
The order hypothesis is explicit and will be removed by a separate signed-order chain isomorphism. -/
theorem ordered_cover_homology_tf (ha : coverRank G C ≤ 2) (p : ℤ) :
    NoZeroSMulDivisors R ((chainComplex (R := R) G T).homology p) := by
  by_cases hp : p=0
  · subst p
    simpa only [Nat.cast_zero,neg_zero] using low_homology_tf (R := R) G T 0 (by omega)
  by_cases hm : p= -1
  · subst p
    simpa only [Nat.cast_one] using low_homology_tf (R := R) G T 1 (by omega)
  exact outside_low_homology_tf G C T hC hord ha p (by omega)

include hC hord in
/-- Finite TF homology over a PID is actually free, as stated by the manuscript. -/
theorem ordered_cover_homology_free [IsPrincipalIdealRing R] (ha : coverRank G C ≤ 2) (p : ℤ) :
    Module.Free R ((chainComplex (R := R) G T).homology p) := by
  letI := ordered_cover_homology_tf (R := R) G C T hC hord ha p
  letI : Module.Finite R ((chainComplex (R := R) G T).homology p) :=
    matrix_homology_finite (degree G T) (chainMatrix (R := R) G T)
      (chainMatrix_degree G T) (chainMatrix_square G T) p
  infer_instance

#print axioms chainComplex_eq_coverSource
#print axioms outside_low_homology_tf
#print axioms ordered_cover_homology_tf
#print axioms ordered_cover_homology_free

end Verification.GraphSmallCoverTF
