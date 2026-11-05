/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphOrderChange

/-!
# Graph Order Applications

The cover-order chain isomorphism transports the actual finite cancellation
and the 2p vertex bound to the original vertex order, with no ordering premise.
-/

namespace Verification.GraphOrderApplications

open Classical CategoryTheory CategoryTheory.Limits
open Verification.GraphCover Verification.GraphCoverOrder Verification.GraphCoverMatrices
open Verification.GraphCoverGrading Verification.GraphCoverCancellation
open Verification.GraphChainMatrix Verification.GraphOrderChange
open Verification.GraphBalancedCover Verification.GraphVertexBound

variable {R V : Type} [CommRing R] [Fintype V] [baseOrder : LinearOrder V]
variable (G : SimpleGraph V) (C T : Finset V) (hC : Covers G C)

/-- The graph-cover source is exactly the independently defined signed chain complex. -/
theorem cover_complex_eq (hord : CoverOrdered C) :
    graphComplex (R := R) G C T hC hord=chainComplex G T := by
  unfold graphComplex Verification.PerturbedHomologyModel.sourceComplex chainComplex
  congr 1
  exact (boundaryMatrix_split G C T).symm

/-- The actual cover-first complex selected from the original vertex order. -/
noncomputable def orderedCoverComplex : CochainComplex (ModuleCat R) ℤ := by
  let o : LinearOrder V := @coverOrder V baseOrder C
  have ho : @CoverOrdered V o C := @coverOrder_property V baseOrder C
  letI := o
  exact graphComplex G C T hC ho

/-- Actual chain isomorphism from the original order to the required cover-first order. -/
noncomputable def coverOrderIso : chainComplex (R := R) G T ≅ orderedCoverComplex G C T hC := by
  let o : LinearOrder V := @coverOrder V baseOrder C
  have ho : @CoverOrdered V o C := @coverOrder_property V baseOrder C
  exact (orderIso G T baseOrder o).trans (CategoryTheory.eqToIso
    (@cover_complex_eq R V _ _ o G C T hC ho).symm)

/-- All actual graph homology groups agree with those used by the cover cancellation. -/
noncomputable def coverHomologyIso (p : ℤ) :
    (chainComplex (R := R) G T).homology p ≅ (orderedCoverComplex G C T hC).homology p :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) p).mapIso (coverOrderIso G C T hC)

/-- The finite-vertex bound now holds for the literal graph chains in the original order. -/
theorem nonzero_homology_vertex_bound (p : ℕ)
    (hn : ¬IsZero ((chainComplex (R := R) G T).homology (-(p : ℤ)))) : 2*p ≤ T.card := by
  apply canonical_nonzero_homology_vertex_bound (R := R) G T p
  intro hz
  apply hn
  have e := coverHomologyIso (R := R) G (balancedCover G T) T (balancedCover_covers G T) (-(p : ℤ))
  exact e.isZero_iff.mpr hz

/-- Contrapositive vanishing in the original chain model. -/
theorem homology_zero_of_small_vertices (p : ℕ) (hp : T.card < 2*p) :
    IsZero ((chainComplex (R := R) G T).homology (-(p : ℤ))) := by
  by_contra hn
  exact (Nat.not_le_of_gt hp) (nonzero_homology_vertex_bound G T p hn)

#print axioms cover_complex_eq
#print axioms orderedCoverComplex
#print axioms coverOrderIso
#print axioms coverHomologyIso
#print axioms nonzero_homology_vertex_bound
#print axioms homology_zero_of_small_vertices

end Verification.GraphOrderApplications
