/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CoordinateClosedImmersion

/-!
# Coordinate Empty Layer

The empty-coordinate stratum is exactly the first nonempty open
filtration stage, as an actual scheme, including its reduced structure.
-/
noncomputable section
namespace Verification.CoordinateEmptyLayer
open CategoryTheory AlgebraicGeometry Verification.PrimeCoordinateFiltration
variable (A V : Type) [CommRing A] [Fintype V] [DecidableEq V] (x : V→A)

theorem ideal_empty : PrimeStratumPresentation.zeroIdeal x ∅=⊥ := by
  rw [PrimeStratumPresentation.zeroIdeal,Ideal.span_eq_bot]
  rintro a ⟨i,rfl⟩
  exact False.elim (Finset.not_mem_empty _ i.property)

def quotientEquiv : PrimeStratumPresentation.ClosedRing x ∅ ≃+*
    PrimeStratumPresentation.OpenRing x ∅ :=
  (Ideal.quotientEquivAlgOfEq (PrimeStratumPresentation.OpenRing x ∅)
    (ideal_empty A V x)).toRingEquiv.trans (RingEquiv.quotientBot _)

theorem stage_one : PrimeSchemeFiltration.stageOpen A x 1=PrimeLocalPair.chartOpen A V x ∅ := by
  ext p
  change p∈stage x 1 ↔ p∈openBy x ∅
  rw [mem_stage,mem_openBy]
  rw [Finset.subset_empty]
  exact ⟨fun h => Finset.card_eq_zero.mp (by omega),fun h => by rw [h];simp⟩

def stratumIso : CoordinateClosedImmersion.source A V x ∅ ≅
    (PrimeSchemeFiltration.stageOpen A x 1).toScheme :=
  Scheme.Spec.mapIso (quotientEquiv A V x).toCommRingCatIso.symm.op ≪≫
    PrimeLocalPair.ambientIso A V x ∅ ≪≫ (Spec (CommRingCat.of A)).isoOfEq (stage_one A V x).symm

#print axioms ideal_empty
#print axioms quotientEquiv
#print axioms stage_one
#print axioms stratumIso
end Verification.CoordinateEmptyLayer
