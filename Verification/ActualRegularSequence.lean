/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualOpenRegular
import Verification.PowerNontrivial

/-!
# Actual Regular Sequence

Under the actual selected-column rank hypothesis, the original
coordinates are a regular sequence in their actual open chart over every
nonzero coefficient ring. Nonemptiness is derived from the Smith power
presentation, rather than assumed as a separate zero-layer hypothesis.
-/
noncomputable section
universe u
namespace Verification.ActualRegularSequence
open Verification.ActualOpenChart Verification.ActualOpenGeometry
open RingTheory.Sequence
variable (R ι κ τ : Type u) [CommRing R] [Nontrivial R] [Fintype ι] [Fintype κ]
variable (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)

theorem original_coordinates_regular
    (hB : ∀ a i : ι, B (Sum.inl a) (Sum.inl i) = 0)
    (hf : Function.Injective (columnMap ι κ τ B))
    (l : List ι) (hl : l.Nodup) :
    IsRegular (GlobalOpen R ι κ τ j B) (l.map (globalCoordinate R ι κ τ j B)) := by
  obtain ⟨n,s⟩ := (LinearMap.range (columnMap ι κ τ B)).smithNormalForm Finsupp.basisSingleOne
  letI := PowerNontrivial.zero_stratum_nontrivial (R := R) j B hB (columnMap ι κ τ B)
    Finsupp.basisSingleOne (fun i => columnMap_single ι κ τ B i) hf s
  exact ActualOpenRegular.original_coordinates_regular_of_stratum R ι κ τ j B hB hf l hl

#print axioms original_coordinates_regular
end Verification.ActualRegularSequence
