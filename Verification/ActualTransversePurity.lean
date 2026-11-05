/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualTransverseCone
import Verification.TransverseDerivedBoundary
import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Actual Transverse Purity

The original cluster slice inserted into the actual derived localization
triangle. The external standard purity theorem is represented by an isomorphism
of the actual Thom/cone arrows. It supplies no boundary formula: naturality of
the adjacent boundary is derived from the already constructed cone map. The
isomorphism condition on the closed comparison is discharged separately by the
actual affine zero-section calculation and A1-invariance of the chosen theory.
-/
namespace Verification.ActualTransversePurity
open CategoryTheory CategoryTheory.Limits Opposite CochainComplex
open Verification.ActualTransverseSlice Verification.ActualTransverseLocalization
open Verification.ExchangeTransverseSlice Verification.ActualOpenChart
open Verification.ActualTransverseCone
universe u w
variable (R ι κ τ : Type u) [CommRing R] [Fintype ι] [Fintype κ]
variable (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
variable (hB : ∀ l i : ι, B (Sum.inl l) (Sum.inl i) = 0) (v : ι)
variable {D : Type*} [Category D] [Abelian D] [HasBinaryBiproducts D] [HasDerivedCategory.{w} D]
variable (F : (Under (CommRingCat.of R))ᵒᵖ ⥤ CochainComplex D ℤ)
variable (T : (Under (CommRingCat.of R))ᵒᵖ ⥤ DerivedCategory D)

noncomputable def closedThomMap :
    T.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (Fiber (characters R ι κ τ B)))) ⟶
      T.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (ClosedSource R ι κ τ j B v))) :=
  T.map (closedSlice R ι κ τ j B hB v).toUnder.op

noncomputable def derivedConeMap :
    DerivedCategory.Q.obj (mappingCone (sliceOpen R ι κ τ B F)) ⟶
      DerivedCategory.Q.obj (mappingCone (ambientOpen R ι κ τ j B v F)) :=
  DerivedCategory.Q.map (sliceConeMap R ι κ τ j B hB v F)

/-- A precise external standard-purity interface, on actual derived diagrams.
It concerns Thom/cofiber identification, not the manuscript's boundary equation. -/
abbrev PurityComparison :=
  Arrow.mk (closedThomMap R ι κ τ j B hB v T) ≅
    Arrow.mk (derivedConeMap R ι κ τ j B hB v F)

variable (P : PurityComparison R ι κ τ j B hB v F T)

noncomputable def sliceBoundary :
    T.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (Fiber (characters R ι κ τ B)))) ⟶
      DerivedCategory.Q.obj ((F.obj (op (CommRingCat.mkUnder (CommRingCat.of R)
        (OpenTarget R ι κ τ B))))⟦(1 : ℤ)⟧) :=
  P.hom.left ≫ DerivedCategory.Q.map
    (Verification.TransverseConeBoundary.boundary (sliceOpen R ι κ τ B F))

noncomputable def adjacentBoundary :
    T.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (ClosedSource R ι κ τ j B v))) ⟶
      DerivedCategory.Q.obj ((F.obj (op (CommRingCat.mkUnder (CommRingCat.of R)
        (OpenSource R ι κ τ j B v))))⟦(1 : ℤ)⟧) :=
  P.hom.right ≫ DerivedCategory.Q.map
    (Verification.TransverseConeBoundary.boundary (ambientOpen R ι κ τ j B v F))

/-- The actual adjacent boundary square follows from standard purity and the
proved naturality of the actual cluster localization cone. -/
theorem adjacent_naturality :
    closedThomMap R ι κ τ j B hB v T ≫ adjacentBoundary R ι κ τ j B hB v F T P =
      sliceBoundary R ι κ τ j B hB v F T P ≫
        DerivedCategory.Q.map ((openMap R ι κ τ j B hB v F)⟦(1 : ℤ)⟧') := by
  have hp := P.hom.w
  change P.hom.left ≫ derivedConeMap R ι κ τ j B hB v F =
    closedThomMap R ι κ τ j B hB v T ≫ P.hom.right at hp
  simp only [adjacentBoundary, sliceBoundary, ← Category.assoc, ← hp]
  simp only [Category.assoc, derivedConeMap, ← Functor.map_comp, actual_boundary_naturality]

/-- After proving the closed map is an A1-equivalence, the boundary is computed
on the transverse slice followed by the literal Laurent restriction map. -/
theorem adjacent_from_slice [IsIso (closedThomMap R ι κ τ j B hB v T)] :
    adjacentBoundary R ι κ τ j B hB v F T P =
      inv (closedThomMap R ι κ τ j B hB v T) ≫
        sliceBoundary R ι κ τ j B hB v F T P ≫
          DerivedCategory.Q.map ((openMap R ι κ τ j B hB v F)⟦(1 : ℤ)⟧') := by
  have hn := adjacent_naturality R ι κ τ j B hB v F T P
  rw [← hn, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

#print axioms closedThomMap
#print axioms derivedConeMap
#print axioms PurityComparison
#print axioms sliceBoundary
#print axioms adjacentBoundary
#print axioms adjacent_naturality
#print axioms adjacent_from_slice
end Verification.ActualTransversePurity
