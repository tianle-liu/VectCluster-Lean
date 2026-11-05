/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualTransversePurity
import Verification.ActualTransverseZeroSection
import Verification.AffineSectionTransport

/-!
# Actual Closed Thom Iso

The closed map in the manuscript's actual transverse slice is inverted
using the proved affine-partner coordinates and standard polynomial A1
invariance. This discharges the closed-map-isomorphism condition in the
derived adjacent-boundary calculation.
-/
namespace Verification.ActualClosedThomIso
open CategoryTheory CategoryTheory.Limits Opposite CochainComplex
open Verification.ActualTransverseSlice Verification.ActualTransverseLocalization
open Verification.ExchangeTransverseSlice Verification.ActualOpenChart
open Verification.ActualTransverseCone Verification.ActualTransversePurity
universe u w
variable (R ι κ τ : Type u) [CommRing R] [Fintype ι] [Fintype κ]
variable (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
variable (hB : ∀ l i : ι, B (Sum.inl l) (Sum.inl i) = 0) (v : ι)
variable {D : Type*} [Category D] [Abelian D] [HasBinaryBiproducts D] [HasDerivedCategory.{w} D]
variable (F : (Under (CommRingCat.of R))ᵒᵖ ⥤ CochainComplex D ℤ)
variable (T : (Under (CommRingCat.of R))ᵒᵖ ⥤ DerivedCategory D)
variable [IsIso (PolynomialSectionIso.projectionMap R (Fiber (characters R ι κ τ B)) ι T)]

noncomputable def closedIso :
    T.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (Fiber (characters R ι κ τ B)))) ≅
      T.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (ClosedSource R ι κ τ j B v))) :=
  AffineSectionTransport.sectionIso R (Fiber (characters R ι κ τ B)) ι
    (ClosedSource R ι κ τ j B v) (ActualTransverseClosed.affineEquiv R ι κ τ j B v hB) T

omit [HasBinaryBiproducts D] in
theorem closedIso_hom : (closedIso R ι κ τ j B hB v T).hom =
    closedThomMap R ι κ τ j B hB v T := by
  rw [closedIso, AffineSectionTransport.sectionIso_hom]
  unfold closedThomMap
  rw [ActualTransverseZeroSection.closedSlice_zeroSection]
  rfl

omit [HasBinaryBiproducts D] in
theorem closedThomMap_isIso : IsIso (closedThomMap R ι κ τ j B hB v T) := by
  rw [← closedIso_hom R ι κ τ j B hB v T]
  infer_instance

/-- The actual adjacent boundary, with its closed-map inverse constructed
from the affine coordinates. Only standard A1 invariance and the standard
natural purity comparison remain as external theory inputs. -/
theorem actual_adjacent_from_slice (P : PurityComparison R ι κ τ j B hB v F T) :
    adjacentBoundary R ι κ τ j B hB v F T P =
      (closedIso R ι κ τ j B hB v T).inv ≫
        sliceBoundary R ι κ τ j B hB v F T P ≫
          DerivedCategory.Q.map ((openMap R ι κ τ j B hB v F)⟦(1 : ℤ)⟧') := by
  have hn := adjacent_naturality R ι κ τ j B hB v F T P
  rw [← hn, ← Category.assoc, ← closedIso_hom, Iso.inv_hom_id, Category.id_comp]

#print axioms closedIso
#print axioms closedIso_hom
#print axioms closedThomMap_isIso
#print axioms actual_adjacent_from_slice
end Verification.ActualClosedThomIso
