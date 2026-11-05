/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LocalizedPrincipalPurity
import Verification.ActualPrincipalPurity
import Verification.ActualClosedThomIso

/-!
# Localized Slice Purity

Apply localized principal purity to the literal transverse slice. The
four smoothness and regular-parameter conditions are proved from AS. The
closed-map inverse uses only the actual affine projection after localization.
-/
noncomputable section
namespace Verification.LocalizedSlicePurity
open CategoryTheory CategoryTheory.Limits Opposite CochainComplex
open Verification.ActualOpenChart Verification.ActualOpenGeometry
open Verification.ActualTransverseSlice Verification.ActualTransverseLocalization
open Verification.ExchangeTransverseSlice Verification.TransverseClosedFiber
universe u w
variable (R ι κ τ : Type u) [CommRing R] [Fintype ι] [Fintype κ]
variable (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
variable (hB : ∀ l i : ι, B (Sum.inl l) (Sum.inl i) = 0) (v : ι)
variable (hf : Function.Injective (columnMap ι κ τ B))
variable (hs : FreezingLattice.Saturated (LinearMap.range (columnMap ι κ τ B)))
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable {D : Type*} [Category D]
variable (L : DerivedCategory C ⥤ D)
variable (F : (Under (CommRingCat.of R))ᵒᵖ ⥤ CochainComplex C ℤ)
variable (T : (Under (CommRingCat.of R))ᵒᵖ ⥤ D)
variable (P : LocalizedPrincipalPurity.Standard L R F T)

def ambientIso : T.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (ClosedSource R ι κ τ j B v))) ≅
    L.obj (DerivedCategory.Q.obj (mappingCone (ActualTransverseCone.ambientOpen R ι κ τ j B v F))) :=
  P.comparison (Intermediate R ι κ τ j B v) (originalParameter R ι κ τ j B v)
    (ActualTransverseSmooth.intermediate_smooth_AS R ι κ τ j B v hB hf hs)
    (ActualTransversePairSmooth.pair_smooth_AS R ι κ τ j B hB hf hs v).2.2
    (ActualTransverseRegular.parameter_regular R ι κ τ j B hB hf v)

def sliceIso : T.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (Fiber (characters R ι κ τ B)))) ≅
    L.obj (DerivedCategory.Q.obj (mappingCone (ActualTransverseCone.sliceOpen R ι κ τ B F))) := by
  have hh := ActualTransversePairSmooth.pair_smooth_AS R ι κ τ j B hB hf hs v
  letI : Algebra.Smooth R (Fiber (characters R ι κ τ B)) := hh.1
  exact T.mapIso (fiberEquiv R ι κ τ B).toUnder.op ≪≫
    P.comparison (Slice (characters R ι κ τ B)) Polynomial.X hh.2.1
      (Algebra.Smooth.of_equiv (fiberEquiv R ι κ τ B).symm) Polynomial.isRegular_X.left

def closedMap := T.map (closedSlice R ι κ τ j B hB v).toUnder.op

theorem comparison_square : closedMap R ι κ τ j B hB v T ≫
    (ambientIso R ι κ τ j B hB v hf hs L F T P).hom =
      (sliceIso R ι κ τ j B hB v hf hs L F T P).hom ≫
        L.map (ActualTransversePurity.derivedConeMap R ι κ τ j B hB v F) := by
  have hh := ActualTransversePairSmooth.pair_smooth_AS R ι κ τ j B hB hf hs v
  letI : Algebra.Smooth R (Fiber (characters R ι κ τ B)) := hh.1
  have hn := P.naturality (Intermediate R ι κ τ j B v) (Slice (characters R ι κ τ B))
    (originalParameter R ι κ τ j B v) Polynomial.X
    (transverseSlice R ι κ τ j B hB v) (transverse_parameter R ι κ τ j B hB v)
    (ActualTransverseSmooth.intermediate_smooth_AS R ι κ τ j B v hB hf hs) hh.2.2 hh.2.1
    (Algebra.Smooth.of_equiv (fiberEquiv R ι κ τ B).symm)
    (ActualTransverseRegular.parameter_regular R ι κ τ j B hB hf v) Polynomial.isRegular_X.left
  rw [ActualPrincipalPurity.principalCone_eq] at hn
  simp only [sliceIso,Iso.trans_hom,Functor.mapIso_hom,Category.assoc,← hn]
  rw [← Category.assoc, ← Functor.map_comp]
  change _ = T.map ((fiberEquiv R ι κ τ B).toAlgHom.comp
    (principalClosedMap R ι κ τ j B hB v)).toUnder.op ≫ _
  rw [closedMap_fiber]
  rfl

def ambientBoundary := (ambientIso R ι κ τ j B hB v hf hs L F T P).hom ≫
  L.map (TransverseDerivedBoundary.boundary (ActualTransverseCone.ambientOpen R ι κ τ j B v F))

def sliceBoundary := (sliceIso R ι κ τ j B hB v hf hs L F T P).hom ≫
  L.map (TransverseDerivedBoundary.boundary (ActualTransverseCone.sliceOpen R ι κ τ B F))

theorem boundary_naturality : closedMap R ι κ τ j B hB v T ≫
    ambientBoundary R ι κ τ j B hB v hf hs L F T P =
      sliceBoundary R ι κ τ j B hB v hf hs L F T P ≫
        L.map (DerivedCategory.Q.map ((ActualTransverseCone.openMap R ι κ τ j B hB v F)⟦(1 : ℤ)⟧')) := by
  dsimp only [ambientBoundary,sliceBoundary]
  rw [← Category.assoc,comparison_square,Category.assoc,← Functor.map_comp]
  rw [Category.assoc,← Functor.map_comp]
  have hn := TransverseDerivedBoundary.boundary_naturality
    (ActualTransverseCone.sliceOpen R ι κ τ B F) (ActualTransverseCone.ambientOpen R ι κ τ j B v F)
    (ActualTransverseCone.openMap R ι κ τ j B hB v F) (ActualTransverseCone.ambientMap R ι κ τ j B hB v F)
    (ActualTransverseCone.chain_square R ι κ τ j B hB v F)
  exact congrArg (fun f => (sliceIso R ι κ τ j B hB v hf hs L F T P).hom ≫ L.map f) hn

variable [IsIso (PolynomialSectionIso.projectionMap R (Fiber (characters R ι κ τ B)) ι T)]

def closedIso : T.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (Fiber (characters R ι κ τ B)))) ≅
    T.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (ClosedSource R ι κ τ j B v))) :=
  AffineSectionTransport.sectionIso R (Fiber (characters R ι κ τ B)) ι
    (ClosedSource R ι κ τ j B v) (ActualTransverseClosed.affineEquiv R ι κ τ j B v hB) T

omit [HasBinaryBiproducts C] [HasDerivedCategory C] in
theorem closedIso_hom : (closedIso R ι κ τ j B hB v T).hom = closedMap R ι κ τ j B hB v T := by
  rw [closedIso,AffineSectionTransport.sectionIso_hom]
  unfold closedMap
  rw [ActualTransverseZeroSection.closedSlice_zeroSection]
  rfl

theorem ambient_from_slice : ambientBoundary R ι κ τ j B hB v hf hs L F T P =
    (closedIso R ι κ τ j B hB v T).inv ≫ sliceBoundary R ι κ τ j B hB v hf hs L F T P ≫
      L.map (DerivedCategory.Q.map ((ActualTransverseCone.openMap R ι κ τ j B hB v F)⟦(1 : ℤ)⟧')) := by
  rw [← boundary_naturality, ← closedIso_hom, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

#print axioms ambientIso
#print axioms sliceIso
#print axioms closedMap
#print axioms comparison_square
#print axioms ambientBoundary
#print axioms sliceBoundary
#print axioms boundary_naturality
#print axioms closedIso
#print axioms closedIso_hom
#print axioms ambient_from_slice
end Verification.LocalizedSlicePurity
