/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LocalizedLineContraction
import Verification.LocalizedSlicePurity
import Verification.ActualTorusReducedRestriction

/-!
# Localized Torus Contraction

The actual adjacent torus boundary after ambient localization is the
u=1 contraction followed by the actual character-fiber restriction.
The equality follows from raw cone naturality and actual affine coordinates;
only smooth affine projections are assumed inverted by the theory.
-/
noncomputable section
namespace Verification.LocalizedTorusContraction
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite CochainComplex
open Verification.ActualOpenChart Verification.ActualOpenGeometry Verification.ExchangeTransverseSlice
open Verification.ActualTorusReducedRestriction
universe u w
variable (R ι κ τ : Type u) [CommRing R] [Fintype ι] [Fintype κ]
variable (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
variable (hB : ∀ l i : ι, B (Sum.inl l) (Sum.inl i) = 0) (v : ι)
variable (hf : Function.Injective (columnMap ι κ τ B))
variable (hs : FreezingLattice.Saturated (LinearMap.range (columnMap ι κ τ B)))
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
variable [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]
variable (L : DerivedCategory C ⥤ D) [L.CommShift ℤ] [L.IsTriangulated]
variable (F : (Under (CommRingCat.of R))ᵒᵖ ⥤ CochainComplex C ℤ)
variable (T : (Under (CommRingCat.of R))ᵒᵖ ⥤ D)
variable (P : LocalizedPrincipalPurity.Standard L R F T)
local notation "S" => ActualAdjacentTorusBoundary.shiftedTheory R F ⋙ L
variable [IsIso (PolynomialSectionIso.projectionMap R (Fiber (characters R ι κ τ B)) ι T)]
variable [IsIso (PolynomialSectionIso.projectionMap R (ActualTorusFace.OldTorus R ι κ τ B v)
  (LocalTransverseOpen.Old v) (ActualAdjacentTorusBoundary.shiftedTheory R F ⋙ L))]

def torusBoundary : T.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (Fiber (characters R ι κ τ B)))) ⟶
    (S).obj (op (CommRingCat.mkUnder (CommRingCat.of R) (ActualTorusFace.OldTorus R ι κ τ B v))) :=
  (LocalizedSlicePurity.closedIso R ι κ τ j B hB v T).hom ≫
    LocalizedSlicePurity.ambientBoundary R ι κ τ j B hB v hf hs L F T P ≫
      (ActualTorusFace.oldIso R ι κ τ j B hB v S).inv

omit [Preadditive D] [HasShift D ℤ] [HasZeroObject D] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive]
  [Pretriangulated D] [L.CommShift ℤ] [L.IsTriangulated] in
theorem actual_torus_boundary : torusBoundary R ι κ τ j B hB v hf hs L F T P =
    LocalizedSlicePurity.sliceBoundary R ι κ τ j B hB v hf hs L F T P ≫
      (S).map (ActualTorusFace.torusFace R ι κ τ B v).toUnder.op := by
  unfold torusBoundary
  rw [LocalizedSlicePurity.closedIso_hom, ← Category.assoc,
    LocalizedSlicePurity.boundary_naturality, Category.assoc]
  congr 1
  exact ActualTorusFace.actual_open_map R ι κ τ j B hB v S

variable [IsIso (L.map (DerivedCategory.Q.map (ActualTransverseBasepoint.lineProjection R ι κ τ B F)))]

def thomContractionIso : T.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (Fiber (characters R ι κ τ B)))) ≅
    L.obj (DerivedCategory.Q.obj ((kernel (ActualTransverseBasepoint.projection R ι κ τ B F))⟦(1 : ℤ)⟧)) :=
  LocalizedSlicePurity.sliceIso R ι κ τ j B hB v hf hs L F T P ≪≫
    LocalizedLineContraction.contractionIso R ι κ τ B L F

theorem boundary_as_contraction : torusBoundary R ι κ τ j B hB v hf hs L F T P =
    (thomContractionIso R ι κ τ j B hB v hf hs L F T P).hom ≫
      L.map (DerivedCategory.Q.map ((reducedRestriction R ι κ τ B v F)⟦(1 : ℤ)⟧')) ≫
        L.map (DerivedCategory.Q.map ((kernel.ι (LaurentBasepoint.projection R
          (OldBase R ι κ τ B v) F))⟦(1 : ℤ)⟧')) := by
  rw [actual_torus_boundary]
  simp only [LocalizedSlicePurity.sliceBoundary,thomContractionIso,Iso.trans_hom,Category.assoc]
  rw [← LocalizedLineContraction.contractionIso_boundary R ι κ τ B L F]
  simp only [Category.assoc]
  have h := congrArg (fun f => L.map f) (shifted_restriction_inclusion R ι κ τ B v F)
  simpa only [Functor.map_comp] using congrArg (fun f =>
    (LocalizedSlicePurity.sliceIso R ι κ τ j B hB v hf hs L F T P).hom ≫
      (LocalizedLineContraction.contractionIso R ι κ τ B L F).hom ≫ f) h

variable (M : D)

def oldContraction (a : (S).obj (op (CommRingCat.mkUnder (CommRingCat.of R)
    (ActualTorusFace.OldTorus R ι κ τ B v))) ⟶ M) :=
  L.map (DerivedCategory.Q.map ((kernel.ι (LaurentBasepoint.projection R
    (OldBase R ι κ τ B v) F))⟦(1 : ℤ)⟧')) ≫ a

theorem boundary_on_sections (a : (S).obj (op (CommRingCat.mkUnder (CommRingCat.of R)
    (ActualTorusFace.OldTorus R ι κ τ B v))) ⟶ M) :
    torusBoundary R ι κ τ j B hB v hf hs L F T P ≫ a =
      (thomContractionIso R ι κ τ j B hB v hf hs L F T P).hom ≫
        L.map (DerivedCategory.Q.map ((reducedRestriction R ι κ τ B v F)⟦(1 : ℤ)⟧')) ≫
          oldContraction R ι κ τ B v L F M a := by
  rw [boundary_as_contraction]
  simp only [oldContraction,Category.assoc]

#print axioms torusBoundary
#print axioms actual_torus_boundary
#print axioms thomContractionIso
#print axioms boundary_as_contraction
#print axioms oldContraction
#print axioms boundary_on_sections
end Verification.LocalizedTorusContraction
