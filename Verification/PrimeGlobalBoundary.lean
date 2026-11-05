/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimeAdjacentProjection

/-!
# Prime Global Boundary

Blocks of the actual filtration boundary, in the canonical excision
coordinates. These are derived maps of the genuine cone differential,
without any supplied cellular matrix or purity formula.
-/
noncomputable section
namespace Verification.PrimeGlobalBoundary
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.PrimeCoordinateFiltration Verification.PrimeLayerCover
open Verification.PrimeAdjacentExcision Verification.PrimeAdjacentAssembly
universe w
variable (A V : Type) [CommRing A] [Fintype V] [DecidableEq V]
variable (x : V → A) (Allowed : Finset V → Prop)
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)
variable (hall : ∀ p : PrimeSpectrum A, Allowed (zeroSet x p))
variable (r : ℕ) (J : Index Allowed (r+1))
local notation "F" => PrimeLayerExcision.openChains A G

def globalBoundary :=
  DerivedCategory.Q.map (FilteredConeComplex.boundary (PrimeSchemeFiltration.filteredChains A x G) r) ≫
    (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
      (FilteredConeComplex.relative (PrimeSchemeFiltration.filteredChains A x G) r)

def inclusion :=
  OpenConeExcision.localMap (Spec (CommRingCat.of A)) F (stage x (r+1)) (stage x (r+1+1))
    (stage_mono x (Nat.le_succ (r+1))) (chart x Allowed (r+1))
      (chart_le_stage x Allowed (r+1)) J

theorem inclusion_eq : inclusion A V x Allowed G r J =
    biproduct.ι (PrimeLayerExcision.localRelative A V x Allowed G (r+1)) J ≫
      (PrimeLayerExcision.relativeIso A V x Allowed G E hall (r+1)).hom := by
  exact (OpenConeExcision.assembly_inclusion _ _ _ _ _ _ _ J).symm

def localBoundary : PrimeLayerExcision.localRelative A V x Allowed G (r+1) J ⟶
    (DerivedCategory.Q.obj (mappingCone (rowArrow A V x J.val r G)))⟦(1 : ℤ)⟧ :=
  DerivedCategory.Q.map (NestedConeBoundary.boundary
    (OpenFlagBoundary.localFirst (Spec (CommRingCat.of A)) F (stage x r) (stage x (r+1))
      (stage_mono x (Nat.le_succ r)) (openBy x J.val))
    (OpenFlagBoundary.localSecond (Spec (CommRingCat.of A)) F (stage x (r+1)) (openBy x J.val))) ≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (mappingCone (rowArrow A V x J.val r G))

theorem local_boundary_square :
    inclusion A V x Allowed G r J ≫ globalBoundary A V x G r =
      localBoundary A V x Allowed G r J ≫ (rowMap A V x J.val r G)⟦(1 : ℤ)⟧' := by
  have h := OpenFlagBoundary.derived_boundary_naturality (Spec (CommRingCat.of A)) F
    (stage x r) (stage x (r+1)) (stage x (r+1+1))
    (stage_mono x (Nat.le_succ r)) (stage_mono x (Nat.le_succ (r+1)))
    (openBy x J.val) (chart_le_stage x Allowed (r+1) J)
  change inclusion A V x Allowed G r J ≫
    DerivedCategory.Q.map (FilteredConeComplex.boundary (PrimeSchemeFiltration.filteredChains A x G) r) = _ at h
  dsimp only [globalBoundary,localBoundary,rowMap]
  rw [← Category.assoc,h,Category.assoc]
  simp only [Category.assoc]
  congr 1
  exact (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.naturality
    (OpenFlagBoundary.rowMap (Spec (CommRingCat.of A)) F (stage x r) (stage x (r+1))
      (stage_mono x (Nat.le_succ r)) (openBy x J.val))

def block (i : Index Allowed r) :=
  inclusion A V x Allowed G r J ≫ globalBoundary A V x G r ≫
    ((PrimeLayerExcision.relativeIso A V x Allowed G E hall r).inv ≫
      biproduct.π (PrimeLayerExcision.localRelative A V x Allowed G r) i)⟦(1 : ℤ)⟧'

theorem block_local (i : Index Allowed r) : block A V x Allowed G E hall r J i =
    localBoundary A V x Allowed G r J ≫
      (PrimeAdjacentProjection.component A V x Allowed J.val r G E hall i)⟦(1 : ℤ)⟧' := by
  dsimp only [block, PrimeAdjacentProjection.component]
  rw [← Category.assoc, local_boundary_square, Category.assoc, ← CategoryTheory.Functor.map_comp]

variable (herase : ∀ v : J.val, Allowed (J.val.erase v.val))

include herase in
theorem block_zero (i : Index Allowed r) (hi : ¬ i.val ⊆ J.val) :
    block A V x Allowed G E hall r J i = 0 := by
  rw [block_local, PrimeAdjacentProjection.component_zero A V x Allowed J.val r
    J.property.1 herase G E hall i hi, Functor.map_zero, comp_zero]

theorem block_edge (v : J.val) :
    block A V x Allowed G E hall r J (edgeIndex V Allowed J.val r J.property.1 herase v) =
      localBoundary A V x Allowed G r J ≫
        ((PrimeAdjacentExcision.relativeIso A V x J.val r J.property.1 G E).inv ≫
          biproduct.π (edgeCone A V x J.val r G) v ≫
            (edgeIso A V x Allowed J.val r J.property.1 herase G v).hom)⟦(1 : ℤ)⟧' := by
  rw [block_local, PrimeAdjacentProjection.component_edge]

#print axioms globalBoundary
#print axioms inclusion
#print axioms inclusion_eq
#print axioms localBoundary
#print axioms local_boundary_square
#print axioms block
#print axioms block_local
#print axioms block_zero
#print axioms block_edge
end Verification.PrimeGlobalBoundary
