/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimeAdjacentAssembly

/-!
# Prime Adjacent Projection

Canonical projections of the actual global preceding layer. A
nonincident component vanishes, and an incident one is the same projection
in the finite excision of the J-chart, with its literal cone identification.
-/
noncomputable section
namespace Verification.PrimeAdjacentProjection
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.PrimeCoordinateFiltration Verification.PrimeLayerCover
open Verification.PrimeAdjacentExcision Verification.PrimeAdjacentAssembly
universe w
variable (A V : Type) [CommRing A] [Fintype V] [DecidableEq V]
variable (x : V → A) (Allowed : Finset V → Prop)
variable (J : Finset V) (r : ℕ) (hr : J.card = r+1)
variable (herase : ∀ v : J, Allowed (J.erase v.val))
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)
variable (hall : ∀ p : PrimeSpectrum A, Allowed (zeroSet x p))

def component (i : Index Allowed r) :=
  rowMap A V x J r G ≫ (PrimeLayerExcision.relativeIso A V x Allowed G E hall r).inv ≫
    biproduct.π (PrimeLayerExcision.localRelative A V x Allowed G r) i

include hr herase in
theorem component_zero (i : Index Allowed r) (hi : ¬ i.val ⊆ J) :
    component A V x Allowed J r G E hall i = 0 := by
  apply (cancel_epi (PrimeAdjacentExcision.relativeIso A V x J r hr G E).hom).1
  rw [comp_zero]
  dsimp only [component]
  rw [reassoc_of% (assembly_square A V x Allowed J r hr herase G E hall)]
  apply biproduct.hom_ext'
  intro v
  have hne : edgeIndex V Allowed J r hr herase v ≠ i := by
    intro he
    apply hi
    rw [← he]
    exact Finset.erase_subset _ _
  simp only [biproduct.ι_desc_assoc, Category.assoc, biproduct.ι_π_ne _ hne, comp_zero]

include hr herase in
theorem component_edge (v : J) :
    component A V x Allowed J r G E hall (edgeIndex V Allowed J r hr herase v) =
      (PrimeAdjacentExcision.relativeIso A V x J r hr G E).inv ≫
        biproduct.π (edgeCone A V x J r G) v ≫
          (edgeIso A V x Allowed J r hr herase G v).hom := by
  apply (cancel_epi (PrimeAdjacentExcision.relativeIso A V x J r hr G E).hom).1
  dsimp only [component]
  simp only [Iso.hom_inv_id_assoc]
  rw [reassoc_of% (assembly_square A V x Allowed J r hr herase G E hall)]
  apply biproduct.hom_ext'
  intro z
  by_cases h : z=v
  · subst z
    simp only [biproduct.ι_desc_assoc, Category.assoc, biproduct.ι_π_self,
      Category.comp_id, Category.id_comp, biproduct.ι_π_self_assoc]
  · have hne := fun he => h (edgeIndex_injective V Allowed J r hr herase he)
    simp only [biproduct.ι_desc_assoc, Category.assoc, biproduct.ι_π_ne _ hne,
      biproduct.ι_π_ne_assoc _ h, comp_zero, zero_comp]

#print axioms component
#print axioms component_zero
#print axioms component_edge
end Verification.PrimeAdjacentProjection
