/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimeAdjacentExcision
import Verification.ConeDerivedComparison

/-!
# Prime Adjacent Assembly

The preceding layer in a fixed coordinate chart maps to the global
preceding layer by the literal inclusion of opens. Its finite excision
summands land in exactly the corresponding global summands.
-/
noncomputable section
namespace Verification.PrimeAdjacentAssembly
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.PrimeCoordinateFiltration Verification.PrimeLayerCover
open Verification.PrimeAdjacentExcision
universe w
variable (A V : Type) [CommRing A] [Fintype V] [DecidableEq V]
variable (x : V → A) (Allowed : Finset V → Prop)
variable (J : Finset V) (r : ℕ) (hr : J.card = r+1)
variable (herase : ∀ v : J, Allowed (J.erase v.val))

def edgeIndex (v : J) : Index Allowed r :=
  ⟨J.erase v.val, by rw [Finset.card_erase_of_mem v.property, hr]; omega, herase v⟩

omit [Fintype V] in
theorem edgeIndex_injective : Function.Injective (edgeIndex V Allowed J r hr herase) := by
  intro v z h
  apply Subtype.ext
  have he : J.erase v.val = J.erase z.val := congrArg Subtype.val h
  by_contra hne
  have hv : v.val ∈ J.erase z.val := Finset.mem_erase.mpr ⟨hne, v.property⟩
  rw [← he] at hv
  exact Finset.not_mem_erase _ _ hv

theorem edge_previous (v : J) :
    previous A V x J r ⊓ edgeChart A V x J v = stage x r ⊓ edgeChart A V x J v := by
  dsimp only [previous, edgeChart]
  rw [inf_assoc, inf_eq_right.mpr (Verification.PrimeAdjacentCharts.chart_erase_le x J v)]

variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (G : Scheme ⥤ CochainComplex C ℤ)
local notation "F" => PrimeLayerExcision.openChains A G

def edgeIso (v : J) : edgeCone A V x J r G v ≅
    PrimeLayerExcision.localRelative A V x Allowed G r (edgeIndex V Allowed J r hr herase v) :=
  ConeDerivedComparison.coneIso _ _
    ((F).map (eqToHom (edge_previous A V x J r v))) (𝟙 _)
    (by simp only [OpenConeExcision.localArrow, Category.comp_id, ← CategoryTheory.Functor.map_comp]; congr 1)

def rowMap : DerivedCategory.Q.obj (mappingCone (rowArrow A V x J r G)) ⟶
    DerivedCategory.Q.obj (FilteredConeComplex.relative (PrimeSchemeFiltration.filteredChains A x G) r) :=
  DerivedCategory.Q.map (OpenFlagBoundary.rowMap (Spec (CommRingCat.of A)) F
    (stage x r) (stage x (r+1)) (stage_mono x (Nat.le_succ r)) (openBy x J))

theorem edge_square (v : J) :
    biproduct.ι (edgeCone A V x J r G) v ≫ assembly A V x J r hr G ≫ rowMap A V x J r G =
      (edgeIso A V x Allowed J r hr herase G v).hom ≫
        biproduct.ι (PrimeLayerExcision.localRelative A V x Allowed G r)
          (edgeIndex V Allowed J r hr herase v) ≫ PrimeLayerExcision.assembly A V x Allowed G r := by
  simp only [assembly, PrimeLayerExcision.assembly, OpenConeExcision.assembly,
    biproduct.ι_desc_assoc, biproduct.ι_desc]
  simp only [OpenConeExcision.localMap, TransverseDerivedBoundary.coneMap,
    edgeIso, ConeDerivedComparison.coneIso, asIso_hom, rowMap, OpenFlagBoundary.rowMap,
    TransverseConeBoundary.coneMap, ← CategoryTheory.Functor.map_comp, ← mappingCone.map_comp]
  congr 1
  change mappingCone.map _ _ _ _ _ ≫ mappingCone.map _ _ _ _ _ = _
  rw [← mappingCone.map_comp]
  congr 1
  · simp only [← CategoryTheory.Functor.map_comp]
    congr 1
  · simp only [Category.id_comp, ← CategoryTheory.Functor.map_comp]
    congr 1

variable (E : OpenConeExcision.StandardExcision G)
variable (hall : ∀ p : PrimeSpectrum A, Allowed (zeroSet x p))

theorem assembly_square :
    (PrimeAdjacentExcision.relativeIso A V x J r hr G E).hom ≫ rowMap A V x J r G ≫
      (PrimeLayerExcision.relativeIso A V x Allowed G E hall r).inv =
        biproduct.desc (fun v : J => (edgeIso A V x Allowed J r hr herase G v).hom ≫
          biproduct.ι (PrimeLayerExcision.localRelative A V x Allowed G r)
            (edgeIndex V Allowed J r hr herase v)) := by
  apply biproduct.hom_ext'
  intro v
  rw [biproduct.ι_desc]
  have hh := congrArg (fun f => f ≫ (PrimeLayerExcision.relativeIso A V x Allowed G E hall r).inv)
    (edge_square A V x Allowed J r hr herase G v)
  have ha : PrimeLayerExcision.assembly A V x Allowed G r =
    (PrimeLayerExcision.relativeIso A V x Allowed G E hall r).hom := rfl
  rw [ha] at hh
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hh

#print axioms edgeIndex
#print axioms edgeIndex_injective
#print axioms edge_previous
#print axioms edgeIso
#print axioms rowMap
#print axioms edge_square
#print axioms assembly_square
end Verification.PrimeAdjacentAssembly
