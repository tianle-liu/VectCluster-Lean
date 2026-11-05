/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimitiveLattice
import Verification.CliqueSaturation

/-!
# Anticlique Subcolumns

AS passes from a set of selected columns to a subset for the literal
matrix with the corresponding rows deleted. The construction projects away
the restored rows and retracts the retained column coordinates.
-/
noncomputable section
namespace Verification.AnticliqueSubcolumns
open Verification.FreezingLattice
variable {V C : Type*} [Fintype V] [Fintype C]

def Rows (I : Finset V) := {a : V ⊕ C // ∀ v ∈ I, a ≠ Sum.inl v}

noncomputable instance rowsFintype (I : Finset V) : Fintype (Rows (C := C) I) := by
  classical
  exact inferInstanceAs (Fintype {a : V ⊕ C // ∀ v ∈ I, a ≠ Sum.inl v})

def column (B : (V ⊕ C) → V → ℤ) (I : Finset V) (i : I) : Rows (C := C) I →₀ ℤ :=
  Finsupp.equivFunOnFinite.symm (fun a => B a.val i.val)

def selectedMap (B : (V ⊕ C) → V → ℤ) (I : Finset V) :
    (I →₀ ℤ) →ₗ[ℤ] (Rows (C := C) I →₀ ℤ) := Finsupp.linearCombination ℤ (column B I)

def rowProjection {I J : Finset V} (h : I ⊆ J) :
    (Rows (C := C) I →₀ ℤ) →ₗ[ℤ] (Rows (C := C) J →₀ ℤ) where
  toFun x := Finsupp.equivFunOnFinite.symm
    (fun a => x ⟨a.val,fun v hv => a.property v (h hv)⟩)
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

def columnInjection {I J : Finset V} (h : I ⊆ J) : (I →₀ ℤ) →ₗ[ℤ] (J →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun i : I => (⟨i.val,h i.property⟩ : J))

def columnProjection {I J : Finset V} (h : I ⊆ J) : (J →₀ ℤ) →ₗ[ℤ] (I →₀ ℤ) where
  toFun x := Finsupp.equivFunOnFinite.symm (fun i : I => x ⟨i.val,h i.property⟩)
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

theorem columns_split {I J : Finset V} (h : I ⊆ J) :
    (columnProjection h).comp (columnInjection h) = LinearMap.id := by
  classical
  apply Finsupp.lhom_ext'
  intro i
  apply LinearMap.ext_ring
  ext j
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, columnInjection,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, LinearMap.id_apply]
  change Finsupp.single (⟨i.val,h i.property⟩ : J) (1 : ℤ) ⟨j.val,h j.property⟩ =
    Finsupp.single i 1 j
  simp [Finsupp.single_apply, Subtype.ext_iff]

theorem maps_compatible (B : (V ⊕ C) → V → ℤ) {I J : Finset V} (h : I ⊆ J) :
    (rowProjection (C := C) h).comp (selectedMap B I) =
      (selectedMap B J).comp (columnInjection h) := by
  classical
  apply Finsupp.lhom_ext'
  intro i
  apply LinearMap.ext_ring
  ext a
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, selectedMap,
    Finsupp.linearCombination_single, one_smul, columnInjection,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rfl

def AS (B : (V ⊕ C) → V → ℤ) (I : Finset V) : Prop :=
  Function.Injective (selectedMap B I) ∧ Saturated (LinearMap.range (selectedMap B I))

theorem AS_subset (B : (V ⊕ C) → V → ℤ) {I J : Finset V} (h : I ⊆ J)
    (hJ : AS B J) : AS B I := by
  obtain ⟨e,he⟩ := Verification.PrimitiveLattice.primitive_columns_split_compatible
    (selectedMap B J) hJ.1 hJ.2
  let r := (columnProjection h).comp ((LinearMap.fst ℤ _ _).comp
    (e.toLinearMap.comp (rowProjection (C := C) h)))
  have hleft : Function.LeftInverse r (selectedMap B I) := by
    intro x
    change columnProjection h ((e (rowProjection h (selectedMap B I x))).1) = x
    have hx := LinearMap.congr_fun (maps_compatible B h) x
    change rowProjection h (selectedMap B I x) = selectedMap B J (columnInjection h x) at hx
    rw [hx, he]
    exact LinearMap.congr_fun (columns_split h) x
  exact ⟨hleft.injective,Verification.CliqueSaturation.split_range_saturated _ _ hleft⟩

#print axioms Rows
#print axioms rowsFintype
#print axioms column
#print axioms selectedMap
#print axioms rowProjection
#print axioms columnInjection
#print axioms columnProjection
#print axioms columns_split
#print axioms maps_compatible
#print axioms AS
#print axioms AS_subset
end Verification.AnticliqueSubcolumns
