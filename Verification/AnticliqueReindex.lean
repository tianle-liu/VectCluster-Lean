/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ExchangeReindex
import Verification.GlobalSelectedColumns

/-!
# Anticlique Reindex

Actual conjugacy of the selected integer column maps under arbitrary
mutable reindexing. Both deleted-row lattices and selected-column lattices
are identified, so injectivity and saturation are equivalent without a
full-matrix rank assumption.
-/
noncomputable section
namespace Verification.AnticliqueReindex
open Verification.ExchangeReindex Verification.AnticliqueSubcolumns Verification.FreezingLattice
variable {V W C : Type} [Fintype V] [Fintype W] [Fintype C]
variable (e : V ≃ W) (B : (W ⊕ C) → W → ℤ) (I : Finset V)

def selectedEquiv : I ≃ I.map e.toEmbedding :=
  Equiv.ofBijective (fun i => ⟨e i.val,Finset.mem_map.mpr ⟨i.val,i.property,rfl⟩⟩) (by
    constructor
    · intro i j h
      exact Subtype.ext (e.injective (congrArg Subtype.val h))
    · intro j
      obtain ⟨i,hi,hij⟩ := Finset.mem_map.mp j.property
      exact ⟨⟨i,hi⟩,Subtype.ext hij⟩)

def rowEquiv : Rows (C := C) I ≃ Rows (C := C) (I.map e.toEmbedding) where
  toFun r := ⟨rows e r.val,by
    intro w hw h
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hw
    apply r.property i hi
    exact (rows e).injective h⟩
  invFun r := ⟨(rows e).symm r.val,by
    intro i hi h
    apply r.property (e i) (Finset.mem_map.mpr ⟨i,hi,rfl⟩)
    have hh := congrArg (rows e) h
    simpa only [Equiv.apply_symm_apply,rows_inl] using hh⟩
  left_inv r := Subtype.ext ((rows e).symm_apply_apply r.val)
  right_inv r := Subtype.ext ((rows e).apply_symm_apply r.val)

def columnLinear : (I →₀ ℤ) ≃ₗ[ℤ] (I.map e.toEmbedding →₀ ℤ) :=
  Finsupp.domLCongr (selectedEquiv e I)

def rowLinear : (Rows (C := C) I →₀ ℤ) ≃ₗ[ℤ] (Rows (C := C) (I.map e.toEmbedding) →₀ ℤ) :=
  Finsupp.domLCongr (rowEquiv (C := C) e I)

theorem column_agrees (i : I) :
    rowLinear (C := C) e I (column (matrix e B) I i) =
      column B (I.map e.toEmbedding) (selectedEquiv e I i) := by
  ext a
  simp only [rowLinear, Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_apply]
  change B (rows e ((rows e).symm a.val)) (e i.val) = B a.val (e i.val)
  rw [Equiv.apply_symm_apply]

theorem selectedMap_conjugate :
    (rowLinear (C := C) e I).toLinearMap.comp (selectedMap (matrix e B) I) =
      (selectedMap B (I.map e.toEmbedding)).comp (columnLinear e I).toLinearMap := by
  apply Finsupp.lhom_ext'
  intro i
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, selectedMap,
    Finsupp.linearCombination_single, one_smul, columnLinear, LinearEquiv.coe_coe,
    Finsupp.domLCongr_single]
  exact column_agrees e B I i

theorem range_precomp_equiv {P Q N : Type*} [AddCommGroup P] [AddCommGroup Q] [AddCommGroup N]
    (c : P ≃ₗ[ℤ] Q) (g : Q →ₗ[ℤ] N) : LinearMap.range (g.comp c.toLinearMap) = LinearMap.range g := by
  ext x
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨c p,rfl⟩
  · rintro ⟨q,rfl⟩
    exact ⟨c.symm q,by simp⟩

theorem injective_precomp_equiv {P Q N : Type*} [AddCommGroup P] [AddCommGroup Q] [AddCommGroup N]
    (c : P ≃ₗ[ℤ] Q) (g : Q →ₗ[ℤ] N) : Function.Injective (g.comp c.toLinearMap) ↔ Function.Injective g := by
  constructor
  · intro h x y hxy
    apply c.symm.injective
    apply h
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using hxy
  · intro h
    exact h.comp c.injective

theorem injective_iff : Function.Injective (selectedMap (matrix e B) I) ↔
    Function.Injective (selectedMap B (I.map e.toEmbedding)) := by
  calc
    Function.Injective (selectedMap (matrix e B) I) ↔
        Function.Injective ((rowLinear (C := C) e I).toLinearMap.comp (selectedMap (matrix e B) I)) :=
      ((rowLinear (C := C) e I).injective.of_comp_iff _).symm
    _ ↔ Function.Injective ((selectedMap B (I.map e.toEmbedding)).comp (columnLinear e I).toLinearMap) := by
      rw [selectedMap_conjugate]
    _ ↔ _ := injective_precomp_equiv _ _

theorem saturated_iff : Saturated (LinearMap.range (selectedMap (matrix e B) I)) ↔
    Saturated (LinearMap.range (selectedMap B (I.map e.toEmbedding))) := by
  rw [← GlobalSelectedColumns.saturated_equiv (rowLinear (C := C) e I),
    selectedMap_conjugate, range_precomp_equiv]

theorem AS_iff : AS B (I.map e.toEmbedding) ↔ AS (matrix e B) I := by
  exact (and_congr (injective_iff e B I) (saturated_iff e B I)).symm

#print axioms selectedEquiv
#print axioms rowEquiv
#print axioms columnLinear
#print axioms rowLinear
#print axioms column_agrees
#print axioms selectedMap_conjugate
#print axioms range_precomp_equiv
#print axioms injective_precomp_equiv
#print axioms injective_iff
#print axioms saturated_iff
#print axioms AS_iff
end Verification.AnticliqueReindex
