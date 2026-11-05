/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualOpenGeometry
import Verification.SelectedColumns

/-!
# Actual Column Rank

Rank and saturation of the actual stratum character columns are derived
from the full original exchange matrix and its independent zero block.
-/
noncomputable section
namespace Verification.ActualColumnRank
open Verification.FreezingLattice
universe u
variable {I K T : Type u} [Fintype I] [Fintype K]

def fullColumn (B : (I ⊕ K) → (I ⊕ T) → ℤ) (v : I ⊕ T) : (I ⊕ K) →₀ ℤ :=
  Finsupp.equivFunOnFinite.symm (fun a => B a v)

theorem fullColumn_apply (B : (I ⊕ K) → (I ⊕ T) → ℤ) (v : I ⊕ T) (a : I ⊕ K) :
    fullColumn B v a = B a v := rfl

def fullMap (B : (I ⊕ K) → (I ⊕ T) → ℤ) :
    ((I ⊕ T) →₀ ℤ) →ₗ[ℤ] ((I ⊕ K) →₀ ℤ) := Finsupp.linearCombination ℤ (fullColumn B)

theorem fullMap_single (B : (I ⊕ K) → (I ⊕ T) → ℤ) (v : I ⊕ T) :
    fullMap B (Finsupp.single v 1) = fullColumn B v := by simp [fullMap]

def fullProductMap (B : (I ⊕ K) → (I ⊕ T) → ℤ) :
    ((I →₀ ℤ) × (T →₀ ℤ)) →ₗ[ℤ] ((I →₀ ℤ) × (K →₀ ℤ)) :=
  (Finsupp.sumFinsuppLEquivProdFinsupp ℤ).toLinearMap.comp
    ((fullMap B).comp (Finsupp.sumFinsuppLEquivProdFinsupp ℤ).symm.toLinearMap)

omit [Fintype I] in
theorem split_single_left (i : I) :
    (Finsupp.sumFinsuppLEquivProdFinsupp ℤ).symm
      ((Finsupp.single i 1 : I →₀ ℤ), (0 : T →₀ ℤ)) = Finsupp.single (Sum.inl i) 1 := by
  classical
  ext a
  cases a <;> simp [Finsupp.sumFinsuppLEquivProdFinsupp_symm_inl,
    Finsupp.sumFinsuppLEquivProdFinsupp_symm_inr, Finsupp.single_apply]

omit [Fintype I] in
theorem actual_column_apply (B : (I ⊕ K) → (I ⊕ T) → ℤ) (i : I) (k : K) :
    Verification.ActualOpenChart.column I K T B i k = B (Sum.inr k) (Sum.inl i) := by
  classical
  simp [Verification.ActualOpenChart.column, Verification.ExchangeCharacters.column,
    Finsupp.sum_apply, Finsupp.smul_apply, Finsupp.single_apply]

theorem productMap_selected_single (B : (I ⊕ K) → (I ⊕ T) → ℤ)
    (hB : ∀ a i : I, B (Sum.inl a) (Sum.inl i) = 0) (i : I) :
    fullProductMap B (Finsupp.single i 1, 0) =
      (0, Verification.ActualOpenGeometry.columnMap I K T B (Finsupp.single i 1)) := by
  simp only [fullProductMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    split_single_left, fullMap_single, Verification.ActualOpenGeometry.columnMap_single]
  apply Prod.ext
  · ext a
    change fullColumn B (Sum.inl i) (Sum.inl a) = 0
    exact hB a i
  · ext k
    change fullColumn B (Sum.inl i) (Sum.inr k) = _
    rw [fullColumn_apply, actual_column_apply]

theorem productMap_selected (B : (I ⊕ K) → (I ⊕ T) → ℤ)
    (hB : ∀ a i : I, B (Sum.inl a) (Sum.inl i) = 0) :
    (fullProductMap B).comp (LinearMap.inl ℤ (I →₀ ℤ) (T →₀ ℤ)) =
      (LinearMap.inr ℤ (I →₀ ℤ) (K →₀ ℤ)).comp
        (Verification.ActualOpenGeometry.columnMap I K T B) := by
  apply Finsupp.lhom_ext'
  intro i
  apply LinearMap.ext_ring
  exact productMap_selected_single B hB i

theorem productMap_zero_block (B : (I ⊕ K) → (I ⊕ T) → ℤ)
    (hB : ∀ a i : I, B (Sum.inl a) (Sum.inl i) = 0) (p : I →₀ ℤ) :
    (fullProductMap B (p,0)).1 = 0 :=
  congrArg Prod.fst (LinearMap.congr_fun (productMap_selected B hB) p)

theorem selected_eq_actual (B : (I ⊕ K) → (I ⊕ T) → ℤ)
    (hB : ∀ a i : I, B (Sum.inl a) (Sum.inl i) = 0) :
    Verification.SelectedColumns.selected (fullProductMap B) =
      Verification.ActualOpenGeometry.columnMap I K T B := by
  apply LinearMap.ext
  intro p
  exact congrArg Prod.snd (LinearMap.congr_fun (productMap_selected B hB) p)

theorem fullProductMap_injective (B : (I ⊕ K) → (I ⊕ T) → ℤ)
    (hinj : Function.Injective (fullMap B)) : Function.Injective (fullProductMap B) :=
  (Finsupp.sumFinsuppLEquivProdFinsupp ℤ).injective.comp
    (hinj.comp (Finsupp.sumFinsuppLEquivProdFinsupp ℤ).symm.injective)

theorem actual_columnMap_injective (B : (I ⊕ K) → (I ⊕ T) → ℤ)
    (hB : ∀ a i : I, B (Sum.inl a) (Sum.inl i) = 0)
    (hinj : Function.Injective (fullMap B)) :
    Function.Injective (Verification.ActualOpenGeometry.columnMap I K T B) := by
  rw [← selected_eq_actual B hB]
  exact Verification.SelectedColumns.selected_injective _ (fullProductMap_injective B hinj)
    (productMap_zero_block B hB)

theorem fullProductMap_saturated (B : (I ⊕ K) → (I ⊕ T) → ℤ)
    (hs : Saturated (LinearMap.range (fullMap B))) :
    Saturated (LinearMap.range (fullProductMap B)) := by
  let e : ((I ⊕ K) →₀ ℤ) ≃ₗ[ℤ] ((I →₀ ℤ) × (K →₀ ℤ)) :=
    Finsupp.sumFinsuppLEquivProdFinsupp ℤ
  let d : ((I ⊕ T) →₀ ℤ) ≃ₗ[ℤ] ((I →₀ ℤ) × (T →₀ ℤ)) :=
    Finsupp.sumFinsuppLEquivProdFinsupp ℤ
  intro a ha x hx
  obtain ⟨p,hp⟩ := hx
  have hax : a • e.symm x ∈ LinearMap.range (fullMap B) := by
    refine ⟨d.symm p, ?_⟩
    have h := congrArg e.symm hp
    change e.symm (e (fullMap B (d.symm p))) = e.symm (a • x) at h
    simpa only [LinearEquiv.symm_apply_apply, map_smul] using h
  obtain ⟨q,hq⟩ := hs a ha (e.symm x) hax
  refine ⟨d q, ?_⟩
  change e (fullMap B (d.symm (d q))) = x
  rw [LinearEquiv.symm_apply_apply,hq,LinearEquiv.apply_symm_apply]

theorem actual_columnMap_saturated (B : (I ⊕ K) → (I ⊕ T) → ℤ)
    (hB : ∀ a i : I, B (Sum.inl a) (Sum.inl i) = 0)
    (hinj : Function.Injective (fullMap B)) (hs : Saturated (LinearMap.range (fullMap B))) :
    Saturated (LinearMap.range (Verification.ActualOpenGeometry.columnMap I K T B)) := by
  rw [← selected_eq_actual B hB]
  exact Verification.SelectedColumns.selected_saturated _ (fullProductMap_injective B hinj)
    (productMap_zero_block B hB) (fullProductMap_saturated B hs)

#print axioms fullColumn
#print axioms fullColumn_apply
#print axioms fullMap
#print axioms fullMap_single
#print axioms fullProductMap
#print axioms split_single_left
#print axioms actual_column_apply
#print axioms productMap_selected_single
#print axioms productMap_selected
#print axioms productMap_zero_block
#print axioms selected_eq_actual
#print axioms fullProductMap_injective
#print axioms actual_columnMap_injective
#print axioms fullProductMap_saturated
#print axioms actual_columnMap_saturated
end Verification.ActualColumnRank
