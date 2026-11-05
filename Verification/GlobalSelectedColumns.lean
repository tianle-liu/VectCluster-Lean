/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.AnticliqueSubcolumns
import Verification.GlobalExchangeSmooth
import Verification.ActualColumnRank

/-!
# Global Selected Columns

Identify the literal deleted-row lattice with the coordinates used in
the fixed global open charts. This links the maximal-set AS test to those
actual smoothness and regular-parameter theorems.
-/
noncomputable section
namespace Verification.GlobalSelectedColumns
open Verification.IndependentChartIndex Verification.FreezingLattice
variable (κ : Type) [Fintype κ] (n : ℕ)

def rowEquiv (I : Finset (Fin n)) :
    AnticliqueSubcolumns.Rows (C := κ) I ≃ (Other n I ⊕ κ) where
  toFun a := by
    rcases a with ⟨a,h⟩
    cases a with
    | inl v => exact Sum.inl ⟨v,fun hv => h v hv rfl⟩
    | inr c => exact Sum.inr c
  invFun a := match a with
    | Sum.inl v => ⟨Sum.inl v.val, by
        intro w hw h
        have := Sum.inl.inj h
        exact v.property (this ▸ hw)⟩
    | Sum.inr c => ⟨Sum.inr c,by simp⟩
  left_inv a := by rcases a with ⟨a,h⟩; cases a <;> rfl
  right_inv a := by cases a <;> rfl

def rowLinear (I : Finset (Fin n)) :
    (AnticliqueSubcolumns.Rows (C := κ) I →₀ ℤ) ≃ₗ[ℤ] ((Other n I ⊕ κ) →₀ ℤ) :=
  Finsupp.domLCongr (rowEquiv κ n I)

theorem columns_agree (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
    (I : Finset (Fin n)) :
    (rowLinear κ n I).toLinearMap.comp
      (AnticliqueSubcolumns.selectedMap (fun a v => B a (Sum.inl v)) I) =
      GlobalExchangeSmooth.selectedMap κ n B I := by
  classical
  apply Finsupp.lhom_ext'
  intro i
  apply LinearMap.ext_ring
  ext a
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply,
    AnticliqueSubcolumns.selectedMap, Finsupp.linearCombination_single, one_smul,
    GlobalExchangeSmooth.selectedMap, ActualOpenGeometry.columnMap_single]
  rw [ActualColumnRank.actual_column_apply]
  simp only [rowLinear, Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_apply]
  cases a <;> rfl

theorem injective_iff (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
    (I : Finset (Fin n)) :
    Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I) ↔
      Function.Injective (AnticliqueSubcolumns.selectedMap (fun a v => B a (Sum.inl v)) I) := by
  rw [← columns_agree κ n B I]
  exact (rowLinear κ n I).injective.of_comp_iff _

theorem saturated_equiv {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    (e : M ≃ₗ[ℤ] N) (f : P →ₗ[ℤ] M) :
    Saturated (LinearMap.range (e.toLinearMap.comp f)) ↔ Saturated (LinearMap.range f) := by
  constructor
  · intro hs a ha x hx
    obtain ⟨p,hp⟩ := hx
    obtain ⟨q,hq⟩ := hs a ha (e x) ⟨p,by change e (f p)=a • e x; rw [hp,map_smul]⟩
    exact ⟨q,e.injective hq⟩
  · intro hs a ha x hx
    obtain ⟨p,hp⟩ := hx
    have hpx : f p=a • e.symm x := by
      apply e.injective
      simpa only [map_smul,LinearEquiv.apply_symm_apply] using hp
    obtain ⟨q,hq⟩ := hs a ha (e.symm x) ⟨p,hpx⟩
    refine ⟨q,?_⟩
    change e (f q)=x
    rw [hq,LinearEquiv.apply_symm_apply]

theorem AS_iff (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
    (I : Finset (Fin n)) :
    (Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I) ∧
      Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I))) ↔
      AnticliqueSubcolumns.AS (fun a v => B a (Sum.inl v)) I := by
  rw [AnticliqueSubcolumns.AS, injective_iff, ← columns_agree κ n B I,
    saturated_equiv]

#print axioms rowEquiv
#print axioms rowLinear
#print axioms columns_agree
#print axioms injective_iff
#print axioms saturated_equiv
#print axioms AS_iff
end Verification.GlobalSelectedColumns
