/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualColumnRank
import Verification.CliqueSaturation
import Verification.SaturatedSmith

/-!
# Actual Clique Columns

The frozen clique rows retract the literal Finsupp character map of
an actual open chart. This applies even if the full exchange matrix has
deficient rank; only colors of the selected independent set must differ.
-/
noncomputable section
universe u
namespace Verification.ActualCliqueColumns
open Verification.ActualOpenGeometry Verification.ActualOpenChart
variable {I T C : Type u} [Fintype I] [Fintype T] [Fintype C] [DecidableEq C]

def frozenRetraction (c : I → C) : ((T ⊕ C) →₀ ℤ) →ₗ[ℤ] (I →₀ ℤ) where
  toFun x := Finsupp.equivFunOnFinite.symm (fun i => x (Sum.inr (c i)))
  map_add' x y := by ext i; rfl
  map_smul' a x := by ext i; rfl

theorem frozen_rows_split (B : (I ⊕ (T ⊕ C)) → (I ⊕ T) → ℤ) (c : I → C)
    (hc : Function.Injective c)
    (hC : ∀ a i, B (Sum.inr (Sum.inr a)) (Sum.inl i) = if c i = a then 1 else 0) :
    (frozenRetraction (T := T) c).comp (columnMap I (T ⊕ C) T B) = LinearMap.id := by
  classical
  apply Finsupp.lhom_ext'
  intro i
  apply LinearMap.ext_ring
  apply Finsupp.ext
  intro j
  change (columnMap I (T ⊕ C) T B (Finsupp.single i 1)) (Sum.inr (c j)) =
    Finsupp.single i 1 j
  rw [columnMap_single, Verification.ActualColumnRank.actual_column_apply, hC]
  simp [hc.eq_iff, Finsupp.single_apply]

theorem actual_clique_AS (B : (I ⊕ (T ⊕ C)) → (I ⊕ T) → ℤ) (c : I → C)
    (hc : Function.Injective c)
    (hC : ∀ a i, B (Sum.inr (Sum.inr a)) (Sum.inl i) = if c i = a then 1 else 0) :
    Function.Injective (columnMap I (T ⊕ C) T B) ∧
      Verification.FreezingLattice.Saturated (LinearMap.range (columnMap I (T ⊕ C) T B)) := by
  have hleft : Function.LeftInverse (frozenRetraction (T := T) c) (columnMap I (T ⊕ C) T B) :=
    fun x => LinearMap.congr_fun (frozen_rows_split B c hc hC) x
  exact ⟨hleft.injective, Verification.CliqueSaturation.split_range_saturated _ _ hleft⟩

variable (R : Type u) [CommRing R]

theorem actual_clique_open_smooth (B : (I ⊕ (T ⊕ C)) → (I ⊕ T) → ℤ) (c : I → C)
    (hc : Function.Injective c)
    (hC : ∀ a i, B (Sum.inr (Sum.inr a)) (Sum.inl i) = if c i = a then 1 else 0)
    (hB : ∀ a i : I, B (Sum.inl a) (Sum.inl i) = 0) :
    Algebra.Smooth R (GlobalOpen R I (T ⊕ C) T Sum.inl B) ∧
      Algebra.Smooth (MvPolynomial I R) (GlobalOpen R I (T ⊕ C) T Sum.inl B) := by
  obtain ⟨hinj,hs⟩ := actual_clique_AS B c hc hC
  exact ⟨Verification.SaturatedSmith.globalOpen_smooth_saturated R I (T ⊕ C) T
      Sum.inl B hB hinj hs,
    Verification.SaturatedSmith.globalOpen_parameters_smooth_saturated R I (T ⊕ C) T
      Sum.inl B hB hinj hs⟩

#print axioms frozenRetraction
#print axioms frozen_rows_split
#print axioms actual_clique_AS
#print axioms actual_clique_open_smooth
end Verification.ActualCliqueColumns
