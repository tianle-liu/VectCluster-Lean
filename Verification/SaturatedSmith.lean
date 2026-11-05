/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualOpenGeometry
import Verification.FreezingLattice
import Mathlib.Algebra.Group.Int.Units

/-!
# Saturated Smith

Saturation forces every nonzero Smith coefficient to be a unit.
Consequently the actual AS open charts and their original-coordinate
parameter maps are smooth over every coefficient ring.
-/
namespace Verification.SaturatedSmith
open Verification.FreezingLattice Verification.SmithCharacters
variable {M ι : Type*} [AddCommGroup M] {N : Submodule ℤ M} {n : ℕ}

theorem coefficient_isUnit (s : Basis.SmithNormalForm N ι n) (hs : Saturated N) (i : Fin n) :
    IsUnit (s.a i) := by
  have hm : s.bM (s.f i) ∈ N := hs (s.a i) (smith_coefficient_ne_zero s i) _
    (by rw [← s.snf]; exact (s.bN i).property)
  have h := s.repr_apply_embedding_eq_repr_smul (⟨s.bM (s.f i),hm⟩ : N) (i := i)
  have heq : 1 = s.a i * s.bN.repr (⟨s.bM (s.f i),hm⟩ : N) i := by
    simpa only [s.bM.repr_self, Finsupp.single_eq_same, map_smul, Finsupp.smul_apply,
      smul_eq_mul] using h
  exact isUnit_iff_dvd_one.mpr ⟨_,heq⟩

theorem coefficient_natAbs (s : Basis.SmithNormalForm N ι n) (hs : Saturated N) (i : Fin n) :
    (s.a i).natAbs = 1 := Int.natAbs_of_isUnit (coefficient_isUnit s hs i)

universe u
variable (R I K T : Type u) [CommRing R] [Fintype I] [Fintype K]
open Verification.ActualOpenGeometry Verification.ActualOpenChart

theorem globalOpen_smooth_saturated (j : T → K) (B : (I ⊕ K) → (I ⊕ T) → ℤ)
    (hB : ∀ a i : I, B (Sum.inl a) (Sum.inl i) = 0)
    (hf : Function.Injective (columnMap I K T B))
    (hs : Saturated (LinearMap.range (columnMap I K T B))) :
    Algebra.Smooth R (GlobalOpen R I K T j B) := by
  obtain ⟨n,s⟩ := (LinearMap.range (columnMap I K T B)).smithNormalForm Finsupp.basisSingleOne
  apply globalOpen_smooth R I K T j B hB hf s
  intro i
  simp only [coefficient_natAbs s hs, Nat.cast_one, isUnit_one]

theorem globalOpen_parameters_smooth_saturated (j : T → K) (B : (I ⊕ K) → (I ⊕ T) → ℤ)
    (hB : ∀ a i : I, B (Sum.inl a) (Sum.inl i) = 0)
    (hf : Function.Injective (columnMap I K T B))
    (hs : Saturated (LinearMap.range (columnMap I K T B))) :
    Algebra.Smooth (MvPolynomial I R) (GlobalOpen R I K T j B) := by
  obtain ⟨n,s⟩ := (LinearMap.range (columnMap I K T B)).smithNormalForm Finsupp.basisSingleOne
  apply globalOpen_parameters_smooth R I K T j B hB hf s
  intro i
  simp only [coefficient_natAbs s hs, Nat.cast_one, isUnit_one]

#print axioms coefficient_isUnit
#print axioms coefficient_natAbs
#print axioms globalOpen_smooth_saturated
#print axioms globalOpen_parameters_smooth_saturated
end Verification.SaturatedSmith
