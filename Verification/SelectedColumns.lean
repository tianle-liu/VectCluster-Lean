/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FreezingLattice

/-!
# Selected Columns

Full-rank and primitive column hypotheses pass to an independent
selected block after its zero rows are removed. This is a lattice bridge
from the full exchange matrix to the character maps of its strata.
-/
namespace Verification.SelectedColumns
open Verification.FreezingLattice
variable {R P Q M N : Type*} [CommRing R]
  [AddCommGroup P] [AddCommGroup Q] [AddCommGroup M] [AddCommGroup N]
  [Module R P] [Module R Q] [Module R M] [Module R N]

def selected (F : (P × Q) →ₗ[R] (M × N)) : P →ₗ[R] N :=
  (LinearMap.snd R M N).comp (F.comp (LinearMap.inl R P Q))

theorem selected_injective (F : (P × Q) →ₗ[R] (M × N))
    (hinj : Function.Injective F) (hzero : ∀ p : P, (F (p,0)).1 = 0) :
    Function.Injective (selected F) := by
  intro p q h
  have hh : F (p,0) = F (q,0) := by
    apply Prod.ext
    · rw [hzero,hzero]
    · exact h
  exact congrArg Prod.fst (hinj hh)

theorem selected_saturated [NoZeroSMulDivisors R Q]
    (F : (P × Q) →ₗ[R] (M × N)) (hinj : Function.Injective F)
    (hzero : ∀ p : P, (F (p,0)).1 = 0)
    (hs : Saturated (LinearMap.range F)) : Saturated (LinearMap.range (selected F)) := by
  intro a ha x hx
  obtain ⟨p,hp⟩ := hx
  have hax : a • (0,x) ∈ LinearMap.range F := by
    refine ⟨(p,0), ?_⟩
    apply Prod.ext
    · simpa using hzero p
    · exact hp
  obtain ⟨q,hq⟩ := hs a ha (0,x) hax
  have hmul : a • q = (p,0) := by
    apply hinj
    rw [map_smul,hq]
    apply Prod.ext
    · simp [hzero]
    · exact hp.symm
  have hq0 : q.2 = 0 := by
    have h := congrArg Prod.snd hmul
    change a • q.2 = 0 at h
    exact (smul_eq_zero.mp h).resolve_left ha
  refine ⟨q.1, ?_⟩
  change (F (q.1,0)).2 = x
  rw [← hq0]
  exact congrArg Prod.snd hq

#print axioms selected
#print axioms selected_injective
#print axioms selected_saturated
end Verification.SelectedColumns
