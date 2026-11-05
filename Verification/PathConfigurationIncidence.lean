/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathStrictTermIndices

/-!
# Path Configuration Incidence

Every incident pair of consecutive actual path strata is a unique literal insertion; nonincidence is preserved by the true mutable-set indexing.
-/
noncomputable section
namespace Verification.PathConfigurationIncidence
open Classical Finset Verification.PathCompression Verification.PathOriginalStratumTransport
open Verification.PathOriginalConfigurationIndex Verification.PathCochains

theorem mutable_subset {n : ℕ} {I J : Finset ℕ} (hI : Admissible n I) (hJ : Admissible n J) :
    mutableSet n I ⊆ mutableSet n J ↔ I⊆J := by
  constructor
  · intro h
    have hh := Finset.image_subset_image h (f:=fun i : Fin n=>i.val+1)
    change positions (mutableSet n I) ⊆ positions (mutableSet n J) at hh
    simpa only [positions_mutable hI,positions_mutable hJ] using hh
  · intro h i hi
    rw [mem_mutableSet] at hi ⊢
    exact h hi

theorem insertion {n : ℕ} (I J : Config n) (hcard : J.val.card=I.val.card+1) (h : I.val⊆J.val) :
    ∃ j,j∈Icc 1 n ∧ j∉I.val ∧ Addable I.val j ∧ J.val=insert j I.val := by
  have hex : ∃ j,j∈J.val ∧ j∉I.val := by
    by_contra hh
    push_neg at hh
    have hle := Finset.card_le_card hh
    omega
  obtain ⟨j,hj,hji⟩ := hex
  have he : insert j I.val=J.val := Finset.eq_of_subset_of_card_le (insert_subset hj h)
    (by rw [card_insert_of_not_mem hji];omega)
  refine ⟨j,J.property.1 hj,hji,?_,he.symm⟩
  exact addable_of_insert (he.symm ▸ J.property) hji

theorem erase_unique (J : Finset ℕ) (j k : ℕ) (hj : j∈J)
    (h : J.erase j=J.erase k) : j=k := by
  by_contra hne
  have hm : j∈J.erase k := mem_erase.mpr ⟨hne,hj⟩
  rw [←h] at hm
  exact (not_mem_erase j J) hm

theorem insert_erase (I : Finset ℕ) (j : ℕ) (hj : j∉I) : (insert j I).erase j=I :=
  Finset.erase_insert hj

#print axioms mutable_subset
#print axioms insertion
#print axioms erase_unique
#print axioms insert_erase
end Verification.PathConfigurationIncidence
