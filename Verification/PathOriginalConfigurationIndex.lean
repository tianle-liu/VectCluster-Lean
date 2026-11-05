/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOriginalIndependence
import Verification.PathCochains
import Verification.PathCoefficientProjection

/-!
# Path Original Configuration Index

Every independent set of the actual path matrix occurs exactly once in
its one-based literal path configurations, with the same codimension.
-/
noncomputable section
namespace Verification.PathOriginalConfigurationIndex
open Finset Verification.PathCompression Verification.PathOriginalStratumTransport
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
variable {κ : Type} {n : ℕ}
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hB : ∀ a i : Fin n,B (Sum.inl a) (Sum.inl i)=PathLattice.pathMatrix n a i)

def positions (J : Finset (Fin n)) : Finset ℕ := J.image (fun i => i.val+1)

theorem mem_positions (J : Finset (Fin n)) (i : Fin n) : i.val+1∈positions J ↔ i∈J := by
  simp only [positions,mem_image]
  constructor
  · rintro ⟨a,ha,he⟩
    have : a=i := Fin.ext (by omega)
    simpa only [this] using ha
  · intro hi;exact ⟨i,hi,rfl⟩

theorem mutable_positions (J : Finset (Fin n)) : mutableSet n (positions J)=J := by
  ext i;rw [mem_mutableSet,mem_positions]

theorem positions_mutable {I : Finset ℕ} (hI : Admissible n I) : positions (mutableSet n I)=I := by
  ext k
  constructor
  · intro hk
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hk
    exact (mem_mutableSet n I i).mp hi
  · intro hk
    have hb := mem_Icc.mp (hI.1 hk)
    let i : Fin n := ⟨k-1,by omega⟩
    have he : i.val+1=k := by dsimp [i];omega
    exact mem_image.mpr ⟨i,(mem_mutableSet n I i).mpr (he ▸ hk),he⟩

include hB in
theorem admissible {J : Finset (Fin n)} (hJ : Independent (laterWeights κ n B) J) :
    Admissible n (positions J) := by
  constructor
  · intro k hk
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hk
    exact mem_Icc.mpr ⟨by omega,by have := i.isLt;omega⟩
  · intro k hk hk'
    obtain ⟨i,hi,he⟩ := mem_image.mp hk
    obtain ⟨j,hj,he'⟩ := mem_image.mp hk'
    have hij : j.val=i.val+1 := by omega
    have hji : ¬ i.val=j.val+1 := by omega
    have hn := hJ i hi j hj
    apply hn
    have hi_lt : i < j := Fin.lt_def.mpr (by omega)
    have hh : ¬ i.val=i.val+1+1 := by omega
    simp [ExchangeRing.Adjacent,laterWeights,hB,PathLattice.pathMatrix,hij,hh,hi_lt]

def configEquiv : PathCochains.Config n ≃ {J : Finset (Fin n) // Independent (laterWeights κ n B) J} where
  toFun I := ⟨mutableSet n I.val,PathOriginalIndependence.independent B hB I.property⟩
  invFun J := ⟨positions J.val,admissible B hB J.property⟩
  left_inv I := Subtype.ext (positions_mutable I.property)
  right_inv J := Subtype.ext (mutable_positions J.val)

theorem positions_card (J : Finset (Fin n)) : (positions J).card=J.card := by
  apply card_image_of_injective
  intro i j h
  exact Fin.ext (by dsimp at h;omega)

theorem config_card (I : PathCochains.Config n) : (configEquiv B hB I).val.card=I.val.card := by
  have hh := positions_card (mutableSet n I.val)
  rw [positions_mutable I.property] at hh
  exact hh.symm

theorem positions_erase (J : Finset (Fin n)) (i : Fin n) :
    positions (J.erase i)=(positions J).erase (i.val+1) := by
  classical
  apply Finset.image_erase
  intro a b h
  exact Fin.ext (by dsimp at h;omega)

#print axioms positions
#print axioms mem_positions
#print axioms mutable_positions
#print axioms positions_mutable
#print axioms admissible
#print axioms configEquiv
#print axioms positions_card
#print axioms config_card
#print axioms positions_erase
end Verification.PathOriginalConfigurationIndex
