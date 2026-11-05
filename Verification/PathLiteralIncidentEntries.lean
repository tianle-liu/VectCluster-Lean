/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathLiteralEntries
import Verification.PathConfigurationIncidence

/-!
# Path Literal Incident Entries

Incident literal path-matrix entries reduce to their unique face, while nonincident configuration blocks vanish.
-/
noncomputable section
namespace Verification.PathLiteralIncidentEntries
open Classical Finset Verification.PathCompression Verification.PathCochains Verification.PathRhoConfiguration
open Verification.PathEndpointCoordinates Verification.PathNormalizedBasis Verification.PathEndpointWords
variable {R : Type*} [CommRing R]

theorem erase_insert_config {n : ℕ} (I : Config n) (j : ℕ) (hj : j∉I.val)
    (hJ : Admissible n (insert j I.val)) : eraseConfig ⟨insert j I.val,hJ⟩ j=I :=
  Subtype.ext (Finset.erase_insert hj)

theorem erase_insert_other {n : ℕ} (I : Config n) (j : ℕ) (hj : j∉I.val)
    (hJ : Admissible n (insert j I.val)) (k : ℕ) (hk : k∈insert j I.val) (hkj : k≠j) :
    eraseConfig ⟨insert j I.val,hJ⟩ k≠I := by
  intro h
  apply hkj
  apply PathConfigurationIncidence.erase_unique (insert j I.val) k j hk
  exact (congrArg Subtype.val h).trans (Finset.erase_insert hj).symm

theorem z_insert (g ρ : R) (n : ℕ) (I : Config (n)) (j : ℕ) (hj : j∉I.val)
    (hJ : Admissible (n) (insert j I.val))
    (s : NormalWord RightNormal (available I.val ((n)+2)).card)
    (t : NormalWord RightNormal (available (insert j I.val) ((n)+2)).card) :
    zMatrix g ρ n ⟨⟨insert j I.val,hJ⟩,t⟩ ⟨I,s⟩=
    incidence g I.val j * PathLiteralEntries.projectedFace g ρ (n) (faceIndex I.val j) s.val t.val := by
  rw [PathLiteralEntries.z_entry]
  rw [Finset.sum_eq_single j]
  · rw [if_pos (erase_insert_config I j hj hJ)]
    rw [erase_insert_config I j hj hJ]
  · intro k hk hkj
    exact if_neg (erase_insert_other I j hj hJ k hk hkj)
  · simp

theorem z_nonincident (g ρ : R) (n : ℕ) (y x : NormalIndex RightNormal (n)) (h : ¬x.1.val⊆y.1.val) :
    zMatrix g ρ n y x=0 := by
  rw [PathLiteralEntries.z_entry]
  apply Finset.sum_eq_zero
  intro j hj
  apply if_neg
  intro he
  apply h
  have hh : (eraseConfig y.1 j).val⊆y.1.val := Finset.erase_subset j y.1.val
  simpa only [he] using hh

#print axioms z_insert
#print axioms z_nonincident

theorem y_insert (g ρ : R) (a : ℕ) (I : Config (2*a)) (j : ℕ) (hj : j∉I.val)
    (hJ : Admissible (2*a) (insert j I.val))
    (s : NormalWord BothNormal (available I.val ((2*a)+2)).card)
    (t : NormalWord BothNormal (available (insert j I.val) ((2*a)+2)).card) :
    yMatrix g ρ a ⟨⟨insert j I.val,hJ⟩,t⟩ ⟨I,s⟩=
    incidence g I.val j * (PathLeftEndpoint.projection 0 (PathLiteralEntries.projectedFace g ρ (2*a) (faceIndex I.val j) s.val)) t.val := by
  rw [PathLiteralEntries.y_entry]
  rw [Finset.sum_eq_single j]
  · rw [if_pos (erase_insert_config I j hj hJ)]
    rw [erase_insert_config I j hj hJ]
  · intro k hk hkj
    exact if_neg (erase_insert_other I j hj hJ k hk hkj)
  · simp

theorem y_nonincident (g ρ : R) (a : ℕ) (y x : NormalIndex BothNormal (2*a)) (h : ¬x.1.val⊆y.1.val) :
    yMatrix g ρ a y x=0 := by
  rw [PathLiteralEntries.y_entry]
  apply Finset.sum_eq_zero
  intro j hj
  apply if_neg
  intro he
  apply h
  have hh : (eraseConfig y.1 j).val⊆y.1.val := Finset.erase_subset j y.1.val
  simpa only [he] using hh

#print axioms y_insert
#print axioms y_nonincident

#print axioms erase_insert_config
#print axioms erase_insert_other
end Verification.PathLiteralIncidentEntries
