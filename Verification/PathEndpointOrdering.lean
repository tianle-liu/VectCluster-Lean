/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathClassOrdering
import Verification.PathEvenEndpointTorus
import Verification.PathVariableEndpointTorus

/-!
# Path Endpoint Ordering

The endpoint classes are literally the first and last surviving path
classes, including when repeated neighbor merges move the right endpoint.
-/
namespace Verification.PathEndpointOrdering
open Finset Verification.PathCompression Verification.PathClassRepresentatives
open Verification.PathClassOrdering Verification.PathSignedStratumCoefficients
variable {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)

theorem first_index : (index (compress hI (firstVertex hI))).val=0 := by
  change coordinate I 0=0
  simp [coordinate,available]

theorem last_index : (index (compress hI (lastVertex hI))).val+1=(available I (n+2)).card := by
  have h := index_compress hI (lastVertex hI)
  exact h

theorem first_le (p : Representatives n I) : compress hI (firstVertex hI)≤p := by
  change 0≤p.val
  exact Nat.zero_le _

theorem le_last (p : Representatives n I) : p≤compress hI (lastVertex hI) := by
  apply (orderIso (n:=n) (I:=I)).le_iff_le.mp
  change (index p).val≤(index (compress hI (lastVertex hI))).val
  have hl:=last_index hI
  have hp:=(index p).isLt
  omega

theorem right_free_index (p : PathVariableEndpointMaps.FreeCoordinates hI) :
    (index p.val).val+1<(available I (n+2)).card := by
  have hp : p.val<compress hI (lastVertex hI) := lt_of_le_of_ne (le_last hI p.val) p.property
  have h:=index_strictMono hp
  have hl:=last_index hI
  change (index p.val).val<(index (compress hI (lastVertex hI))).val at h
  omega

variable {a : ℕ} (hY : Admissible (2*a) I)

theorem both_free_indices (p : PathEvenEndpointTorus.FreeCoordinates hY) :
    0<(index p.val).val ∧ (index p.val).val+1<(available I (2*a+2)).card := by
  have hn₀ : p.val≠compress hY (firstVertex hY) := by
    intro he
    exact p.property ⟨false,he.symm⟩
  have hn₁ : p.val≠compress hY (lastVertex hY) := by
    intro he
    exact p.property ⟨true,he.symm⟩
  have h₀ := index_strictMono (lt_of_le_of_ne (first_le hY p.val) hn₀.symm)
  have h₁ := index_strictMono (lt_of_le_of_ne (le_last hY p.val) hn₁)
  change (index (compress hY (firstVertex hY))).val<(index p.val).val at h₀
  change (index p.val).val<(index (compress hY (lastVertex hY))).val at h₁
  rw [first_index] at h₀
  have hl:=last_index hY
  exact ⟨h₀,by omega⟩

#print axioms first_index
#print axioms last_index
#print axioms first_le
#print axioms le_last
#print axioms right_free_index
#print axioms both_free_indices
end Verification.PathEndpointOrdering
