/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathRepresentativeFaceList

/-!
# Path Ordered Face Units

Ordered actual coefficient units and their exact signed Laurent face.
The total numeric accessor is used only on the verified surviving lists.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.PathOrderedFaceUnits
open Finset Verification.PathCompression Verification.PathClassRepresentatives
open Verification.PathSignedStratumCoefficients Verification.PathSignedFaceUnits
open Verification.PathFaceVertexTransport Verification.PathRepresentativeFaceList

theorem representative_insert_before (I : Finset ℕ) (j p : ℕ) (hp : p<j) :
    representative (insert j I) p=representative I p := by
  induction p using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more p ih _ =>
    simp only [representative,mem_insert]
    have hn : p+1≠j := by omega
    simp only [hn,false_or]
    split_ifs
    · exact ih (by omega)
    · rfl

variable (S : Type) [CommRing S] {n : ℕ} {I : Finset ℕ} (hI : Admissible n I) (a b : S)

def unitAt (p : ℕ) : (Coefficients S hI a b)ˣ :=
  if hp : p∈range (n+2) \ I then signedCoordinate S hI a b ⟨p,hp⟩ else 1

theorem unitAt_vertex (p : Vertices n I) : unitAt S hI a b p.val=signedCoordinate S hI a b p := by
  rw [unitAt,dif_pos p.property]
  congr 1

theorem unitAt_representative (p : Vertices n I) :
    unitAt S hI a b (representative I p.val)=signedCoordinate S hI a b p := by
  have hh := unitAt_vertex S hI a b (includeRepresentative (compress hI p))
  change unitAt S hI a b (representative I p.val)=_ at hh
  rw [hh]
  unfold signedCoordinate
  rw [compress_include]

def units : List (Coefficients S hI a b)ˣ := (representatives n I).map (unitAt S hI a b)

variable (R : Type) [CommRing R] [Algebra R S]
variable (j : ℕ) (hj : j∈Icc 1 n) (ha : Addable I j) (w : ℕ)
local notation "hJ" => nextAdmissible hI j hj ha
local notation "New" => Coefficients S (nextAdmissible hI j hj ha) a b
local notation "φ" => Units.map (PathFaceVertexTransport.map R S hI a b j hj ha w).toRingHom.toMonoidHom
local notation "C" => Units.map (algebraMap New (LaurentPolynomialUniversal.Laurent New)).toMonoidHom

theorem remaining (p : ℕ) (hp : p∈representatives n (insert j I)) :
    φ (unitAt S hI a b p)=C (unitAt S hJ a b p) := by
  have hm : p∈available (insert j I) (n+2) := (Finset.mem_sort (·≤·)).mp hp
  let v := includeRepresentative (⟨p,hm⟩ : Representatives n (insert j I))
  have ho := unitAt_vertex S hI a b (oldVertex j v)
  have hn := unitAt_vertex S hJ a b v
  change unitAt S hI a b p=_ at ho
  change unitAt S hJ a b p=_ at hn
  rw [ho,hn]
  exact remaining_unit R S hI a b j hj ha w v

theorem normal : φ (unitAt S hI a b j)=(-1)^w*LaurentPolynomialUniversal.parameterUnit New := by
  have hh := unitAt_vertex S hI a b (normalVertex j hj ha)
  change unitAt S hI a b j=_ at hh
  rw [hh]
  exact normal_unit R S hI a b j hj ha w

theorem right : φ (unitAt S hI a b (j+1))=C (unitAt S hJ a b (representative I (j-1))) := by
  let l := leftVertex hJ ⟨j,mem_insert_self j I⟩
  let r := rightVertex hJ ⟨j,mem_insert_self j I⟩
  have ho := unitAt_vertex S hI a b (oldVertex j r)
  change unitAt S hI a b (j+1)=_ at ho
  have hn := unitAt_representative S hJ a b l
  change unitAt S hJ a b (representative (insert j I) (j-1))=_ at hn
  rw [representative_insert_before I j (j-1) (by have hh:=(mem_Icc.mp hj).1;omega)] at hn
  rw [ho,hn,remaining_unit R S hI a b j hj ha w r]
  exact congrArg C (neighbors S hI a b j hj ha)

include hj ha in
theorem target_units : units S hJ a b=
    ((representatives n I).take (faceIndex I j)).map (unitAt S hJ a b) ++
      unitAt S hJ a b (representative I (j-1)) ::
        ((representatives n I).drop (faceIndex I j+3)).map (unitAt S hJ a b) := by
  unfold units
  rw [target_split hI j hj ha,List.map_append,List.map_cons]

theorem source_units : (units S hI a b).map φ=
    (((representatives n I).take (faceIndex I j)).map (unitAt S hJ a b)).map C ++
      C (unitAt S hJ a b (representative I (j-1))) ::
        ((-1)^w*LaurentPolynomialUniversal.parameterUnit New) ::
          C (unitAt S hJ a b (representative I (j-1))) ::
            (((representatives n I).drop (faceIndex I j+3)).map (unitAt S hJ a b)).map C := by
  have hp : ∀p∈(representatives n I).take (faceIndex I j),p∈representatives n (insert j I) := by
    intro p hp
    rw [target_split hI j hj ha]
    exact List.mem_append_left _ hp
  have hs : ∀p∈(representatives n I).drop (faceIndex I j+3),p∈representatives n (insert j I) := by
    intro p hp
    rw [target_split hI j hj ha]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ hp)
  have hm : representative I (j-1)∈representatives n (insert j I) := by
    rw [target_split hI j hj ha]
    simp only [List.mem_append,List.mem_cons,true_or,or_true]
  have hl : (((representatives n I).take (faceIndex I j)).map (unitAt S hI a b)).map φ=
      (((representatives n I).take (faceIndex I j)).map (unitAt S hJ a b)).map C := by
    simp only [List.map_map]
    exact List.map_congr_left (fun p hh => remaining S hI a b R j hj ha w p (hp p hh))
  have hr : (((representatives n I).drop (faceIndex I j+3)).map (unitAt S hI a b)).map φ=
      (((representatives n I).drop (faceIndex I j+3)).map (unitAt S hJ a b)).map C := by
    simp only [List.map_map]
    exact List.map_congr_left (fun p hh => remaining S hI a b R j hj ha w p (hs p hh))
  unfold units
  conv_lhs => rw [source_split hI j hj ha]
  simp only [List.map_append,List.map_cons]
  rw [hl,hr,remaining S hI a b R j hj ha w _ hm,normal S hI a b R j hj ha w,right S hI a b R j hj ha w]

#print axioms target_units
#print axioms source_units
#print axioms representative_insert_before
#print axioms unitAt
#print axioms unitAt_vertex
#print axioms unitAt_representative
#print axioms units
#print axioms remaining
#print axioms normal
#print axioms right
end Verification.PathOrderedFaceUnits
