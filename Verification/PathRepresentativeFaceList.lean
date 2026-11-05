/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathClassOrdering
import Verification.PathSignedFaceUnits
import Verification.PathFaceVertexTransport
import Mathlib.Data.Finset.Sort

/-!
# Path Representative Face List

The actual increasing surviving-coordinate list loses exactly the normal
and its right copy. Its three consecutive face positions are derived from
the path zero-set, not supplied as a word-coordinate compatibility.
-/
noncomputable section
namespace Verification.PathRepresentativeFaceList
open Finset Verification.PathCompression Verification.PathClassRepresentatives
open Verification.PathClassOrdering Verification.PathSignedFaceUnits
open Verification.PathFaceVertexTransport

def representatives (n : ℕ) (I : Finset ℕ) : List ℕ := (available I (n+2)).sort (·≤·)

theorem length_representatives (n : ℕ) (I : Finset ℕ) :
    (representatives n I).length=(available I (n+2)).card := Finset.length_sort _

theorem get_index {n : ℕ} {I : Finset ℕ} (p : Representatives n I) :
    (representatives n I)[(index p).val]'(by rw [length_representatives];exact (index p).isLt)=p.val := by
  have he : (available I (n+2)).orderIsoOfFin rfl=(orderIso (n:=n) (I:=I)).symm :=
    Subsingleton.elim _ _
  have hh := congrArg Subtype.val (congrFun (congrArg DFunLike.coe he) (index p))
  change (available I (n+2)).orderEmbOfFin rfl (index p)=_ at hh
  rw [Finset.orderEmbOfFin_apply] at hh
  exact hh.trans (congrArg Subtype.val (orderIso.symm_apply_apply p))

theorem sort_erase (s : Finset ℕ) (a : ℕ) :
    (s.erase a).sort (·≤·)=(s.sort (·≤·)).erase a := by
  have hn := Finset.sort_nodup (·≤·) s
  have he : ((s.sort (·≤·)).erase a).toFinset=s.erase a := by
    ext x
    simp only [List.mem_toFinset,hn.mem_erase_iff,Finset.mem_sort,Finset.mem_erase]
  rw [←he]
  exact (List.toFinset_sort (·≤·) (hn.erase a)).mpr
    ((Finset.sort_sorted (·≤·) s).erase a)

theorem representatives_insert (n : ℕ) (I : Finset ℕ) (j : ℕ) :
    representatives n (insert j I)=((representatives n I).erase j).erase (j+1) := by
  simp only [representatives,available_insert,sort_erase]

theorem split_three {α : Type*} (xs : List α) (k : ℕ) (hk : k+3≤xs.length) :
    xs=xs.take k ++ xs[k]::xs[k+1]::xs[k+2]::xs.drop (k+3) := by
  conv_lhs => rw [← List.take_append_drop k xs]
  rw [List.drop_eq_getElem_cons (by omega : k<xs.length),
    List.drop_eq_getElem_cons (by omega : k+1<xs.length),
    List.drop_eq_getElem_cons (by omega : k+2<xs.length)]

variable {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)
variable (j : ℕ) (hj : j∈Icc 1 n) (ha : Addable I j)

include hI hj ha in
/-- Literal sorted representatives, including possible previously merged left
neighbors, have the exact three slots used by the rho face. -/
theorem source_split :
    representatives n I=(representatives n I).take (faceIndex I j) ++
      representative I (j-1)::j::(j+1)::(representatives n I).drop (faceIndex I j+3) := by
  let hJ := nextAdmissible hI j hj ha
  let l : Vertices n I := oldVertex j (leftVertex hJ ⟨j,mem_insert_self j I⟩)
  let r : Vertices n I := oldVertex j (rightVertex hJ ⟨j,mem_insert_self j I⟩)
  have hl := get_index (compress hI l)
  have hm := get_index (compress hI (normalVertex j hj ha))
  have hr := get_index (compress hI r)
  have hli := index_left hI j hj l rfl
  have hmi := index_normal hI j hj ha (normalVertex j hj ha) rfl
  have hri := index_right hI j hj ha r rfl
  have hmv : (compress hI (normalVertex j hj ha)).val=j := representative_fixed I ha.1
  have hrv : (compress hI r).val=j+1 := representative_fixed I ha.2
  simp only [hli] at hl
  simp only [hmi,hmv] at hm
  simp only [hri,hrv] at hr
  have hv := faceIndex_valid hI j hj ha
  rw [←length_representatives] at hv
  calc
    _ = _ := split_three (representatives n I) (faceIndex I j) hv
    _ = _ := by rw [hl,hm,hr];rfl

include hI hj ha in
theorem target_split :
    representatives n (insert j I)=(representatives n I).take (faceIndex I j) ++
      representative I (j-1)::(representatives n I).drop (faceIndex I j+3) := by
  have hn := Finset.sort_nodup (·≤·) (available I (n+2))
  change (representatives n I).Nodup at hn
  rw [source_split hI j hj ha] at hn
  have hd := (List.nodup_append.mp hn).2.2
  have hm : j ∉ (representatives n I).take (faceIndex I j) := by
    intro hh
    exact List.disjoint_left.mp hd hh (by simp)
  have hr : j+1 ∉ (representatives n I).take (faceIndex I j) := by
    intro hh
    exact List.disjoint_left.mp hd hh (by simp)
  have hlt : representative I (j-1)<j := by
    have hh:=representative_le I (j-1)
    have hp:=(mem_Icc.mp hj).1
    omega
  rw [representatives_insert]
  conv_lhs => rw [source_split hI j hj ha]
  rw [List.erase_append_right _ hm,List.erase_cons_tail (by simp;omega),List.erase_cons_head,
    List.erase_append_right _ hr,List.erase_cons_tail (by simp;omega),List.erase_cons_head]

#print axioms target_split
#print axioms representatives
#print axioms length_representatives
#print axioms get_index
#print axioms sort_erase
#print axioms representatives_insert
#print axioms split_three
#print axioms source_split
end Verification.PathRepresentativeFaceList
