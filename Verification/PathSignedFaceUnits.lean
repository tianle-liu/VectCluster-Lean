/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathSignedStratumCoefficients
import Verification.LaurentPolynomialUniversal

/-!
# Path Signed Face Units

The signed Laurent face on the actual surviving path coordinates:
the new normal is u and both its neighbors are the common new class.
-/
noncomputable section
namespace Verification.PathSignedFaceUnits
open Verification.PathCompression Verification.PathClassRepresentatives
open Verification.PathSignedStratumCoefficients Verification.LaurentPolynomialUniversal
open Finset
variable (R : Type) [CommRing R] {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)
variable (a b : R) (j : ℕ) (hj : j ∈ Icc 1 n) (ha : Addable I j)

def nextAdmissible : Admissible n (insert j I) := admissible_insert hI j hj ha
abbrev NextCoefficients := Coefficients R (nextAdmissible hI j hj ha) a b
abbrev FaceLaurent := Laurent (NextCoefficients R hI a b j hj ha)

def remainingVertex (p : Vertices n I) (hp : p.val≠j) : Vertices n (insert j I) :=
  ⟨p.val,mem_sdiff.mpr ⟨(mem_sdiff.mp p.property).1,
    fun hm => (mem_insert.mp hm).elim hp (mem_sdiff.mp p.property).2⟩⟩

def faceUnit (p : Vertices n I) : (FaceLaurent R hI a b j hj ha)ˣ :=
  if hp : p.val=j then parameterUnit _ else
    Units.map (algebraMap (NextCoefficients R hI a b j hj ha) _).toMonoidHom
      (signedCoordinate R (nextAdmissible hI j hj ha) a b (remainingVertex j p hp))

include ha in
theorem left_ne_normal (i : I) : (leftVertex hI i).val≠j := by
  intro he
  have hp:=(mem_Icc.mp (hI.1 i.property)).1
  have hv : i.val=j+1 := by change i.val-1=j at he;omega
  exact ha.2 (mem_union_left _ (hv ▸ i.property))

include ha in
theorem right_ne_normal (i : I) : (rightVertex hI i).val≠j := by
  intro he
  exact ha.1 (mem_union_right _ (mem_image.mpr ⟨i.val,i.property,he⟩))

theorem faceUnit_neighbors (i : I) :
    faceUnit R hI a b j hj ha (rightVertex hI i)=faceUnit R hI a b j hj ha (leftVertex hI i) := by
  rw [faceUnit,dif_neg (right_ne_normal hI j ha i),faceUnit,dif_neg (left_ne_normal hI j ha i)]
  apply congrArg
  unfold signedCoordinate
  apply congrArg
  apply congrArg
  have hr : remainingVertex j (rightVertex hI i) (right_ne_normal hI j ha i)=
      rightVertex (nextAdmissible hI j hj ha) ⟨i.val,mem_insert_of_mem i.property⟩ := by
    apply Subtype.ext
    rfl
  have hl : remainingVertex j (leftVertex hI i) (left_ne_normal hI j ha i)=
      leftVertex (nextAdmissible hI j hj ha) ⟨i.val,mem_insert_of_mem i.property⟩ := by
    apply Subtype.ext
    rfl
  rw [hr,hl,compress_neighbors]

theorem faceUnit_compression (p : Vertices n I) :
    faceUnit R hI a b j hj ha (includeRepresentative (compress hI p))=faceUnit R hI a b j hj ha p :=
  vertex_evaluate hI (faceUnit R hI a b j hj ha) (faceUnit_neighbors R hI a b j hj ha) p

def normalVertex : Vertices n I :=
  ⟨j,mem_sdiff.mpr ⟨mem_range.mpr (by have hh:=mem_Icc.mp hj;omega),
    fun hm => ha.1 (mem_union_left _ hm)⟩⟩

theorem faceUnit_normal : faceUnit R hI a b j hj ha (normalVertex j hj ha)=parameterUnit _ := by
  simp [faceUnit,normalVertex]

include hj in
theorem first_ne_normal : (firstVertex hI).val≠j := by
  change 0≠j
  have hh:=mem_Icc.mp hj
  omega

include hj in
theorem last_ne_normal : (lastVertex hI).val≠j := by
  change n+1≠j
  have hh:=mem_Icc.mp hj
  omega

theorem faceUnit_endpoint (e : Bool) :
    (faceUnit R hI a b j hj ha (endpoint hI e) : FaceLaurent R hI a b j hj ha)=
      algebraMap R _ (endpointValue R (n:=n) a b e) := by
  have hn : (endpoint hI e).val≠j := by
    cases e
    · exact first_ne_normal hI j hj
    · exact last_ne_normal hI j hj
  rw [faceUnit,dif_neg hn]
  change algebraMap (NextCoefficients R hI a b j hj ha) _
    (signedCoordinate R (nextAdmissible hI j hj ha) a b (remainingVertex j (endpoint hI e) hn) : NextCoefficients R hI a b j hj ha)=_
  have he : remainingVertex j (endpoint hI e) hn=endpoint (nextAdmissible hI j hj ha) e := by
    apply Subtype.ext
    cases e <;> rfl
  rw [he,signed_endpoint]
  rfl

#print axioms nextAdmissible
#print axioms NextCoefficients
#print axioms FaceLaurent
#print axioms remainingVertex
#print axioms faceUnit
#print axioms left_ne_normal
#print axioms right_ne_normal
#print axioms faceUnit_neighbors
#print axioms faceUnit_compression
#print axioms normalVertex
#print axioms faceUnit_normal
#print axioms first_ne_normal
#print axioms last_ne_normal
#print axioms faceUnit_endpoint
end Verification.PathSignedFaceUnits
