/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathRecursiveCoordinates
import Verification.PathGlobalAffineSigns

/-!
# Path Recursive Faces

Literal recursive comparisons of every full-rho path face. The extra
closed-stratum incidence is computed from the original zero set.
-/

namespace Verification.PathRecursiveFaces

open Classical Verification.PathCompression Verification.PathRhoConfiguration
  Verification.PathRhoWords Verification.PathRhoFaces Verification.PathRhoFinite
  Verification.PathConfigRecursion Verification.PathRecursiveCoordinates
  Verification.PathAffineSigns Verification.PathSignCompression Verification.PathGlobalAffineSigns

variable {R : Type*} [CommRing R] (g ρ : R)

theorem open_incidence (I : Finset ℕ) (j : ℕ) :
    incidence g (shift 1 I) (j+1)=incidence g I j := by
  rw [incidence,rank_shift]
  rfl

theorem closed_incidence (I : Finset ℕ) (j : ℕ) :
    incidence g (insert 1 (shift 2 I)) (j+2)=g*incidence g I j := by
  rw [incidence,closed_rank,pow_succ,incidence,mul_comm]

/-- The original open face includes exactly the preceding free torus symbol. -/
theorem open_face {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)
    (j : ℕ) (hpos : 0<j) (hj : Addable I j) (bit : Bool) (x : List Bool →₀ R) :
    faceMap g ρ (shift 1 I) (j+1) (prepend bit x)=
      phase (-g) bit • prepend bit (faceMap g ρ I j x) := by
  simp only [faceMap,LinearMap.smul_apply,open_incidence,
    open_faceIndex hI j hpos hj,face_prepend,map_smul,smul_smul,mul_comm]

/-- The closed diagonal before coordinate normalization is exactly g times the shorter face. -/
theorem closed_face {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)
    (j : ℕ) (hpos : 0<j) (hj : Addable I j) :
    faceMap g ρ (insert 1 (shift 2 I)) (j+2)=g • faceMap g ρ I j := by
  rw [faceMap,faceMap,closed_incidence,closed_faceIndex hI j hpos hj,smul_smul]

/-- The Thom incidence adds one g per shorter zero, in addition to its affine normal sign. -/
def closedFactor (a b : Bool) (I : Finset ℕ) : R :=
  g^I.card*stratumFactor g a b I

theorem closedFactor_insert (a b : Bool) (I : Finset ℕ) (j : ℕ) (hj : j ∉ I) :
    closedFactor g a b (insert j I)=g*vertexFactor g a b j*closedFactor g a b I := by
  rw [closedFactor,Finset.card_insert_of_not_mem hj,pow_succ,stratumFactor_insert g a b I j hj]
  unfold closedFactor
  ring

theorem closedFactor_squared (hg : g*g=1) (a b : Bool) (I : Finset ℕ) :
    closedFactor g a b I*closedFactor g a b I=1 := by
  calc
    _=(g*g)^I.card*(stratumFactor g a b I*stratumFactor g a b I) := by
      rw [mul_pow]
      unfold closedFactor
      ring
    _=1 := by rw [hg,one_pow,stratumFactor_squared g hg,one_mul]

/-- All-coordinate signs on the closed Z layer need no remaining stratum scalar. -/
theorem closedFactor_all (hg : g*g=1) (I : Finset ℕ) :
    closedFactor g true true I=1 := by
  have hs : stratumFactor g true true I=g^I.card := by
    simp [stratumFactor,vertexFactor]
  rw [closedFactor,hs,← mul_pow,hg,one_pow]

/-- The complete closed face comparison, with every rho term and normal orientation retained. -/
theorem closed_signed_face (hg : g*g=1) (hr : (1+g)*ρ=0) (a b : Bool)
    {n : ℕ} {I : Finset ℕ} (hI : Admissible n I) (j : ℕ)
    (hj : j ∈ Finset.Icc 1 n) (ha : Addable I j)
    (x : layer (R := R) (available I (n+2)).card) :
    faceMap g ρ (insert 1 (shift 2 I)) (j+2)
      (closedFactor g a b I • signMap g ρ a b x.val)=
        closedFactor g a b (insert j I) • signMap g ρ a b (faceMap g ρ I j x.val) := by
  have hn : j ∉ I := fun hm => ha.1 (Finset.mem_union_left _ hm)
  rw [closed_face g ρ hI j (Finset.mem_Icc.mp hj).1 ha]
  change g • faceMap g ρ I j (closedFactor g a b I • signMap g ρ a b x.val)=_
  rw [closedFactor,mul_smul,map_smul,faceMap_sign g ρ hg hr a b hI j hj ha]
  rw [closedFactor,Finset.card_insert_of_not_mem hn,pow_succ]
  simp only [smul_smul]
  congr 1
  ring

#print axioms open_incidence
#print axioms closed_incidence
#print axioms open_face
#print axioms closed_face
#print axioms closedFactor
#print axioms closedFactor_insert
#print axioms closedFactor_squared
#print axioms closedFactor_all
#print axioms closed_signed_face

end Verification.PathRecursiveFaces
