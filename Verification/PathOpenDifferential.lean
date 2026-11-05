/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOpenEmbedding
import Verification.PathClosedDifferential

/-!
# Path Open Differential

The full original differential on the open quotient, retaining the phase
of the free preceding coordinate and every rho term.
-/

namespace Verification.PathOpenDifferential

open Classical Verification.PathCompression Verification.PathCochains
  Verification.PathRhoWords Verification.PathRhoFaces Verification.PathRhoConfiguration
  Verification.PathConfigRecursion Verification.PathRecursiveCoordinates
  Verification.PathRecursiveFaces Verification.PathOpenWords Verification.PathOpenEmbedding
  Verification.PathClosedDifferential

variable {R : Type*} [CommRing R]

theorem openUp_erase (n : ℕ) (I : Config n) (j : ℕ) :
    eraseConfig (openUp n I).val (j+1)=(openUp n (eraseConfig I j)).val := by
  apply Subtype.ext
  exact shift_erase 1 I.val j

theorem unprepend_faceMap (g ρ : R) {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)
    (j : ℕ) (hpos : 0<j) (hj : Addable I j) (bit : Bool) (x : List Bool →₀ R) :
    unprepend bit (faceMap g ρ (shift 1 I) (j+1) x)=
      phase (-g) bit • faceMap g ρ I j (unprepend bit x) := by
  simp only [faceMap,LinearMap.smul_apply,map_smul,open_incidence,
    open_faceIndex hI j hpos hj,unprepend_face,smul_smul,mul_comm]

/-- Restriction computes the open diagonal, with no hypothesis on discarded closed values. -/
theorem restriction_differential (g ρ : R) (n : ℕ) (bit : Bool) :
    (restriction n bit).comp (differential g ρ (n+1))=
      phase (-g) bit • (differential g ρ n).comp (restriction n bit) := by
  apply LinearMap.ext
  intro x
  funext J
  apply Subtype.ext
  change unprepend bit (ambientDifferential g ρ (n+1) (inclusion (n+1) x) (openUp n J).val)=
    phase (-g) bit • ambientDifferential g ρ n (inclusion n (restriction n bit x)) J
  rw [ambientDifferential_apply,ambientDifferential_apply,map_sum,Finset.smul_sum]
  change (∑ j ∈ shift 1 J.val,unprepend bit (faceMap g ρ (eraseConfig (openUp n J).val j).val j
    (x (eraseConfig (openUp n J).val j)).val))=_
  unfold shift
  rw [Finset.sum_image (by intro i _ j _ he; exact Nat.add_right_cancel he)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [openUp_erase]
  have hi : insert j (eraseConfig J j).val=J.val := Finset.insert_erase hj
  have ha := addable_of_insert (hi.symm ▸ J.property) (Finset.not_mem_erase _ _)
  change unprepend bit (faceMap g ρ (shift 1 (eraseConfig J j).val) (j+1)
    (x (openUp n (eraseConfig J j)).val).val)=_
  rw [unprepend_faceMap g ρ (eraseConfig J j).property j (Finset.mem_Icc.mp (J.property.1 hj)).1 ha]
  rfl

noncomputable def openDifferential (g ρ : R) (n : ℕ) :
    (Bool → Total (R := R) n) →ₗ[R] (Bool → Total (R := R) n) :=
  LinearMap.pi (fun bit => phase (-g) bit • (differential g ρ n).comp (LinearMap.proj bit))

theorem projection_differential (g ρ : R) (n : ℕ) :
    (projection n).comp (differential g ρ (n+1))=
      (openDifferential g ρ n).comp (projection n) := by
  apply LinearMap.ext
  intro x
  funext bit
  exact LinearMap.congr_fun (restriction_differential g ρ n bit) x

theorem closed_kernel_preserved (g ρ : R) (n : ℕ) :
    LinearMap.ker (projection (R := R) n) ≤
      (LinearMap.ker (projection n)).comap (differential g ρ (n+1)) := by
  intro x hx
  change projection n (differential g ρ (n+1) x)=0
  have hh := LinearMap.congr_fun (projection_differential g ρ n) x
  change projection n (differential g ρ (n+1) x)=openDifferential g ρ n (projection n x) at hh
  rw [hh,LinearMap.mem_ker.mp hx,map_zero]

#print axioms openUp_erase
#print axioms unprepend_faceMap
#print axioms restriction_differential
#print axioms openDifferential
#print axioms projection_differential
#print axioms closed_kernel_preserved

end Verification.PathOpenDifferential
