/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOpenWords
import Verification.PathOpenBasisRecursion

/-!
# Path Open Embedding

Actual restriction to the open strata and its two free-coordinate summands.
The kernel is the closed-stratum submodule, so this is a literal open quotient.
-/

namespace Verification.PathOpenEmbedding

open Classical Verification.PathCompression Verification.PathCochains
  Verification.PathRhoWords Verification.PathRhoFinite Verification.PathConfigRecursion
  Verification.PathOpenBasisRecursion Verification.PathOpenWords

variable {R : Type*} [CommRing R]

theorem openUp_length (n : ℕ) (I : Config n) :
    (available (openUp n I).val.val (n+1+2)).card=(available I.val (n+2)).card+1 := by
  have hh := open_free_count n (openUp n I)
  change (available (openUp n I).val.val (n+1+2)).card=
    (available ((openEquiv n) ((openEquiv n).symm I)).val (n+2)).card+1 at hh
  simpa only [Equiv.apply_symm_apply] using hh

noncomputable def restriction (n : ℕ) (bit : Bool) :
    Total (R := R) (n+1) →ₗ[R] Total (R := R) n :=
  LinearMap.pi (fun I => LinearMap.codRestrict _
    ((unprepend bit).comp ((layer _).subtype.comp (LinearMap.proj (openUp n I).val)))
    (fun x => unprepend_mem_layer _ bit _ (by
      rw [← openUp_length n I]
      exact (x (openUp n I).val).property)))

noncomputable def extension (n : ℕ) (bit : Bool) :
    Total (R := R) n →ₗ[R] Total (R := R) (n+1) :=
  LinearMap.pi (fun I => if h : 1 ∉ I.val then
    LinearMap.codRestrict _
      ((prepend bit).comp ((layer _).subtype.comp (LinearMap.proj (openDown n ⟨I,h⟩))))
      (fun x => by
        rw [open_free_count n ⟨I,h⟩]
        exact prepend_mem_layer _ bit _ (x (openDown n ⟨I,h⟩)).property)
    else 0)

theorem restriction_apply (n : ℕ) (bit : Bool) (x : Total (R := R) (n+1)) (I : Config n) :
    ((restriction n bit x) I).val=unprepend bit (x (openUp n I).val).val := rfl

theorem extension_open (n : ℕ) (bit : Bool) (x : Total (R := R) n) (I : OpenConfig n) :
    ((extension n bit x) I.val).val=prepend bit (x (openDown n I)).val := by
  simp only [extension,LinearMap.pi_apply,I.property,not_false_eq_true,↓reduceDIte,LinearMap.codRestrict_apply,
    LinearMap.comp_apply,Submodule.subtype_apply,LinearMap.proj_apply]

theorem extension_closed (n : ℕ) (bit : Bool) (x : Total (R := R) n)
    (I : Config (n+1)) (hI : 1 ∈ I.val) : (extension n bit x) I=0 := by
  simp only [extension,LinearMap.pi_apply,hI,not_true_eq_false,↓reduceDIte,LinearMap.zero_apply]

theorem restriction_extension (n : ℕ) (a b : Bool) (x : Total (R := R) n) :
    restriction n a (extension n b x)=if a=b then x else 0 := by
  funext I
  apply Subtype.ext
  rw [restriction_apply,extension_open]
  have he : openDown n (openUp n I)=I := (openEquiv n).apply_symm_apply I
  rw [he,unprepend_prepend]
  split <;> rfl

noncomputable def projection (n : ℕ) :
    Total (R := R) (n+1) →ₗ[R] (Bool → Total (R := R) n) :=
  LinearMap.pi (restriction n)

noncomputable def sectionMap (n : ℕ) :
    (Bool → Total (R := R) n) →ₗ[R] Total (R := R) (n+1) :=
  (extension n false).comp (LinearMap.proj false)+(extension n true).comp (LinearMap.proj true)

theorem projection_section (n : ℕ) :
    (projection (R := R) n).comp (sectionMap n)=LinearMap.id := by
  apply LinearMap.ext
  intro x
  funext bit
  change restriction n bit (extension n false (x false)+extension n true (x true))=x bit
  rw [map_add,restriction_extension,restriction_extension]
  cases bit <;> simp

theorem section_projection_open (n : ℕ) (x : Total (R := R) (n+1)) (I : OpenConfig n) :
    (sectionMap n (projection n x)) I.val=x I.val := by
  apply Subtype.ext
  change ((extension n false (restriction n false x)) I.val).val+
    ((extension n true (restriction n true x)) I.val).val=_
  rw [extension_open,extension_open,restriction_apply,restriction_apply]
  have he : (openUp n (openDown n I)).val=I.val :=
    congrArg Subtype.val ((openEquiv n).symm_apply_apply I)
  rw [he]
  apply split_word
  exact (Finsupp.mem_supported' R _).mp (x I.val).property [] (by
    change ([] : List Bool).length ≠ (available I.val.val (n+1+2)).card
    rw [open_free_count n I]
    simp)

theorem projection_surjective (n : ℕ) : Function.Surjective (projection (R := R) n) := by
  intro x
  exact ⟨sectionMap n x,LinearMap.congr_fun (projection_section n) x⟩

theorem projection_zero_iff (n : ℕ) (x : Total (R := R) (n+1)) :
    projection n x=0 ↔ ∀ I : Config (n+1), 1 ∉ I.val → x I=0 := by
  constructor
  · intro hx I hI
    have hh := section_projection_open n x ⟨I,hI⟩
    rw [hx,map_zero] at hh
    exact hh.symm
  · intro hx
    ext bit I w
    change unprepend bit (x (openUp n I).val).val w=0
    rw [hx (openUp n I).val (openUp n I).property]
    rfl

/-- The actual quotient by closed support is the two-coordinate shorter module. -/
noncomputable def quotientEquiv (n : ℕ) :
    (Total (R := R) (n+1) ⧸ LinearMap.ker (projection n)) ≃ₗ[R] (Bool → Total (R := R) n) :=
  LinearMap.quotKerEquivOfSurjective (projection n) (projection_surjective n)

#print axioms openUp_length
#print axioms restriction
#print axioms extension
#print axioms restriction_apply
#print axioms extension_open
#print axioms extension_closed
#print axioms restriction_extension
#print axioms projection
#print axioms sectionMap
#print axioms projection_section
#print axioms section_projection_open
#print axioms projection_surjective
#print axioms projection_zero_iff
#print axioms quotientEquiv

end Verification.PathOpenEmbedding
