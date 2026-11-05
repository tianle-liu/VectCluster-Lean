/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathRecursiveFaces
import Verification.PathClosedBasisRecursion

/-!
# Path Closed Embedding

The actual closed-stratum summand of the full path module, including
mutually inverse restriction and extension on its specified support.
-/

namespace Verification.PathClosedEmbedding

open Classical Verification.PathCompression Verification.PathCochains
  Verification.PathRhoFinite Verification.PathConfigRecursion Verification.PathClosedBasisRecursion

variable {R : Type*} [CommRing R]

theorem closedUp_length (n : ℕ) (I : Config n) :
    (available (closedUp n I).val.val (n+2+2)).card=(available I.val (n+2)).card := by
  have hh := closed_free_count n (closedUp n I)
  change (available (closedUp n I).val.val (n+2+2)).card=
    (available ((closedEquiv n) ((closedEquiv n).symm I)).val (n+2)).card at hh
  simpa only [Equiv.apply_symm_apply] using hh

noncomputable def restriction (n : ℕ) : Total (R := R) (n+2) →ₗ[R] Total (R := R) n :=
  LinearMap.pi (fun I => LinearMap.codRestrict _
    ((layer (available (closedUp n I).val.val (n+2+2)).card).subtype.comp
      (LinearMap.proj (closedUp n I).val)) (fun x => by
        simpa only [closedUp_length] using (x (closedUp n I).val).property))

noncomputable def extension (n : ℕ) : Total (R := R) n →ₗ[R] Total (R := R) (n+2) :=
  LinearMap.pi (fun I => if h : 1 ∈ I.val then
    LinearMap.codRestrict _
      ((layer (available (closedDown n ⟨I,h⟩).val (n+2)).card).subtype.comp
        (LinearMap.proj (closedDown n ⟨I,h⟩))) (fun x => by
          rw [closed_free_count n ⟨I,h⟩]
          exact (x (closedDown n ⟨I,h⟩)).property)
    else 0)

theorem restriction_apply (n : ℕ) (x : Total (R := R) (n+2)) (I : Config n) :
    ((restriction n x) I).val=(x (closedUp n I).val).val := rfl

theorem extension_closed (n : ℕ) (x : Total (R := R) n) (I : ClosedConfig n) :
    ((extension n x) I.val).val=(x (closedDown n I)).val := by
  simp only [extension,LinearMap.pi_apply,I.property,↓reduceDIte,
    LinearMap.codRestrict_apply,LinearMap.comp_apply,LinearMap.proj_apply,Submodule.subtype_apply]

theorem extension_open (n : ℕ) (x : Total (R := R) n) (I : Config (n+2)) (hI : 1 ∉ I.val) :
    (extension n x) I=0 := by
  simp only [extension,LinearMap.pi_apply,hI,↓reduceDIte,LinearMap.zero_apply]

theorem restriction_extension (n : ℕ) :
    (restriction (R := R) n).comp (extension n)=LinearMap.id := by
  apply LinearMap.ext
  intro x
  funext I
  apply Subtype.ext
  rw [LinearMap.comp_apply,restriction_apply,extension_closed]
  have he : closedDown n (closedUp n I)=I := (closedEquiv n).apply_symm_apply I
  rw [he]
  rfl

theorem extension_restriction (n : ℕ) (x : Total (R := R) (n+2))
    (hx : ∀ I, 1 ∉ I.val → x I=0) : extension n (restriction n x)=x := by
  funext I
  by_cases hI : 1 ∈ I.val
  · apply Subtype.ext
    rw [extension_closed n _ ⟨I,hI⟩,restriction_apply]
    have he : (closedUp n (closedDown n ⟨I,hI⟩)).val=I :=
      congrArg Subtype.val ((closedEquiv n).symm_apply_apply ⟨I,hI⟩)
    rw [he]
  · rw [extension_open n _ I hI,hx I hI]

theorem extension_injective (n : ℕ) : Function.Injective (extension (R := R) n) := by
  intro x y h
  have hh := congrArg (restriction n) h
  have hf (z : Total (R := R) n) : restriction n (extension n z)=z :=
    LinearMap.congr_fun (restriction_extension n) z
  rw [hf,hf] at hh
  exact hh

noncomputable def closedSupport (n : ℕ) : Submodule R (Total (R := R) (n+2)) :=
  LinearMap.range (extension n)

theorem mem_closedSupport (n : ℕ) (x : Total (R := R) (n+2)) :
    x ∈ closedSupport n ↔ ∀ I, 1 ∉ I.val → x I=0 := by
  constructor
  · rintro ⟨y,rfl⟩ I hI
    exact extension_open n y I hI
  · intro hx
    exact ⟨restriction n x,extension_restriction n x hx⟩

#print axioms closedUp_length
#print axioms restriction
#print axioms extension
#print axioms restriction_apply
#print axioms extension_closed
#print axioms extension_open
#print axioms restriction_extension
#print axioms extension_restriction
#print axioms extension_injective
#print axioms closedSupport
#print axioms mem_closedSupport

end Verification.PathClosedEmbedding
