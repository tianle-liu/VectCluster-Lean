/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOpenEmbedding
import Verification.PathClosedSignedComplex
import Verification.PathEndpointTotal

/-!
# Path Recursion Degree

The actual recursive word maps have their original cellular degree.
In particular the closed embedding carries the required degree-one shift,
whereas both open coordinate components preserve degree.
-/

namespace Verification.PathRecursionDegree

open Classical Verification.PathCochains Verification.PathConfigRecursion
  Verification.PathGlobalAffineSigns Verification.PathClosedSignedComplex

variable {R : Type*} [CommRing R]

def TotalDegree (n : ℕ) (p : ℤ) (x : Total (R := R) n) : Prop :=
  ∀ I, (I.val.card : ℤ) ≠ p → x I=0

theorem sign_degree (g ρ : R) (a b : Bool) (n : ℕ) (p : ℤ) (x : Total (R := R) n)
    (hx : TotalDegree n p x) : TotalDegree n p (totalSign g ρ a b n x) := by
  intro I hI
  apply Subtype.ext
  change stratumFactor g a b I.val • Verification.PathAffineSigns.signMap g ρ a b (x I).val=0
  rw [hx I hI]
  change stratumFactor g a b I.val • Verification.PathAffineSigns.signMap g ρ a b 0=0
  rw [map_zero,smul_zero]

theorem twist_degree (g : R) (n : ℕ) (p : ℤ) (x : Total (R := R) n)
    (hx : TotalDegree n p x) : TotalDegree n p (degreeTwist g n x) := by
  intro I hI
  change g^I.val.card • x I=0
  rw [hx I hI,smul_zero]

theorem open_up_card (n : ℕ) (I : Config n) : (openUp n I).val.val.card=I.val.card :=
  shift_card 1 I.val

theorem closed_up_card (n : ℕ) (I : Config n) : (closedUp n I).val.val.card=I.val.card+1 := by
  change (insert 1 (shift 2 I.val)).card=I.val.card+1
  rw [Finset.card_insert_of_not_mem (one_not_shift_two n I),shift_card]

theorem open_restriction_degree (n : ℕ) (bit : Bool) (p : ℤ) (x : Total (R := R) (n+1))
    (hx : TotalDegree (n+1) p x) :
    TotalDegree n p (Verification.PathOpenEmbedding.restriction n bit x) := by
  intro I hI
  apply Subtype.ext
  rw [Verification.PathOpenEmbedding.restriction_apply]
  rw [hx (openUp n I).val (by simpa only [open_up_card] using hI)]
  exact map_zero _

theorem open_extension_degree (n : ℕ) (bit : Bool) (p : ℤ) (x : Total (R := R) n)
    (hx : TotalDegree n p x) :
    TotalDegree (n+1) p (Verification.PathOpenEmbedding.extension n bit x) := by
  intro I hI
  by_cases ho : 1 ∈ I.val
  · exact Verification.PathOpenEmbedding.extension_closed n bit x I ho
  · apply Subtype.ext
    rw [Verification.PathOpenEmbedding.extension_open n bit x ⟨I,ho⟩]
    have hc : (openDown n ⟨I,ho⟩).val.card=I.val.card := open_card n ⟨I,ho⟩
    rw [hx (openDown n ⟨I,ho⟩) (by simpa only [hc] using hI)]
    exact map_zero _

theorem closed_restriction_degree (n : ℕ) (p : ℤ) (x : Total (R := R) (n+2))
    (hx : TotalDegree (n+2) (p+1) x) :
    TotalDegree n p (Verification.PathClosedEmbedding.restriction n x) := by
  intro I hI
  apply Subtype.ext
  rw [Verification.PathClosedEmbedding.restriction_apply]
  have hn : ((closedUp n I).val.val.card : ℤ) ≠ p+1 := by
    rw [closed_up_card,Nat.cast_add,Nat.cast_one]
    omega
  rw [hx (closedUp n I).val hn]
  rfl

theorem closed_extension_degree (n : ℕ) (p : ℤ) (x : Total (R := R) n)
    (hx : TotalDegree n p x) :
    TotalDegree (n+2) (p+1) (Verification.PathClosedEmbedding.extension n x) := by
  intro I hI
  by_cases hc : 1 ∈ I.val
  · apply Subtype.ext
    rw [Verification.PathClosedEmbedding.extension_closed n x ⟨I,hc⟩]
    have he : (closedDown n ⟨I,hc⟩).val.card+1=I.val.card := closed_card n ⟨I,hc⟩
    have hn : ((closedDown n ⟨I,hc⟩).val.card : ℤ) ≠ p := by
      intro hp
      have hh := congrArg (fun j : ℕ => (j:ℤ)) he
      simp only [Nat.cast_add,Nat.cast_one] at hh
      omega
    rw [hx (closedDown n ⟨I,hc⟩) hn]
    rfl
  · exact Verification.PathClosedEmbedding.extension_open n x I hc

theorem signed_extension_degree (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b : Bool) (n : ℕ) (p : ℤ) (x : Total (R := R) n) (hx : TotalDegree n p x) :
    TotalDegree (n+2) (p+1) (signedExtension g ρ hg hr a b n x) :=
  closed_extension_degree n p _ (twist_degree g n p _ (sign_degree g ρ a b n p x hx))

#print axioms TotalDegree
#print axioms sign_degree
#print axioms twist_degree
#print axioms open_up_card
#print axioms closed_up_card
#print axioms open_restriction_degree
#print axioms open_extension_degree
#print axioms closed_restriction_degree
#print axioms closed_extension_degree
#print axioms signed_extension_degree

end Verification.PathRecursionDegree
