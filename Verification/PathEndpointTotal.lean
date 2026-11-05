/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathRightEndpoint
import Verification.PathCochainSquare

/-!
# Path Endpoint Total

Endpoint relations on the original stratum-indexed rho complex. These are
actual idempotents and actual quotient differentials, not assumptions of a
path contraction or of the geometric comparison.
-/

namespace Verification.PathEndpointTotal

open Classical Verification.PathCompression Verification.PathCochains
  Verification.PathRhoWords Verification.PathRhoFinite Verification.PathRhoConfiguration

variable {R : Type*} [CommRing R]

/-- Apply a length-preserving word map on every actual independent zero stratum. -/
noncomputable def totalMap (P : (List Bool →₀ R) →ₗ[R] (List Bool →₀ R))
    (hP : ∀ n x, x ∈ layer (R := R) n → P x ∈ layer n) (n : ℕ) :
    Total (R := R) n →ₗ[R] Total (R := R) n :=
  LinearMap.pi (fun I => LinearMap.codRestrict _
    (P.comp ((layer (available I.val (n+2)).card).subtype.comp (LinearMap.proj I)))
      (fun x => hP _ (x I).val (x I).property))

theorem totalMap_apply (P : (List Bool →₀ R) →ₗ[R] (List Bool →₀ R))
    (hP : ∀ n x, x ∈ layer (R := R) n → P x ∈ layer n) (n : ℕ)
    (x : Total (R := R) n) (I : Config n) :
    (totalMap P hP n x I).val=P (x I).val := rfl

noncomputable def left (k : R) (n : ℕ) : Total (R := R) n →ₗ[R] Total (R := R) n :=
  totalMap (Verification.PathLeftEndpoint.projection k)
    (Verification.PathLeftEndpoint.projection_mem_layer k) n

noncomputable def right (k : R) (n : ℕ) : Total (R := R) n →ₗ[R] Total (R := R) n :=
  totalMap (Verification.PathRightEndpoint.projection k)
    (Verification.PathRightEndpoint.projection_mem_layer k) n

theorem totalMap_idempotent (P : (List Bool →₀ R) →ₗ[R] (List Bool →₀ R))
    (hP : ∀ n x, x ∈ layer (R := R) n → P x ∈ layer n) (n : ℕ)
    (hid : P.comp P=P) :
    (totalMap P hP n).comp (totalMap P hP n)=totalMap P hP n := by
  apply LinearMap.ext
  intro x
  funext I
  apply Subtype.ext
  exact congrArg (fun f : _ →ₗ[R] _ => f (x I).val) hid

theorem left_idempotent (k : R) (n : ℕ) : (left k n).comp (left k n)=left k n :=
  totalMap_idempotent _ _ _ (Verification.PathLeftEndpoint.projection_idempotent k)

theorem right_idempotent (k : R) (n : ℕ) : (right k n).comp (right k n)=right k n :=
  totalMap_idempotent _ _ _ (Verification.PathRightEndpoint.projection_idempotent k)

/-- An all-position word quotient identity assembles over the literal path incidence sum. -/
theorem totalMap_quotient (P : (List Bool →₀ R) →ₗ[R] (List Bool →₀ R))
    (hP : ∀ n x, x ∈ layer (R := R) n → P x ∈ layer n) (g ρ : R) (n : ℕ)
    (hf : ∀ i m, i+3 ≤ m → ∀ x, x ∈ layer (R := R) m →
      P (face (-g) ρ i (P x))=P (face (-g) ρ i x)) :
    (totalMap P hP n).comp ((differential g ρ n).comp (totalMap P hP n))=
      (totalMap P hP n).comp (differential g ρ n) := by
  apply LinearMap.ext
  intro x
  funext J
  apply Subtype.ext
  change P (ambientDifferential g ρ n (inclusion n (totalMap P hP n x)) J)=
    P (ambientDifferential g ρ n (inclusion n x) J)
  simp only [ambientDifferential_apply,map_sum,faceMap,LinearMap.smul_apply,map_smul]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  have hsub : insert j (eraseConfig J j).val=J.val := Finset.insert_erase hj
  have ha := addable_of_insert (hsub.symm ▸ J.property) (Finset.not_mem_erase _ _)
  exact hf _ _ (faceIndex_valid (eraseConfig J j).property j (J.property.1 hj) ha)
    (x (eraseConfig J j)).val (x (eraseConfig J j)).property

theorem left_quotient (k g ρ : R) (n : ℕ) (hkg : (-g)*k=k) (hk : k*k=ρ*k) :
    (left k n).comp ((differential g ρ n).comp (left k n))=
      (left k n).comp (differential g ρ n) := by
  apply totalMap_quotient
  intro i m hm x hx
  exact congrArg (fun f : _ →ₗ[R] _ => f x)
    (Verification.PathLeftEndpoint.projection_face_quotient k (-g) ρ hkg hk i)

theorem right_quotient (k g ρ : R) (n : ℕ) (hk : k*k=ρ*k) :
    (right k n).comp ((differential g ρ n).comp (right k n))=
      (right k n).comp (differential g ρ n) :=
  totalMap_quotient _ _ _ _ _ (Verification.PathRightEndpoint.projection_face_quotient k (-g) ρ hk)

/-- The two distinct endpoints commute on every layer of length at least two. -/
theorem word_endpoints_commute (a b : R) (n : ℕ) (hn : 2 ≤ n)
    (x : List Bool →₀ R) (hx : x ∈ layer (R := R) n) :
    Verification.PathLeftEndpoint.projection a (Verification.PathRightEndpoint.projection b x)=
      Verification.PathRightEndpoint.projection b (Verification.PathLeftEndpoint.projection a x) := by
  let L := Verification.PathLeftEndpoint.projection a
  let Q := Verification.PathRightEndpoint.projection b
  have hh : layer (R := R) n ≤ LinearMap.ker (L.comp Q-Q.comp L) := by
    rw [layer,Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨w,hw,rfl⟩
    change w.length=n at hw
    change L (Q (Finsupp.single w 1))-Q (L (Finsupp.single w 1))=0
    apply sub_eq_zero.mpr
    cases w with
    | nil => simp only [List.length_nil] at hw; omega
    | cons c tail =>
      have ht : 0 < tail.length := by simp only [List.length_cons] at hw; omega
      change Verification.PathLeftEndpoint.projection a
          (Verification.PathRightEndpoint.projection b (Finsupp.single (c::tail) 1))=
        Verification.PathRightEndpoint.projection b
          (Verification.PathLeftEndpoint.projection a (Finsupp.single (c::tail) 1))
      rw [← prepend_single]
      rw [Verification.PathRightEndpoint.projection_prepend b c tail.length ht _
        (Finsupp.single_mem_supported R 1 rfl),Verification.PathLeftEndpoint.projection_prepend,
        Verification.PathLeftEndpoint.projection_prepend,map_smul,
        Verification.PathRightEndpoint.projection_prepend b false tail.length ht _
          (Finsupp.single_mem_supported R 1 rfl)]
  exact sub_eq_zero.mp (LinearMap.mem_ker.mp (hh hx))

theorem even_free_length (a : ℕ) (I : Config (2*a)) :
    2 ≤ (available I.val (2*a+2)).card := by
  have hpos : 0 < (available I.val (2*a+2)).card :=
    Finset.card_pos.mpr ⟨0,zero_available I.property (by omega)⟩
  have hc := available_card I.property
  omega

theorem endpoints_commute (a b : R) (m : ℕ) :
    (left a (2*m)).comp (right b (2*m))=(right b (2*m)).comp (left a (2*m)) := by
  apply LinearMap.ext
  intro x
  funext I
  apply Subtype.ext
  exact word_endpoints_commute a b _ (even_free_length m I) (x I).val (x I).property

#print axioms totalMap
#print axioms totalMap_apply
#print axioms left
#print axioms right
#print axioms totalMap_idempotent
#print axioms left_idempotent
#print axioms right_idempotent
#print axioms totalMap_quotient
#print axioms left_quotient
#print axioms right_quotient
#print axioms word_endpoints_commute
#print axioms even_free_length
#print axioms endpoints_commute

end Verification.PathEndpointTotal
