/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOpenWords
import Verification.PathRightEndpoint

/-!
# Path Open Endpoint Words

The genuine endpoint word projectors commute with open-coordinate splitting.
-/

namespace Verification.PathOpenEndpointWords

open Classical Verification.PathRhoWords Verification.PathRhoFinite Verification.PathOpenWords

variable {R : Type*} [CommRing R]

theorem right_unprepend (k : R) (n : ℕ) (hn : 0<n) (bit : Bool)
    (x : List Bool →₀ R) (hx : x ∈ layer (R := R) (n+1)) :
    Verification.PathRightEndpoint.projection k (unprepend bit x)=
      unprepend bit (Verification.PathRightEndpoint.projection k x) := by
  let Q := Verification.PathRightEndpoint.projection k
  let D := Q.comp (unprepend bit)-(unprepend bit).comp Q
  have hh : layer (R := R) (n+1) ≤ LinearMap.ker D := by
    rw [layer,Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨w,hw,rfl⟩
    change w.length=n+1 at hw
    change Q (unprepend bit (Finsupp.single w 1))-unprepend bit (Q (Finsupp.single w 1))=0
    apply sub_eq_zero.mpr
    cases w with
    | nil => simp only [List.length_nil] at hw; omega
    | cons a tail =>
      have ht : tail.length=n := by simp only [List.length_cons] at hw; omega
      rw [← prepend_single]
      rw [Verification.PathRightEndpoint.projection_prepend k a n hn _
        (Finsupp.single_mem_supported R 1 ht),unprepend_prepend,unprepend_prepend]
      by_cases hb : bit=a
      · simp only [hb,↓reduceIte]
        rfl
      · simp only [hb,↓reduceIte,map_zero]
  exact sub_eq_zero.mp (LinearMap.mem_ker.mp (hh hx))

theorem left_zero_unprepend_false (x : List Bool →₀ R) :
    unprepend false (Verification.PathLeftEndpoint.projection (0:R) x)=unprepend false x := by
  have hh : (unprepend false).comp (Verification.PathLeftEndpoint.projection (0:R))=
      unprepend false := by
    apply Finsupp.lhom_ext
    intro w r
    have hr : Finsupp.single w r=r • Finsupp.single w (1:R) := by simp
    rw [hr,map_smul,map_smul]
    congr 1
    cases w with
    | nil =>
      ext v
      simp [LinearMap.comp_apply,Verification.PathLeftEndpoint.projection_single,
        Verification.PathLeftEndpoint.projectionColumn,unprepend_apply,Finsupp.single_apply]
    | cons a tail =>
      change unprepend false (Verification.PathLeftEndpoint.projection (0:R)
        (Finsupp.single (a::tail) 1))=unprepend false (Finsupp.single (a::tail) 1)
      rw [← prepend_single,Verification.PathLeftEndpoint.projection_prepend,map_smul,
        unprepend_prepend,unprepend_prepend]
      cases a <;> simp [Verification.PathRhoEndpoint.evaluation]
  exact LinearMap.congr_fun hh x

theorem left_zero_unprepend_true (x : List Bool →₀ R) :
    unprepend true (Verification.PathLeftEndpoint.projection (0:R) x)=0 := by
  have hh : (unprepend true).comp (Verification.PathLeftEndpoint.projection (0:R))=0 := by
    apply Finsupp.lhom_ext
    intro w r
    have hr : Finsupp.single w r=r • Finsupp.single w (1:R) := by simp
    rw [hr,map_smul,map_smul]
    congr 1
    cases w with
    | nil =>
      ext v
      simp [LinearMap.comp_apply,Verification.PathLeftEndpoint.projection_single,
        Verification.PathLeftEndpoint.projectionColumn,unprepend_apply,Finsupp.single_apply]
    | cons a tail =>
      change unprepend true (Verification.PathLeftEndpoint.projection (0:R)
        (Finsupp.single (a::tail) 1))=0
      rw [← prepend_single,Verification.PathLeftEndpoint.projection_prepend,map_smul,unprepend_prepend]
      simp
  exact LinearMap.congr_fun hh x

#print axioms right_unprepend
#print axioms left_zero_unprepend_false
#print axioms left_zero_unprepend_true

end Verification.PathOpenEndpointWords
