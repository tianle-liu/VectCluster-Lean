/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathRhoLeading
import Verification.PathEndpointLeading
import Verification.PathWeightFiltration

/-!
# Path Rho Filtration

The full differential differs from its rho-zero specialization by a
strictly weight-decreasing operator on the literal finite word modules.
-/

namespace Verification.PathRhoFiltration

open Classical Verification.PathCompression Verification.PathCochains
  Verification.PathRhoConfiguration Verification.PathRhoWords
  Verification.PathRhoLeading Verification.PathEndpointLeading
  Verification.PathWordWeight Verification.PathWeightFiltration

variable {R : Type*} [CommRing R]

theorem face_difference_strict_bounded (ε ρ : R) (i p s : ℕ) (x : List Bool →₀ R)
    (hx : x ∈ bounded (R := R) p s) :
    face ε ρ i x-face ε 0 i x ∈ strictBounded (R := R) (p+1) s := by
  let D : (List Bool →₀ R) →ₗ[R] (List Bool →₀ R) := face ε ρ i-face ε 0 i
  have hh : bounded (R := R) p s ≤ (strictBounded (p+1) s).comap D := by
    rw [bounded,Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨w,hw,rfl⟩
    change D (Finsupp.single w 1) ∈ strictBounded (R := R) (p+1) s
    apply (Finsupp.mem_supported' R _).mpr
    intro v hv
    change (face ε ρ i (Finsupp.single w 1)-face ε 0 i (Finsupp.single w 1)) v=0
    rw [face_single,face_single]
    apply face_difference_strict ε ρ i p w v
    change p+w.count true ≤ s at hw
    change ¬(p+1)+v.count true < s at hv
    omega
  exact hh hx

def TotalStrict (n s : ℕ) (x : Total (R := R) n) : Prop :=
  ∀ I, (x I).val ∈ strictBounded (R := R) I.val.card s

theorem differential_difference_strict (g ρ : R) (n s : ℕ) (x : Total (R := R) n)
    (hx : TotalBounded n s x) :
    TotalStrict n s (differential g ρ n x-differential g 0 n x) := by
  intro J
  change ambientDifferential g ρ n (inclusion n x) J-
    ambientDifferential g 0 n (inclusion n x) J ∈ strictBounded (R := R) J.val.card s
  rw [ambientDifferential_apply,ambientDifferential_apply,← Finset.sum_sub_distrib]
  apply Submodule.sum_mem
  intro j hj
  change incidence g (eraseConfig J j).val j •
    face (-g) ρ (faceIndex (eraseConfig J j).val j) (x (eraseConfig J j)).val-
      incidence g (eraseConfig J j).val j •
    face (-g) 0 (faceIndex (eraseConfig J j).val j) (x (eraseConfig J j)).val ∈ _
  rw [← smul_sub]
  apply (strictBounded J.val.card s).smul_mem
  have hc : (eraseConfig J j).val.card+1=J.val.card := Finset.card_erase_add_one hj
  have hh := face_difference_strict_bounded (-g) ρ (faceIndex (eraseConfig J j).val j)
    (eraseConfig J j).val.card s (x (eraseConfig J j)).val (hx (eraseConfig J j))
  simpa only [hc] using hh

theorem right_total_strict (k : R) (n s : ℕ) (x : Total (R := R) n)
    (hx : TotalStrict n s x) :
    TotalStrict n s (Verification.PathEndpointTotal.right k n x) := by
  intro I
  exact right_strict k I.val.card s (x I).val (hx I)

theorem left_total_strict (k : R) (n s : ℕ) (x : Total (R := R) n)
    (hx : TotalStrict n s x) :
    TotalStrict n s (Verification.PathEndpointTotal.left k n x) := by
  intro I
  exact left_strict k I.val.card s (x I).val (hx I)

theorem right_total_difference_strict (k : R) (n s : ℕ) (x : Total (R := R) n)
    (hx : TotalBounded n s x) :
    TotalStrict n s (Verification.PathEndpointTotal.right k n x-
      Verification.PathEndpointTotal.right 0 n x) := by
  intro I
  exact right_difference_strict k I.val.card s (x I).val (hx I)

/-- Both the interior-rho terms and the evaluated endpoint-rho terms lower weight. -/
theorem projected_difference_strict (g ρ k : R) (n s : ℕ) (x : Total (R := R) n)
    (hx : TotalBounded n s x) :
    TotalStrict n s (Verification.PathEndpointTotal.right k n (differential g ρ n x)-
      Verification.PathEndpointTotal.right 0 n (differential g 0 n x)) := by
  have h₁ := right_total_strict k n s _ (differential_difference_strict g ρ n s x hx)
  have h₂ := right_total_difference_strict k n s _ (differential_bounded g 0 n s x hx)
  intro I
  have hh := (strictBounded (R := R) I.val.card s).add_mem (h₁ I) (h₂ I)
  simpa only [map_sub,Pi.sub_apply,Pi.add_apply,Submodule.coe_sub,Submodule.coe_add,
    sub_add_sub_cancel] using hh

#print axioms face_difference_strict_bounded
#print axioms TotalStrict
#print axioms differential_difference_strict
#print axioms right_total_strict
#print axioms left_total_strict
#print axioms right_total_difference_strict
#print axioms projected_difference_strict

end Verification.PathRhoFiltration
