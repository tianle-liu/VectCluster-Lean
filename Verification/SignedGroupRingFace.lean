/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SplitTorusFiber
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# Signed Group Ring Face

Literal signed group-ring quotients and their coordinate residue maps.
The residue retains monomials whose chosen character is nontrivial.
All descent and commutation assertions are proved in the group ring.
-/
noncomputable section
namespace Verification.SignedGroupRingFace
open MonoidAlgebra
variable {G H : Type*} [CommGroup G] [Group H]

abbrev RingOf (G : Type*) [CommGroup G] := MonoidAlgebra ℤ G

def weight (χ : G →* H) (a : G) : ℤ := by
  classical
  exact if χ a = 1 then 0 else 1

def projection (χ : G →* H) : RingOf G →ₗ[ℤ] RingOf G := by
  classical
  exact (Finsupp.filterAddHom (fun a => χ a ≠ 1)).toIntLinearMap

theorem projection_single (χ : G →* H) (a : G) (n : ℤ) :
    projection χ (Finsupp.single a n) = weight χ a • Finsupp.single a n := by
  classical
  change (Finsupp.single a n).filter (fun a => χ a ≠ 1) = _
  by_cases h : χ a = 1
  · simp [Finsupp.filter_single_of_neg, weight, h]
  · simp [Finsupp.filter_single_of_pos, weight, h]

theorem projection_shift (χ : G →* H) (g : G) (hg : χ g = 1) (a : RingOf G) :
    projection χ (a * of ℤ G g) = projection χ a * of ℤ G g := by
  classical
  induction a using Finsupp.induction with
  | zero => simp
  | @single_add a n f ha hn hf =>
    rw [add_mul, map_add, map_add, add_mul, hf]
    congr 1
    rw [of_apply, single_mul_single, projection_single, projection_single]
    simp [weight, map_mul, hg, smul_mul_assoc, single_mul_single]

def relation (g : G) (ε : ℤ) : RingOf G := of ℤ G g - algebraMap ℤ _ ε

theorem projection_relation_mul (χ : G →* H) (g : G) (hg : χ g = 1)
    (ε : ℤ) (a : RingOf G) :
    projection χ (a * relation g ε) = projection χ a * relation g ε := by
  rw [relation, mul_sub, map_sub, projection_shift χ g hg, mul_sub]
  congr 1
  rw [mul_comm a _, ← Algebra.smul_def, map_smul, Algebra.smul_def, mul_comm]

variable {ι : Type*}
def relations (g : ι → G) (ε : ι → ℤ) : Ideal (RingOf G) :=
  Ideal.span (Set.range fun i => relation (g i) (ε i))

theorem projection_mem (χ : G →* H) (g : ι → G) (ε : ι → ℤ)
    (hg : ∀ i, χ (g i) = 1) {a : RingOf G} (ha : a ∈ relations g ε) :
    projection χ a ∈ relations g ε := by
  have h : ∀ b, projection χ (b*a) ∈ relations g ε := by
    induction ha using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨i,rfl⟩
      intro b
      rw [projection_relation_mul χ (g i) (hg i)]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i))
    | zero => intro b; simp
    | add x y hx hy ihx ihy =>
      intro b
      rw [mul_add,map_add]
      exact Ideal.add_mem _ (ihx b) (ihy b)
    | smul b x hx ih =>
      intro c
      simpa only [smul_eq_mul,← mul_assoc] using ih (c*b)
  simpa only [one_mul] using h 1

def face (χ : G →* H) (g : ι → G) (ε : ι → ℤ)
    (hg : ∀ i, χ (g i) = 1) (J : Ideal (RingOf G)) (hJ : relations g ε ≤ J) :
    (RingOf G ⧸ relations g ε) →ₗ[ℤ] (RingOf G ⧸ J) :=
  (relations g ε).restrictScalars ℤ |>.mapQ (J.restrictScalars ℤ) (projection χ)
    (by intro a ha; exact hJ (projection_mem χ g ε hg ha))

theorem face_mk (χ : G →* H) (g : ι → G) (ε : ι → ℤ)
    (hg : ∀ i, χ (g i) = 1) (J : Ideal (RingOf G)) (hJ : relations g ε ≤ J)
    (a : RingOf G) :
    face χ g ε hg J hJ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk J (projection χ a) := rfl

theorem face_monomial (χ : G →* H) (g : ι → G) (ε : ι → ℤ)
    (hg : ∀ i, χ (g i) = 1) (J : Ideal (RingOf G)) (hJ : relations g ε ≤ J)
    (a : G) :
    face χ g ε hg J hJ (Ideal.Quotient.mk _ (of ℤ G a)) =
      weight χ a • Ideal.Quotient.mk J (of ℤ G a) := by
  classical
  rw [face_mk,of_apply,projection_single]
  exact map_zsmul _ _ _

variable {K : Type*} [Group K]
theorem projections_commute (χ : G →* H) (ψ : G →* K) (a : RingOf G) :
    projection χ (projection ψ a) = projection ψ (projection χ a) := by
  classical
  ext g
  change (a.filter (fun a => ψ a ≠ 1)).filter (fun a => χ a ≠ 1) g =
    (a.filter (fun a => χ a ≠ 1)).filter (fun a => ψ a ≠ 1) g
  simp only [Finsupp.filter_apply]
  split_ifs <;> rfl

#print axioms RingOf
#print axioms weight
#print axioms projection
#print axioms projection_single
#print axioms projection_shift
#print axioms relation
#print axioms projection_relation_mul
#print axioms relations
#print axioms projection_mem
#print axioms face
#print axioms face_mk
#print axioms face_monomial
#print axioms projections_commute
end Verification.SignedGroupRingFace
