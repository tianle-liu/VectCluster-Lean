/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.EvenGraphBridge

/-!
# Augmented Simplex Contraction

Actual integral augmented-simplex chains in an exterior algebra. The boundary
is the sum of coordinate contractions; the displayed ordered-word formula is
the usual signed deletion boundary. Wedge multiplication by a chosen vertex
is an explicit contraction when the vertex set is nonempty.
-/

namespace Verification.AugmentedSimplexContraction

open Verification.EvenDifferential Verification.EvenGraphBridge

variable {R α : Type*} [CommRing R] [Fintype α] [LinearOrder α]

noncomputable def totalDual : Module.Dual R (α → R) := ∑ a : α, LinearMap.proj a

noncomputable def boundary : ExteriorAlgebra R (α → R) →ₗ[R] ExteriorAlgebra R (α → R) :=
  contract totalDual

def homotopy (a : α) : ExteriorAlgebra R (α → R) →ₗ[R] ExteriorAlgebra R (α → R) :=
  LinearMap.mulLeft R (ExteriorAlgebra.ι R (Pi.single a 1))

theorem totalDual_single (a : α) : totalDual (R := R) (Pi.single a 1) = 1 := by
  simp [totalDual, LinearMap.sum_apply, Pi.single_apply]

omit [LinearOrder α] in
theorem boundary_eq_sum :
    boundary (R := R) (α := α) = ∑ a : α, contract (LinearMap.proj a) := by
  exact map_sum (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (α → R)))) _ _

/-- Exact signed boundary on every actual ordered exterior basis monomial. -/
theorem boundary_word (A : Finset α) :
    boundary (R := R) (word (A.sort (· ≤ ·))) =
      ∑ a ∈ A, (-1 : R) ^ rankBelow A a • word ((A.erase a).sort (· ≤ ·)) := by
  classical
  rw [boundary_eq_sum, LinearMap.sum_apply]
  trans ∑ a ∈ A, contract (LinearMap.proj a) (word (A.sort (· ≤ ·)))
  · symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro a _ ha
    exact contract_word_absent a _ (by simpa using ha)
  · apply Finset.sum_congr rfl
    intro a ha
    rw [contract_word_present a _ (Finset.sort_nodup _ _) (by simpa using ha),
      idxOf_sort A a ha, sort_erase A a]

omit [LinearOrder α] in
theorem boundary_squared :
    (boundary (R := R) (α := α)).comp boundary = 0 := by
  apply LinearMap.ext
  intro x
  exact CliffordAlgebra.contractLeft_contractLeft (totalDual (R := R) (α := α))
    (Q := (0 : QuadraticForm R (α → R))) x

omit [Fintype α] in
theorem homotopy_squared (a : α) :
    (homotopy (R := R) a).comp (homotopy a) = 0 := by
  apply LinearMap.ext
  intro x
  change ExteriorAlgebra.ι R (Pi.single a 1) * (ExteriorAlgebra.ι R (Pi.single a 1) * x) = 0
  rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

/-- The contraction equation for the full augmented simplex, including its empty face. -/
theorem boundary_homotopy (a : α) :
    (boundary (R := R)).comp (homotopy a) + (homotopy a).comp boundary = LinearMap.id := by
  apply LinearMap.ext
  intro x
  change contract totalDual (ExteriorAlgebra.ι R (Pi.single a 1) * x) +
    ExteriorAlgebra.ι R (Pi.single a 1) * contract totalDual x = x
  rw [CliffordAlgebra.contractLeft_ι_mul, totalDual_single, one_smul, sub_add_cancel]

theorem homotopy_regular (a : α) :
    ((homotopy (R := R) a).comp boundary).comp (homotopy a) = homotopy a := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun (boundary_homotopy (R := R) a) (homotopy a x)
  have hh := LinearMap.congr_fun (homotopy_squared (R := R) a) x
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hh
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    hh, map_zero, zero_add] using h

theorem boundary_regular (a : α) :
    ((boundary (R := R)).comp (homotopy a)).comp boundary = boundary := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun (boundary_homotopy (R := R) a) (boundary x)
  have hh := LinearMap.congr_fun (boundary_squared (R := R) (α := α)) x
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hh
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    hh, map_zero, add_zero] using h

omit [Fintype α] [LinearOrder α] in
theorem empty_algebraMap_inverse [IsEmpty α] (x : ExteriorAlgebra R (α → R)) :
    algebraMap R (ExteriorAlgebra R (α → R)) (ExteriorAlgebra.algebraMapInv x) = x := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r => simp [ExteriorAlgebra.algebraMap_leftInverse]
  | ι v =>
    have hv : v = 0 := Subsingleton.elim _ _
    simp [hv]
  | mul x y hx hy => simp only [map_mul, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- An empty simplex fiber is precisely one copy of R, not the zero module. -/
noncomputable def emptyEquiv [IsEmpty α] : ExteriorAlgebra R (α → R) ≃ₐ[R] R :=
  AlgEquiv.ofBijective ExteriorAlgebra.algebraMapInv
    ⟨Function.LeftInverse.injective (empty_algebraMap_inverse (R := R) (α := α)),
      fun r => ⟨algebraMap R (ExteriorAlgebra R (α → R)) r,
        ExteriorAlgebra.algebraMap_leftInverse (α → R) r⟩⟩

omit [LinearOrder α] in
theorem empty_boundary [IsEmpty α] : boundary (R := R) (α := α) = 0 := by
  rw [boundary_eq_sum]
  simp

#print axioms totalDual
#print axioms boundary
#print axioms homotopy
#print axioms totalDual_single
#print axioms boundary_eq_sum
#print axioms boundary_word
#print axioms boundary_squared
#print axioms homotopy_squared
#print axioms boundary_homotopy
#print axioms homotopy_regular
#print axioms boundary_regular
#print axioms empty_algebraMap_inverse
#print axioms emptyEquiv
#print axioms empty_boundary

end Verification.AugmentedSimplexContraction
