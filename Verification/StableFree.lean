/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.LinearAlgebra.Prod
import Mathlib.Data.Nat.Choose.Sum

/-!
# Stable Free

The original projective-complement argument of manuscript.tex:443–447,
and the coefficient of its Koszul class at lines 431–437. The K₀ localization
theorem and existence of a finite free complement are external inputs here;
the isomorphism after adding that complement is constructed explicitly.
-/
namespace Verification.StableFree

variable {R : Type*} [CommRing R]
variable {P Q S U V : Type*}
variable [AddCommGroup P] [AddCommGroup Q] [AddCommGroup S]
variable [AddCommGroup U] [AddCommGroup V]
variable [Module R P] [Module R Q] [Module R S] [Module R U] [Module R V]

/-- Add the complement and explicitly reassociate both sides. -/
def addComplement (e : (P × Q) ≃ₗ[R] (U × Q)) (f : (Q × S) ≃ₗ[R] V) :
    (P × V) ≃ₗ[R] (U × V) :=
  ((LinearEquiv.refl R P).prodCongr f.symm).trans
    ((LinearEquiv.prodAssoc R P Q S).symm.trans
      ((e.prodCongr (LinearEquiv.refl R S)).trans
        ((LinearEquiv.prodAssoc R U Q S).trans
          ((LinearEquiv.refl R U).prodCongr f))))

/-- The resulting equivalence has the expected value, with no cancellation
assumption on the original projective module Q. -/
theorem addComplement_apply (e : (P × Q) ≃ₗ[R] (U × Q))
    (f : (Q × S) ≃ₗ[R] V) (p : P) (v : V) :
    addComplement e f (p,v) =
      ((e (p,(f.symm v).1)).1,
        f ((e (p,(f.symm v).1)).2,(f.symm v).2)) := rfl

/-- K₀ equality plus a projective complement gives stable freeness. -/
theorem stable_free_of_complement {r n : ℕ}
    (e : (P × Q) ≃ₗ[R] ((Fin r → R) × Q))
    (f : (Q × S) ≃ₗ[R] (Fin n → R)) :
    Nonempty ((P × (Fin n → R)) ≃ₗ[R] ((Fin r → R) × (Fin n → R))) :=
  ⟨addComplement e f⟩

theorem koszul_rank_zero (r : ℕ) (hr : r ≠ 0) :
    (∑ i ∈ Finset.range (r+1), ((-1)^i * r.choose i : ℤ)) = 0 :=
  Int.alternating_sum_range_choose_of_ne hr

/-- The vanishing is valid in the actual additive group of classes, not
only as an integer identity. -/
theorem koszul_class_zero {G : Type*} [AddCommGroup G]
    (r : ℕ) (hr : r ≠ 0) (unitClass : G) :
    (∑ i ∈ Finset.range (r+1), ((-1)^i * r.choose i : ℤ) • unitClass) = 0 := by
  have hsum (t : Finset ℕ) :
      (∑ i ∈ t, ((-1)^i * r.choose i : ℤ) • unitClass) =
        (∑ i ∈ t, ((-1)^i * r.choose i : ℤ)) • unitClass := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert i t hi ih => simp [hi, ih, add_zsmul]
  rw [hsum, koszul_rank_zero r hr, zero_smul]

#print axioms addComplement
#print axioms addComplement_apply
#print axioms stable_free_of_complement
#print axioms koszul_rank_zero
#print axioms koszul_class_zero
end Verification.StableFree
