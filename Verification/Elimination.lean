/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Elimination

Eliminating exchange partners whose original coordinates are invertible.
This constructs an actual algebra equivalence over every commutative ring,
including nonreduced rings. It is the algebraic elimination used when
describing zero strata and freezing divisors in manuscript.tex:375–377,
395–400 and 514–517.
-/

namespace Verification.Elimination

open MvPolynomial

variable {R ι κ : Type*} [CommRing R]

noncomputable def relation (a : κ → Rˣ) (b : κ → R) (k : κ) :
    MvPolynomial (ι ⊕ κ) R := C (a k : R) * X (Sum.inr k) - C (b k)

noncomputable def relations (a : κ → Rˣ) (b : κ → R) :
    Ideal (MvPolynomial (ι ⊕ κ) R) := Ideal.span (Set.range (relation a b))

noncomputable def substitute (a : κ → Rˣ) (b : κ → R) :
    MvPolynomial (ι ⊕ κ) R →ₐ[R] MvPolynomial ι R :=
  aeval (Sum.elim X (fun k => C (((a k)⁻¹ : Rˣ) * b k)))

theorem substitute_relation (a : κ → Rˣ) (b : κ → R) (k : κ) :
    substitute (ι := ι) a b (relation a b k) = 0 := by
  simp only [relation, substitute, map_sub, map_mul, aeval_C, aeval_X, Sum.elim_inr]
  change C (a k : R) * (C (((a k)⁻¹ : Rˣ) : R) * C (b k)) - C (b k) = 0
  rw [← mul_assoc, ← C_mul]
  simp

theorem relations_le_kernel (a : κ → Rˣ) (b : κ → R) :
    relations (ι := ι) a b ≤ RingHom.ker (substitute a b).toRingHom := by
  apply Ideal.span_le.mpr
  rintro p ⟨k, rfl⟩
  exact substitute_relation a b k

noncomputable def descend (a : κ → Rˣ) (b : κ → R) :
    (MvPolynomial (ι ⊕ κ) R ⧸ relations a b) →ₐ[R] MvPolynomial ι R :=
  Ideal.Quotient.liftₐ (relations a b) (substitute a b) (relations_le_kernel a b)

noncomputable def includeFree (a : κ → Rˣ) (b : κ → R) :
    MvPolynomial ι R →ₐ[R] (MvPolynomial (ι ⊕ κ) R ⧸ relations a b) :=
  (Ideal.Quotient.mkₐ R (relations a b)).comp (rename Sum.inl)

theorem descend_includeFree (a : κ → Rˣ) (b : κ → R) :
    (descend (ι := ι) a b).comp (includeFree a b) = AlgHom.id R _ := by
  ext i
  simp [descend, includeFree, substitute]

theorem quotient_relation (a : κ → Rˣ) (b : κ → R) (k : κ) :
    Ideal.Quotient.mk (relations (ι := ι) a b) (relation a b k) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (Set.mem_range_self k)

theorem quotient_eliminated_variable (a : κ → Rˣ) (b : κ → R) (k : κ) :
    Ideal.Quotient.mk (relations (ι := ι) a b) (X (Sum.inr k)) =
      Ideal.Quotient.mk (relations a b) (C (((a k)⁻¹ : Rˣ) * b k)) := by
  let q := Ideal.Quotient.mk (relations (ι := ι) a b)
  have h : q (C (a k : R)) * q (X (Sum.inr k)) = q (C (b k)) := by
    have hr := quotient_relation (ι := ι) a b k
    simpa [relation, map_sub, map_mul, sub_eq_zero, q] using hr
  have hinv : q (C (((a k)⁻¹ : Rˣ) : R)) * q (C (a k : R)) = 1 := by
    rw [← map_mul, ← C_mul]
    simp
  calc
    q (X (Sum.inr k)) =
        q (C (((a k)⁻¹ : Rˣ) : R)) * (q (C (a k : R)) * q (X (Sum.inr k))) := by
          rw [← mul_assoc, hinv, one_mul]
    _ = q (C (((a k)⁻¹ : Rˣ) : R)) * q (C (b k)) := by rw [h]
    _ = q (C (((a k)⁻¹ : Rˣ) * b k)) := by rw [← map_mul, ← C_mul]

theorem includeFree_descend (a : κ → Rˣ) (b : κ → R) :
    (includeFree (ι := ι) a b).comp (descend a b) = AlgHom.id R _ := by
  apply Ideal.Quotient.algHom_ext
  ext i
  cases i with
  | inl i => simp [includeFree, descend, substitute]
  | inr k =>
    change includeFree a b (substitute a b (X (Sum.inr k))) =
      Ideal.Quotient.mk (relations a b) (X (Sum.inr k))
    rw [show substitute (ι := ι) a b (X (Sum.inr k)) =
      C ((((a k)⁻¹ : Rˣ) : R) * b k) by simp only [substitute, aeval_X, Sum.elim_inr]]
    change Ideal.Quotient.mk (relations a b) (rename Sum.inl (C _)) = _
    rw [rename_C]
    exact (quotient_eliminated_variable (ι := ι) a b k).symm

/-- The quotient by all unit-coefficient linear equations is the polynomial
algebra on the free variables, not merely a bijection on field-valued points. -/
noncomputable def quotientEquiv (a : κ → Rˣ) (b : κ → R) :
    (MvPolynomial (ι ⊕ κ) R ⧸ relations a b) ≃ₐ[R] MvPolynomial ι R :=
  AlgEquiv.ofAlgHom (descend a b) (includeFree a b)
    (descend_includeFree a b) (includeFree_descend a b)

#print axioms substitute_relation
#print axioms relations_le_kernel
#print axioms descend_includeFree
#print axioms quotient_relation
#print axioms quotient_eliminated_variable
#print axioms includeFree_descend
#print axioms quotientEquiv

end Verification.Elimination

-- Explicit dependency audit of the early module constructions.
#print axioms Verification.Elimination.descend
#print axioms Verification.Elimination.includeFree
#print axioms Verification.Elimination.relation
#print axioms Verification.Elimination.relations
#print axioms Verification.Elimination.substitute
