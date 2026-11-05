/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.Elimination
import Mathlib.AlgebraicGeometry.Scheme

/-!
# Elimination With Constraints

The ring-level zero-stratum calculation in manuscript.tex:395–400.
Coefficient equations and equations solving invertible-coordinate exchange
partners may be imposed simultaneously. The resulting actual quotient is a
polynomial algebra over the coefficient quotient, over arbitrary commutative
rings, including nonreduced rings. The application identifies the coefficient
ideal with the torus-character equations; that geometric identification is not
assumed or asserted here.
-/

namespace Verification.EliminationWithConstraints

open MvPolynomial

variable {R ι κ : Type*} [CommRing R]

/-- Both the coefficient constraints and the unit-coefficient linear equations. -/
noncomputable def constraints (J : Ideal R) (a : κ → Rˣ) (b : κ → R) :
    Ideal (MvPolynomial (ι ⊕ κ) R) :=
  Ideal.span ((C : R →+* MvPolynomial (ι ⊕ κ) R) '' (J : Set R) ∪
    Set.range (Elimination.relation a b))

/-- Eliminate the solved variables and reduce coefficients modulo `J`. -/
noncomputable def substitute (J : Ideal R) (a : κ → Rˣ) (b : κ → R) :
    MvPolynomial (ι ⊕ κ) R →+* MvPolynomial ι (R ⧸ J) :=
  (MvPolynomial.map (Ideal.Quotient.mk J)).comp (Elimination.substitute a b).toRingHom

theorem substitute_C (J : Ideal R) (a : κ → Rˣ) (b : κ → R) (r : R) :
    substitute (ι := ι) J a b (C r) = C (Ideal.Quotient.mk J r) := by
  simp [substitute, Elimination.substitute]

theorem substitute_free (J : Ideal R) (a : κ → Rˣ) (b : κ → R) (i : ι) :
    substitute J a b (X (Sum.inl i)) = X i := by
  simp [substitute, Elimination.substitute]

theorem substitute_eliminated (J : Ideal R) (a : κ → Rˣ) (b : κ → R) (k : κ) :
    substitute (ι := ι) J a b (X (Sum.inr k)) =
      C (Ideal.Quotient.mk J ((((a k)⁻¹ : Rˣ) : R) * b k)) := by
  simp [substitute, Elimination.substitute]

theorem constraints_le_kernel (J : Ideal R) (a : κ → Rˣ) (b : κ → R) :
    constraints (ι := ι) J a b ≤ RingHom.ker (substitute J a b) := by
  apply Ideal.span_le.mpr
  rintro p (⟨r, hr, rfl⟩ | ⟨k, rfl⟩)
  · change substitute J a b (C r) = 0
    rw [substitute_C, Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]
  · change MvPolynomial.map (Ideal.Quotient.mk J)
      (Elimination.substitute a b (Elimination.relation a b k)) = 0
    rw [Elimination.substitute_relation, map_zero]

noncomputable def descend (J : Ideal R) (a : κ → Rˣ) (b : κ → R) :
    (MvPolynomial (ι ⊕ κ) R ⧸ constraints J a b) →+* MvPolynomial ι (R ⧸ J) :=
  Ideal.Quotient.lift (constraints J a b) (substitute J a b)
    (fun _ hp => constraints_le_kernel J a b hp)

theorem quotient_coefficient (J : Ideal R) (a : κ → Rˣ) (b : κ → R)
    (r : R) (hr : r ∈ J) :
    Ideal.Quotient.mk (constraints (ι := ι) J a b) (C r) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (Or.inl ⟨r, hr, rfl⟩)

noncomputable def coefficientLift (J : Ideal R) (a : κ → Rˣ) (b : κ → R) :
    (R ⧸ J) →+* (MvPolynomial (ι ⊕ κ) R ⧸ constraints J a b) :=
  Ideal.Quotient.lift J ((Ideal.Quotient.mk (constraints J a b)).comp C)
    (quotient_coefficient J a b)

noncomputable def includeFree (J : Ideal R) (a : κ → Rˣ) (b : κ → R) :
    MvPolynomial ι (R ⧸ J) →+* (MvPolynomial (ι ⊕ κ) R ⧸ constraints J a b) :=
  eval₂Hom (coefficientLift J a b)
    (fun i => Ideal.Quotient.mk (constraints J a b) (X (Sum.inl i)))

theorem includeFree_C_mk (J : Ideal R) (a : κ → Rˣ) (b : κ → R) (r : R) :
    includeFree (ι := ι) J a b (C (Ideal.Quotient.mk J r)) =
      Ideal.Quotient.mk (constraints J a b) (C r) := by
  simp [includeFree, coefficientLift]

theorem descend_includeFree (J : Ideal R) (a : κ → Rˣ) (b : κ → R) :
    (descend (ι := ι) J a b).comp (includeFree J a b) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro r
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    simp only [RingHom.comp_apply, includeFree_C_mk, RingHom.id_apply]
    exact substitute_C J a b r
  · intro i
    simp only [RingHom.comp_apply, includeFree, eval₂Hom_X', RingHom.id_apply]
    exact substitute_free J a b i

theorem quotient_relation (J : Ideal R) (a : κ → Rˣ) (b : κ → R) (k : κ) :
    Ideal.Quotient.mk (constraints (ι := ι) J a b) (Elimination.relation a b k) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (Or.inr (Set.mem_range_self k))

theorem quotient_eliminated_variable (J : Ideal R) (a : κ → Rˣ) (b : κ → R)
    (k : κ) :
    Ideal.Quotient.mk (constraints (ι := ι) J a b) (X (Sum.inr k)) =
      Ideal.Quotient.mk (constraints J a b) (C ((((a k)⁻¹ : Rˣ) : R) * b k)) := by
  let q := Ideal.Quotient.mk (constraints (ι := ι) J a b)
  have h : q (C (a k : R)) * q (X (Sum.inr k)) = q (C (b k)) := by
    have hr := quotient_relation (ι := ι) J a b k
    simpa [Elimination.relation, map_sub, map_mul, sub_eq_zero, q] using hr
  have hinv : q (C (((a k)⁻¹ : Rˣ) : R)) * q (C (a k : R)) = 1 := by
    rw [← map_mul, ← C_mul]
    simp
  calc
    q (X (Sum.inr k)) =
        q (C (((a k)⁻¹ : Rˣ) : R)) * (q (C (a k : R)) * q (X (Sum.inr k))) := by
          rw [← mul_assoc, hinv, one_mul]
    _ = q (C (((a k)⁻¹ : Rˣ) : R)) * q (C (b k)) := by rw [h]
    _ = q (C ((((a k)⁻¹ : Rˣ) : R) * b k)) := by rw [← map_mul, ← C_mul]

theorem includeFree_descend (J : Ideal R) (a : κ → Rˣ) (b : κ → R) :
    (includeFree (ι := ι) J a b).comp (descend J a b) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    change includeFree J a b (substitute J a b (C r)) = _
    rw [substitute_C, includeFree_C_mk]
    rfl
  · intro i
    change includeFree J a b (substitute J a b (X i)) = _
    cases i with
    | inl i =>
      rw [substitute_free]
      simp only [includeFree, eval₂Hom_X', RingHom.comp_apply, RingHom.id_apply]
    | inr k =>
      rw [substitute_eliminated, includeFree_C_mk]
      exact (quotient_eliminated_variable J a b k).symm

/-- The entire simultaneous quotient is a polynomial ring over the coefficient
quotient. This is an equivalence of rings, not just their field-valued points. -/
noncomputable def quotientRingEquiv (J : Ideal R) (a : κ → Rˣ) (b : κ → R) :
    (MvPolynomial (ι ⊕ κ) R ⧸ constraints J a b) ≃+* MvPolynomial ι (R ⧸ J) :=
  RingEquiv.ofRingHom (descend J a b) (includeFree J a b)
    (descend_includeFree J a b) (includeFree_descend J a b)

/-- The equivalence preserves the original coefficient algebra structure. -/
noncomputable def quotientEquiv (J : Ideal R) (a : κ → Rˣ) (b : κ → R) :
    (MvPolynomial (ι ⊕ κ) R ⧸ constraints J a b) ≃ₐ[R] MvPolynomial ι (R ⧸ J) :=
  AlgEquiv.ofRingEquiv (f := quotientRingEquiv J a b) (fun r => by
    change substitute J a b (C r) = C (Ideal.Quotient.mk J r)
    exact substitute_C J a b r)

universe u

/-- The same calculation gives an isomorphism of the actual affine schemes. -/
noncomputable def quotientSpecIso {S α β : Type u} [CommRing S]
    (J : Ideal S) (a : β → Sˣ) (b : β → S) :
    AlgebraicGeometry.Spec (CommRingCat.of
      (MvPolynomial (α ⊕ β) S ⧸ constraints J a b)) ≅
      AlgebraicGeometry.Spec (CommRingCat.of (MvPolynomial α (S ⧸ J))) :=
  AlgebraicGeometry.Scheme.Spec.mapIso
    (quotientRingEquiv J a b).toCommRingCatIso.symm.op

#print axioms constraints
#print axioms substitute
#print axioms substitute_C
#print axioms substitute_free
#print axioms substitute_eliminated
#print axioms constraints_le_kernel
#print axioms descend
#print axioms quotient_coefficient
#print axioms coefficientLift
#print axioms includeFree
#print axioms includeFree_C_mk
#print axioms descend_includeFree
#print axioms quotient_relation
#print axioms quotient_eliminated_variable
#print axioms includeFree_descend
#print axioms quotientRingEquiv
#print axioms quotientEquiv
#print axioms quotientSpecIso

end Verification.EliminationWithConstraints
