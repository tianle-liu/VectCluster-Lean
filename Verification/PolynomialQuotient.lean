/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StratumPresentation
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Polynomial Quotient

Coefficient base change by a quotient, for actual polynomial quotient
rings. This supplies the closed-locus part of the original exchange strata.
-/
namespace Verification.PolynomialQuotient
open MvPolynomial
variable {R α : Type*} [CommRing R] (I : Ideal R)

abbrev coefficientIdeal : Ideal (MvPolynomial α R) := I.map C
abbrev CoefficientQuotient := MvPolynomial α R ⧸ coefficientIdeal (α := α) I

theorem coefficientIdeal_le_kernel : coefficientIdeal (α := α) I ≤
    RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk I)) := by
  rw [coefficientIdeal, Ideal.map_le_iff_le_comap]
  intro r hr
  change MvPolynomial.map (Ideal.Quotient.mk I) (C r) = 0
  rw [map_C, Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]

noncomputable def forward : CoefficientQuotient (α := α) I →+* MvPolynomial α (R ⧸ I) :=
  Ideal.Quotient.lift _ (MvPolynomial.map (Ideal.Quotient.mk I)) (coefficientIdeal_le_kernel I)

noncomputable def coefficientLift : (R ⧸ I) →+* CoefficientQuotient (α := α) I :=
  Ideal.Quotient.lift I ((Ideal.Quotient.mk (coefficientIdeal I)).comp C) (by
    intro r hr
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_map_of_mem C hr)

noncomputable def backward : MvPolynomial α (R ⧸ I) →+* CoefficientQuotient (α := α) I :=
  eval₂Hom (coefficientLift I) (fun a => Ideal.Quotient.mk _ (X a))

theorem backward_C (r : R) :
    backward (α := α) I (C (Ideal.Quotient.mk I r)) =
      Ideal.Quotient.mk (coefficientIdeal I) (C r) := by
  simp [backward, coefficientLift]

theorem backward_X (a : α) :
    backward I (X a) = Ideal.Quotient.mk (coefficientIdeal I) (X a) := by
  simp [backward]

theorem forward_backward : (forward (α := α) I).comp (backward I) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro r
    obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective r
    change forward I (backward I (C (Ideal.Quotient.mk I r))) = _
    rw [backward_C]
    change MvPolynomial.map (Ideal.Quotient.mk I) (C r) = _
    simp
  · intro a
    change forward I (backward I (X a)) = _
    rw [backward_X]
    change MvPolynomial.map (Ideal.Quotient.mk I) (X a) = _
    simp

theorem backward_forward : (backward (α := α) I).comp (forward I) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    change backward I (MvPolynomial.map (Ideal.Quotient.mk I) (C r)) = _
    rw [map_C, backward_C]
    rfl
  · intro a
    change backward I (MvPolynomial.map (Ideal.Quotient.mk I) (X a)) = _
    rw [map_X, backward_X]
    rfl

noncomputable def coefficientQuotientEquiv :
    CoefficientQuotient (α := α) I ≃+* MvPolynomial α (R ⧸ I) :=
  RingEquiv.ofRingHom (forward I) (backward I) (forward_backward I) (backward_forward I)

theorem coefficientQuotientEquiv_mk (p : MvPolynomial α R) :
    coefficientQuotientEquiv I (Ideal.Quotient.mk (coefficientIdeal I) p) =
      MvPolynomial.map (Ideal.Quotient.mk I) p := rfl

theorem transport_ideal (J : Ideal (MvPolynomial α R)) :
    (J.map (Ideal.Quotient.mk (coefficientIdeal I))).map
      (coefficientQuotientEquiv I).toRingHom = J.map (MvPolynomial.map (Ideal.Quotient.mk I)) := by
  rw [Ideal.map_map]
  congr 1

/-- Impose both the original polynomial equations and a closed coefficient
locus, in either order, with all maps between the actual quotient rings. -/
noncomputable def closedLocusEquiv (J : Ideal (MvPolynomial α R)) :
    ((MvPolynomial α R ⧸ J) ⧸
      (coefficientIdeal I).map (Ideal.Quotient.mk J)) ≃+*
      (MvPolynomial α (R ⧸ I) ⧸ J.map (MvPolynomial.map (Ideal.Quotient.mk I))) :=
  (DoubleQuot.quotQuotEquivComm J (coefficientIdeal I)).trans
    (Ideal.quotientEquiv _ _ (coefficientQuotientEquiv I) (transport_ideal I J).symm)

theorem closedLocusEquiv_generator (J : Ideal (MvPolynomial α R)) (p : MvPolynomial α R) :
    closedLocusEquiv I J
      (Ideal.Quotient.mk ((coefficientIdeal I).map (Ideal.Quotient.mk J))
        (Ideal.Quotient.mk J p)) =
      Ideal.Quotient.mk (J.map (MvPolynomial.map (Ideal.Quotient.mk I)))
        (MvPolynomial.map (Ideal.Quotient.mk I) p) := by
  change closedLocusEquiv I J (DoubleQuot.quotQuotMk J (coefficientIdeal I) p) = _
  simp only [closedLocusEquiv, RingEquiv.trans_apply,
    DoubleQuot.quotQuotEquivComm_quotQuotMk, Ideal.quotientEquiv_apply,
    Ideal.quotientMap_mk, coefficientQuotientEquiv_mk]
  rfl

open Verification.StratumPresentation
variable {S ι κ : Type*} [CommRing S]

theorem map_exchangeIdeal (f : R →+* S) (x g : (ι ⊕ κ) → R) :
    (exchangeIdeal x g).map (MvPolynomial.map f) =
      exchangeIdeal (fun v => f (x v)) (fun v => f (g v)) := by
  rw [exchangeIdeal, Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext v
  simp [Function.comp_def, exchangeRelation]

noncomputable def exchangeClosedLocusEquiv (x g : (ι ⊕ κ) → R) :
    ((MvPolynomial (ι ⊕ κ) R ⧸ exchangeIdeal x g) ⧸
      (coefficientIdeal I).map (Ideal.Quotient.mk (exchangeIdeal x g))) ≃+*
      (MvPolynomial (ι ⊕ κ) (R ⧸ I) ⧸
        exchangeIdeal (fun v => Ideal.Quotient.mk I (x v))
          (fun v => Ideal.Quotient.mk I (g v))) :=
  (closedLocusEquiv I (exchangeIdeal x g)).trans
    (Ideal.quotEquivOfEq (map_exchangeIdeal (Ideal.Quotient.mk I) x g))

theorem exchangeClosedLocusEquiv_generator (x g : (ι ⊕ κ) → R)
    (p : MvPolynomial (ι ⊕ κ) R) :
    exchangeClosedLocusEquiv I x g
      (Ideal.Quotient.mk ((coefficientIdeal I).map (Ideal.Quotient.mk (exchangeIdeal x g)))
        (Ideal.Quotient.mk (exchangeIdeal x g) p)) =
      Ideal.Quotient.mk (exchangeIdeal (fun v => Ideal.Quotient.mk I (x v))
        (fun v => Ideal.Quotient.mk I (g v)))
        (MvPolynomial.map (Ideal.Quotient.mk I) p) := by
  rw [exchangeClosedLocusEquiv, RingEquiv.trans_apply, closedLocusEquiv_generator]
  rfl

#print axioms coefficientIdeal
#print axioms CoefficientQuotient
#print axioms coefficientIdeal_le_kernel
#print axioms forward
#print axioms coefficientLift
#print axioms backward
#print axioms backward_C
#print axioms backward_X
#print axioms forward_backward
#print axioms backward_forward
#print axioms coefficientQuotientEquiv
#print axioms coefficientQuotientEquiv_mk
#print axioms transport_ideal
#print axioms closedLocusEquiv
#print axioms closedLocusEquiv_generator
#print axioms map_exchangeIdeal
#print axioms exchangeClosedLocusEquiv
#print axioms exchangeClosedLocusEquiv_generator
end Verification.PolynomialQuotient
