/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LocalExchangeSmooth
import Verification.TranslatedStratum
import Mathlib.Tactic.Ring

/-!
# Rescale Exchange

Remove the explicit unit multiplying 1+chi in each remaining exchange
equation. Only the y-partner is rescaled, and every original x-coordinate
is fixed by the actual quotient algebra equivalence.
-/

noncomputable section
universe u
namespace Verification.RescaleExchange
open MvPolynomial
variable {R ι : Type u} [CommRing R]

def scaleHom (a : ι → Rˣ) : MvPolynomial (ι ⊕ ι) R →ₐ[R] MvPolynomial (ι ⊕ ι) R :=
  aeval (Sum.elim (fun i => X (Sum.inl i)) (fun i => C (a i : R) * X (Sum.inr i)))

theorem scaleHom_C (a : ι → Rˣ) (r : R) : scaleHom a (C r) = C r := by simp [scaleHom]

theorem scaleHom_X_left (a : ι → Rˣ) (i : ι) : scaleHom a (X (Sum.inl i)) = X (Sum.inl i) := by
  simp [scaleHom]

theorem scaleHom_X_right (a : ι → Rˣ) (i : ι) :
    scaleHom a (X (Sum.inr i)) = C (a i : R) * X (Sum.inr i) := by simp [scaleHom]

theorem scaleHom_inv_comp (a : ι → Rˣ) :
    (scaleHom (fun i => (a i)⁻¹)).comp (scaleHom a) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro v
  cases v with
  | inl i => simp [AlgHom.comp_apply, scaleHom_X_left]
  | inr i =>
    simp only [AlgHom.comp_apply, scaleHom_X_right, map_mul, scaleHom_C, AlgHom.id_apply]
    rw [← mul_assoc, ← C_mul]
    simp

theorem scaleHom_comp_inv (a : ι → Rˣ) :
    (scaleHom a).comp (scaleHom (fun i => (a i)⁻¹)) = AlgHom.id R _ := by
  simpa only [inv_inv] using scaleHom_inv_comp (fun i => (a i)⁻¹)

def scaleEquiv (a : ι → Rˣ) : MvPolynomial (ι ⊕ ι) R ≃ₐ[R] MvPolynomial (ι ⊕ ι) R :=
  AlgEquiv.ofAlgHom (scaleHom a) (scaleHom (fun i => (a i)⁻¹))
    (scaleHom_comp_inv a) (scaleHom_inv_comp a)

def rawRelation (a χ : ι → Rˣ) (i : ι) : MvPolynomial (ι ⊕ ι) R :=
  X (Sum.inl i) * X (Sum.inr i) - C (a i : R) * (1 + C (χ i : R))

def rawRelations (a χ : ι → Rˣ) : Ideal (MvPolynomial (ι ⊕ ι) R) :=
  Ideal.span (Set.range (rawRelation a χ))

theorem scale_relation (a χ : ι → Rˣ) (i : ι) :
    scaleEquiv a (rawRelation a χ i) = C (a i : R) * LocalExchangeSmooth.relation χ i := by
  change scaleHom a (rawRelation a χ i) = _
  simp only [rawRelation, map_sub, map_mul, scaleHom_X_left, scaleHom_X_right,
    map_add, map_one, scaleHom_C, LocalExchangeSmooth.relation]
  ring

theorem map_rawRelations (a χ : ι → Rˣ) :
    (rawRelations a χ).map (scaleEquiv a).toRingHom = LocalExchangeSmooth.relations χ := by
  rw [rawRelations, Ideal.map_span, ← Set.range_comp]
  have h : (fun i => scaleEquiv a (rawRelation a χ i)) =
      fun i => C (a i : R) * LocalExchangeSmooth.relation χ i := funext (scale_relation a χ)
  change Ideal.span (Set.range (fun i => scaleEquiv a (rawRelation a χ i))) = _
  rw [h]
  exact Verification.TranslatedStratum.unit_scaled_span
    (fun i => Units.map (C : R →+* MvPolynomial (ι ⊕ ι) R).toMonoidHom (a i))
    (LocalExchangeSmooth.relation χ)

def quotientEquiv (a χ : ι → Rˣ) :
    (MvPolynomial (ι ⊕ ι) R ⧸ rawRelations a χ) ≃ₐ[R] LocalExchangeSmooth.LocalAlgebra χ :=
  Ideal.quotientEquivAlg _ _ (scaleEquiv a) (map_rawRelations a χ).symm

theorem quotientEquiv_X_left (a χ : ι → Rˣ) (i : ι) :
    quotientEquiv a χ (Ideal.Quotient.mk (rawRelations a χ) (X (Sum.inl i))) =
      LocalExchangeSmooth.x χ i := by
  change Ideal.Quotient.mk (LocalExchangeSmooth.relations χ) (scaleHom a (X (Sum.inl i))) = _
  rw [scaleHom_X_left]
  rfl

#print axioms scaleHom
#print axioms scaleHom_C
#print axioms scaleHom_X_left
#print axioms scaleHom_X_right
#print axioms scaleHom_inv_comp
#print axioms scaleHom_comp_inv
#print axioms scaleEquiv
#print axioms rawRelation
#print axioms rawRelations
#print axioms scale_relation
#print axioms map_rawRelations
#print axioms quotientEquiv
#print axioms quotientEquiv_X_left
end Verification.RescaleExchange
