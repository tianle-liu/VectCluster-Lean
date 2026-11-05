/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualOldTorusSmooth

/-!
# Scaled Polynomial Projection

The quotient by the original affine partners is the coefficient algebra,
even when the chosen affine chart scales every partner by a coefficient unit.
-/
noncomputable section
namespace Verification.ScaledPolynomialProjection
open MvPolynomial
variable {R A S μ : Type} [CommRing R] [CommRing A] [CommRing S]
variable [Algebra R A] [Algebra R S]

theorem scaled_span (u : μ → Sˣ) :
    Ideal.span (Set.range (fun i => C (u i : S)*X i : μ → MvPolynomial μ S))=
      Ideal.span (Set.range (fun i : μ => (X i : MvPolynomial μ S))) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i))
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    have h := Ideal.mul_mem_left
      (Ideal.span (Set.range (fun i => C (u i : S)*X i : μ → MvPolynomial μ S)))
      (C ((u i)⁻¹ : Sˣ)) (Ideal.subset_span (Set.mem_range_self i))
    simpa only [← mul_assoc,← map_mul,Units.inv_mul,map_one,one_mul] using h

variable (e : A ≃ₐ[R] MvPolynomial μ S) (p : μ → A) (u : μ → Sˣ)
variable (h : ∀ i, e (p i)=C (u i : S)*X i)

def projection : A →ₐ[R] S := (PolynomialSectionIso.zeroEvaluation R S μ).comp e.toAlgHom

include h in
theorem span_map : (Ideal.span (Set.range p)).map e.toRingEquiv.toRingHom=
    RingHom.ker (PolynomialSectionIso.zeroEvaluation R S μ).toRingHom := by
  rw [Ideal.map_span,← Set.range_comp,ActualOldTorusSmooth.evaluation_kernel]
  have he : (fun i => e (p i))=(fun i => C (u i : S)*X i) := funext h
  change Ideal.span (Set.range (fun i => e (p i)))=_
  rw [he,scaled_span]

theorem projection_surjective : Function.Surjective (projection e) := by
  intro a
  refine ⟨e.symm (C a),?_⟩
  change PolynomialSectionIso.zeroEvaluation R S μ (e (e.symm (C a)))=a
  rw [e.apply_symm_apply]
  exact MvPolynomial.aeval_C _ _

def quotientEquiv : (A ⧸ Ideal.span (Set.range p)) ≃ₐ[R] S :=
  (Ideal.quotientEquivAlg _ _ e (span_map e p u h).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f:=PolynomialSectionIso.zeroEvaluation R S μ)
      (fun a => ⟨C a,MvPolynomial.aeval_C _ _⟩))

theorem quotientEquiv_mk (a : A) :
    quotientEquiv e p u h (Ideal.Quotient.mk (Ideal.span (Set.range p)) a)=projection e a := by
  rfl

#print axioms scaled_span
#print axioms projection
#print axioms span_map
#print axioms projection_surjective
#print axioms quotientEquiv
#print axioms quotientEquiv_mk
end Verification.ScaledPolynomialProjection
