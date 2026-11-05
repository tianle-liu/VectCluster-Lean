/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StratumPresentation

/-!
# Killed Original Polynomial

Kill only the specified original coordinates. The others remain genuine
polynomial variables; no extra invertibility or vanishing is imposed.
-/
noncomputable section
namespace Verification.KilledOriginalPolynomial
open MvPolynomial Verification.StratumPresentation
variable (R ι κ : Type*) [CommRing R]

def polynomialMap : MvPolynomial (ι ⊕ κ) R →ₐ[R] MvPolynomial κ R :=
  aeval (Sum.elim (fun _ => 0) X)

def descend : OriginalQuotient R ι κ →ₐ[R] MvPolynomial κ R :=
  Ideal.Quotient.liftₐ (zeroCoordinateIdeal R ι κ) (polynomialMap R ι κ) (by
    change zeroCoordinateIdeal R ι κ ≤ RingHom.ker (polynomialMap R ι κ).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change polynomialMap R ι κ (X (Sum.inl i)) = 0
    simp only [polynomialMap, aeval_X, Sum.elim_inl])

def includeRemaining : MvPolynomial κ R →ₐ[R] OriginalQuotient R ι κ :=
  (Ideal.Quotient.mkₐ R (zeroCoordinateIdeal R ι κ)).comp (rename Sum.inr)

theorem killed_variable (i : ι) :
    Ideal.Quotient.mk (zeroCoordinateIdeal R ι κ) (X (Sum.inl i)) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))

theorem descend_include : (descend R ι κ).comp (includeRemaining R ι κ) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro k
  simp [descend, includeRemaining, polynomialMap]

theorem include_descend : (includeRemaining R ι κ).comp (descend R ι κ) = AlgHom.id R _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro v
  cases v with
  | inl i =>
    change includeRemaining R ι κ (polynomialMap R ι κ (X (Sum.inl i))) =
      Ideal.Quotient.mk (zeroCoordinateIdeal R ι κ) (X (Sum.inl i))
    simp only [polynomialMap, aeval_X, Sum.elim_inl, map_zero, killed_variable]
  | inr k => simp [descend, includeRemaining, polynomialMap]

def quotientEquiv : OriginalQuotient R ι κ ≃ₐ[R] MvPolynomial κ R :=
  AlgEquiv.ofAlgHom (descend R ι κ) (includeRemaining R ι κ)
    (descend_include R ι κ) (include_descend R ι κ)

@[simp] theorem quotientEquiv_remaining (k : κ) :
    quotientEquiv R ι κ (Ideal.Quotient.mk (zeroCoordinateIdeal R ι κ) (X (Sum.inr k))) = X k := by
  change polynomialMap R ι κ (X (Sum.inr k)) = X k
  simp only [polynomialMap, aeval_X, Sum.elim_inr]

@[simp] theorem quotientEquiv_killed (i : ι) :
    quotientEquiv R ι κ (Ideal.Quotient.mk (zeroCoordinateIdeal R ι κ) (X (Sum.inl i))) = 0 := by
  rw [killed_variable, map_zero]

#print axioms polynomialMap
#print axioms descend
#print axioms includeRemaining
#print axioms killed_variable
#print axioms descend_include
#print axioms include_descend
#print axioms quotientEquiv
#print axioms quotientEquiv_remaining
#print axioms quotientEquiv_killed
end Verification.KilledOriginalPolynomial
