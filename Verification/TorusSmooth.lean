/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalTorus
import Verification.SplitExchangeChart

/-!
# Torus Smooth

Smoothness of the actual split torus group algebra, obtained from its
proved original-coordinate quotient/localization presentation.
-/
namespace Verification.TorusSmooth
open MvPolynomial Verification.StratumPresentation Verification.OriginalTorus
universe u
variable (R ι κ : Type u) [CommRing R]

noncomputable def eraseZero : OriginalQuotient R ι κ →ₐ[R] MvPolynomial κ R :=
  Ideal.Quotient.liftₐ _ (aeval (Sum.elim (fun _ => 0) X)) (by
    change zeroCoordinateIdeal R ι κ ≤ RingHom.ker _
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    simp)

noncomputable def includeRemaining : MvPolynomial κ R →ₐ[R] OriginalQuotient R ι κ :=
  (Ideal.Quotient.mkₐ R _).comp (rename Sum.inr)

theorem eraseZero_includeRemaining :
    (eraseZero R ι κ).comp (includeRemaining R ι κ) = AlgHom.id R _ := by
  ext k
  simp [eraseZero, includeRemaining]

theorem includeRemaining_eraseZero :
    (includeRemaining R ι κ).comp (eraseZero R ι κ) = AlgHom.id R _ := by
  apply Ideal.Quotient.algHom_ext
  ext v
  cases v with
  | inl i =>
    have hi : Ideal.Quotient.mk (zeroCoordinateIdeal R ι κ) (X (Sum.inl i)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
    simp [eraseZero, includeRemaining, hi]
  | inr k => simp [eraseZero, includeRemaining]

noncomputable def originalQuotientEquiv : OriginalQuotient R ι κ ≃ₐ[R] MvPolynomial κ R :=
  AlgEquiv.ofAlgHom (eraseZero R ι κ) (includeRemaining R ι κ)
    (eraseZero_includeRemaining R ι κ) (includeRemaining_eraseZero R ι κ)

variable [Fintype κ]

theorem originalQuotient_smooth : Algebra.Smooth R (OriginalQuotient R ι κ) := by
  letI : Algebra.Smooth R (MvPolynomial κ R) := {}
  exact Algebra.Smooth.of_equiv (originalQuotientEquiv R ι κ).symm

theorem originalStratum_smooth : Algebra.Smooth R (OriginalStratum R ι κ) := by
  letI : Algebra.Smooth R (OriginalQuotient R ι κ) := originalQuotient_smooth R ι κ
  letI : Algebra.Smooth (OriginalQuotient R ι κ) (OriginalStratum R ι κ) :=
    Verification.SplitExchangeChart.valueLocalization_smooth
      (fun k : κ => Ideal.Quotient.mk (zeroCoordinateIdeal R ι κ) (X (Sum.inr k)))
  exact Algebra.Smooth.comp R (OriginalQuotient R ι κ) (OriginalStratum R ι κ)

theorem torus_smooth : Algebra.Smooth R (MonoidAlgebra R (Multiplicative (κ →₀ ℤ))) := by
  letI : Algebra.Smooth R (OriginalStratum R κ κ) := originalStratum_smooth R κ κ
  exact Algebra.Smooth.of_equiv (originalTorusEquiv R κ κ)

#print axioms eraseZero
#print axioms includeRemaining
#print axioms eraseZero_includeRemaining
#print axioms includeRemaining_eraseZero
#print axioms originalQuotientEquiv
#print axioms originalQuotient_smooth
#print axioms originalStratum_smooth
#print axioms torus_smooth
end Verification.TorusSmooth
