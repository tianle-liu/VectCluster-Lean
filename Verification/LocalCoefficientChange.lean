/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LocalExchangeParameters
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Local Coefficient Change

Change the actual coefficient algebra in the local exchange quotient
while preserving every original parameter.
-/
noncomputable section
universe u
namespace Verification.LocalCoefficientChange
open MvPolynomial Verification.LocalExchangeSmooth
variable {R S T ι : Type u} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]
variable (e : S ≃ₐ[R] T) (χ : ι → Sˣ) (ψ : ι → Tˣ)
variable (h : ∀ i, e (χ i : S) = (ψ i : T))
attribute [local instance] MvPolynomial.algebraMvPolynomial

include h in
theorem map_relation (i : ι) :
    mapAlgEquiv (ι ⊕ ι) e (relation χ i) = relation ψ i := by
  simp only [mapAlgEquiv_apply, relation, map_sub, map_mul, map_X, map_one, map_C]
  change X (Sum.inl i) * X (Sum.inr i) - 1 - C (e (χ i : S)) = _
  rw [h]

include h in
theorem map_relations : (relations χ).map (mapAlgEquiv (ι ⊕ ι) e).toRingHom = relations ψ := by
  rw [relations, Ideal.map_span, ← Set.range_comp]
  change Ideal.span (Set.range (fun i => mapAlgEquiv (ι ⊕ ι) e (relation χ i))) = _
  simp only [map_relation e χ ψ h]
  rfl

def quotientEquiv : LocalAlgebra χ ≃ₐ[R] LocalAlgebra ψ :=
  Ideal.quotientEquivAlg _ _ (mapAlgEquiv (ι ⊕ ι) e) (map_relations e χ ψ h).symm

theorem quotientEquiv_x (i : ι) : quotientEquiv e χ ψ h (x χ i) = x ψ i := by
  change Ideal.Quotient.mk (relations ψ) (map e.toRingHom (X (Sum.inl i))) = _
  rw [map_X]
  rfl

theorem quotientEquiv_y (i : ι) : quotientEquiv e χ ψ h (y χ i) = y ψ i := by
  change Ideal.Quotient.mk (relations ψ) (map e.toRingHom (X (Sum.inr i))) = _
  rw [map_X]
  rfl

def parameterEquiv : LocalAlgebra χ ≃ₐ[MvPolynomial ι R] LocalAlgebra ψ :=
  AlgEquiv.ofRingEquiv (f := (quotientEquiv e χ ψ h).toRingEquiv) (fun p => by
    have he : (quotientEquiv e χ ψ h).toAlgHom.comp (LocalExchangeParameters.parameterMap χ) =
        LocalExchangeParameters.parameterMap ψ := by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, LocalExchangeParameters.parameterMap, aeval_X]
      exact quotientEquiv_x e χ ψ h i
    exact AlgHom.congr_fun he p)

#print axioms map_relation
#print axioms map_relations
#print axioms quotientEquiv
#print axioms quotientEquiv_x
#print axioms quotientEquiv_y
#print axioms parameterEquiv
end Verification.LocalCoefficientChange
