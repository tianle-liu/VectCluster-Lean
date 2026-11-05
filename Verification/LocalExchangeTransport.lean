/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LocalExchangeParameters

/-!
# Local Exchange Transport

Transport of a literal local exchange quotient along a coefficient
algebra equivalence. The original and mutated coordinates are fixed, and
so is the map from the original-coordinate parameter polynomial algebra.
-/
noncomputable section
universe u
namespace Verification.LocalExchangeTransport
open MvPolynomial Verification.LocalExchangeSmooth
variable {R S T ι : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
variable (e : S ≃ₐ[R] T) (χ : ι → Sˣ) (ψ : ι → Tˣ)
variable (he : ∀ i, e (χ i : S) = (ψ i : T))
include he

theorem map_relations : (relations χ).map (mapAlgEquiv (ι ⊕ ι) e).toRingHom = relations ψ := by
  rw [relations,Ideal.map_span,← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  change MvPolynomial.map e.toRingHom (relation χ i) = relation ψ i
  simp only [relation,map_sub,map_mul,map_one,map_C,map_X]
  change X (Sum.inl i) * X (Sum.inr i) - 1 - C (e (χ i : S)) = _
  rw [he]

def localEquiv : LocalAlgebra χ ≃ₐ[R] LocalAlgebra ψ :=
  Ideal.quotientEquivAlg _ _ (mapAlgEquiv (ι ⊕ ι) e) (map_relations e χ ψ he).symm

theorem localEquiv_x (i : ι) : localEquiv e χ ψ he (x χ i) = x ψ i := by
  change Ideal.Quotient.mk _ (MvPolynomial.map e.toRingHom (X (Sum.inl i))) = _
  rw [map_X]
  rfl

theorem localEquiv_y (i : ι) : localEquiv e χ ψ he (y χ i) = y ψ i := by
  change Ideal.Quotient.mk _ (MvPolynomial.map e.toRingHom (X (Sum.inr i))) = _
  rw [map_X]
  rfl

theorem localEquiv_coefficient (s : S) :
    localEquiv e χ ψ he (algebraMap S (LocalAlgebra χ) s) = algebraMap T (LocalAlgebra ψ) (e s) := by
  change Ideal.Quotient.mk _ (MvPolynomial.map e.toRingHom (C s)) = _
  rw [map_C]
  rfl

def parameterEquiv : LocalAlgebra χ ≃ₐ[MvPolynomial ι R] LocalAlgebra ψ :=
  AlgEquiv.ofRingEquiv (f := (localEquiv e χ ψ he).toRingEquiv) (fun p => by
    have hh : (localEquiv e χ ψ he).toAlgHom.comp (LocalExchangeParameters.parameterMap (R := R) χ) =
        LocalExchangeParameters.parameterMap (R := R) ψ := by
      apply MvPolynomial.algHom_ext
      intro i
      change localEquiv e χ ψ he ((aeval (x χ) : MvPolynomial ι R →ₐ[R] _) (X i)) =
        (aeval (x ψ) : MvPolynomial ι R →ₐ[R] _) (X i)
      rw [aeval_X,aeval_X,localEquiv_x]
    exact AlgHom.congr_fun hh p)

#print axioms map_relations
#print axioms localEquiv
#print axioms localEquiv_x
#print axioms localEquiv_y
#print axioms localEquiv_coefficient
#print axioms parameterEquiv
end Verification.LocalExchangeTransport
