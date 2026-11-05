/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ExplicitPrimitiveFiber

/-!
# Signed Primitive Fiber Units

Unit-valued monomial normalization through an arbitrary primitive
translated character-fiber quotient, including its defining-ideal transport.
-/
noncomputable section
open scoped Classical
namespace Verification.SignedPrimitiveFiberUnits
variable {R ι κ : Type*} [CommRing R] [Fintype ι] [Fintype κ]
variable (f : (ι →₀ ℤ) →ₗ[ℤ] (κ →₀ ℤ)) (hf : Function.Injective f)
variable (hs : FreezingLattice.Saturated (LinearMap.range f)) (u : ι → Rˣ)

def unit (m : κ →₀ ℤ) :
    (MonoidAlgebra R (Multiplicative (Fin (Module.finrank ℤ ((κ →₀ ℤ) ⧸ LinearMap.range f)) →₀ ℤ)))ˣ :=
  Units.map (algebraMap R _).toMonoidHom
    (PrimitiveCharacters.basisCharacter Finsupp.basisSingleOne u
      (Multiplicative.ofAdd (ExplicitPrimitiveFiber.torusSplitting f hf hs m).1)) *
    (MonoidAlgebra.of R _).toHomUnits
      (Multiplicative.ofAdd (ExplicitPrimitiveFiber.torusSplitting f hf hs m).2)

def equiv (J : Ideal (MonoidAlgebra R (Multiplicative (κ →₀ ℤ))))
    (hJ : J = PrimitiveCharacters.prescribedIdeal f Finsupp.basisSingleOne u) :
    (MonoidAlgebra R (Multiplicative (κ →₀ ℤ)) ⧸ J) ≃ₐ[R]
      MonoidAlgebra R (Multiplicative (Fin (Module.finrank ℤ ((κ →₀ ℤ) ⧸ LinearMap.range f)) →₀ ℤ)) :=
  (Ideal.quotientEquivAlgOfEq R hJ).trans
    (ExplicitPrimitiveFiber.torusEquiv f hf hs Finsupp.basisSingleOne u)

omit [Fintype ι] in
theorem monomial (J : Ideal (MonoidAlgebra R (Multiplicative (κ →₀ ℤ))))
    (hJ : J = PrimitiveCharacters.prescribedIdeal f Finsupp.basisSingleOne u) (m : κ →₀ ℤ) :
    equiv f hf hs u J hJ (Ideal.Quotient.mk J (MonoidAlgebra.of R _ (Multiplicative.ofAdd m))) =
      (unit f hf hs u m : MonoidAlgebra R _) := by
  dsimp only [equiv,AlgEquiv.trans_apply]
  rw [Ideal.quotientEquivAlgOfEq_mk]
  exact ExplicitPrimitiveFiber.torusEquiv_monomial _ _ _ _ _ _

#print axioms unit
#print axioms equiv
#print axioms monomial
end Verification.SignedPrimitiveFiberUnits
