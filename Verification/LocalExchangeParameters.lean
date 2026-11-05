/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LocalExchangeSmooth

/-!
# Local Exchange Parameters

The x-coordinate projection of the actual local exchange quotient is
smooth. Thus the coordinates are genuine simultaneous smooth parameters,
with the map to the parameter affine space explicitly identified.
The scheme normal-bundle/global gluing step is outside this module.
-/

noncomputable section
universe u
namespace Verification.LocalExchangeParameters
open MvPolynomial Verification.LocalExchangeSmooth
variable {R S κ : Type u} [CommRing R] [CommRing S] [Algebra R S]

def parameterMap (χ : κ → Sˣ) : MvPolynomial κ R →ₐ[R] LocalAlgebra χ := aeval (x χ)

instance parameterAlgebra (χ : κ → Sˣ) : Algebra (MvPolynomial κ R) (LocalAlgebra χ) :=
  (parameterMap (R := R) χ).toRingHom.toAlgebra

theorem parameter_X (χ : κ → Sˣ) (k : κ) :
    algebraMap (MvPolynomial κ R) (LocalAlgebra χ) (X k) = x χ k := aeval_X _ _

section CharacterAlgebra
variable [Algebra (Target R κ) S] [IsScalarTower R (Target R κ) S]
variable (χ : κ → Sˣ)
variable (hχ : ∀ k, algebraMap (Target R κ) S (DiagonalPowerFibers.laurentCoordinate R κ k) = χ k)
include hχ

theorem parameter_formallySmooth [Algebra.FormallySmooth (Target R κ) S] :
    Algebra.FormallySmooth (MvPolynomial κ R) (LocalAlgebra χ) := by
  constructor
  intro B _ _ J hJ f
  letI : Algebra R B := Algebra.compHom B (algebraMap R (MvPolynomial κ R))
  letI : IsScalarTower R (MvPolynomial κ R) B :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let a : κ → B := fun k => algebraMap (MvPolynomial κ R) B (X k)
  have ha (k : κ) : Ideal.Quotient.mk J (a k) = (f.restrictScalars R) (x χ k) := by
    change algebraMap (MvPolynomial κ R) (B ⧸ J) (X k) = f (x χ k)
    rw [← parameter_X (R := R) χ k, f.commutes]
  choose b hb using (fun k => Ideal.Quotient.mk_surjective ((f.restrictScalars R) (y χ k)))
  obtain ⟨g,hg,hx,_⟩ := lift_with_coordinates χ hχ J hJ (f.restrictScalars R) a b ha hb
  have hp : g.comp (parameterMap (R := R) χ) =
      IsScalarTower.toAlgHom R (MvPolynomial κ R) B := by
    apply MvPolynomial.algHom_ext
    intro k
    change g ((parameterMap (R := R) χ) (X k)) = algebraMap (MvPolynomial κ R) B (X k)
    rw [parameterMap, aeval_X]
    exact hx k
  let gP : LocalAlgebra χ →ₐ[MvPolynomial κ R] B :=
    { g.toRingHom with commutes' := fun p => AlgHom.congr_fun hp p }
  refine ⟨gP, ?_⟩
  exact AlgHom.ext (fun z => AlgHom.congr_fun hg z)

theorem parameter_smooth [Fintype κ] [Algebra.Smooth (Target R κ) S] :
    Algebra.Smooth (MvPolynomial κ R) (LocalAlgebra χ) := by
  letI := local_smooth χ hχ
  letI : Algebra.FinitePresentation (MvPolynomial κ R) (LocalAlgebra χ) :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R (MvPolynomial κ R) (LocalAlgebra χ)
  exact { formallySmooth := parameter_formallySmooth χ hχ }

end CharacterAlgebra

theorem local_character_parameters_smooth {M ι : Type u} [AddCommGroup M] [Fintype κ] [Fintype ι]
    (f : (κ →₀ ℤ) →ₗ[ℤ] M) (hf : Function.Injective f)
    {n : ℕ} (s : Basis.SmithNormalForm (LinearMap.range f) ι n)
    (he : ∀ i, IsUnit ((s.a i).natAbs : R)) :
    Algebra.Smooth (MvPolynomial κ R) (LocalAlgebra (characterUnits R f)) := by
  letI := (CharacterMapSmooth.characterMap (R := R) f).toRingHom.toAlgebra
  letI := CharacterMapSmooth.characterMap_smooth f hf Finsupp.basisSingleOne s he
  apply parameter_smooth (characterUnits R f)
  intro k
  exact CharacterMapSmooth.characterMap_monomial f (Finsupp.single k 1)

theorem local_character_parameters_smooth_charZero {k M ι : Type u} [Field k] [CharZero k]
    [AddCommGroup M] [Fintype κ] [Fintype ι]
    (bM : Basis ι ℤ M) (f : (κ →₀ ℤ) →ₗ[ℤ] M) (hf : Function.Injective f) :
    Algebra.Smooth (MvPolynomial κ k) (LocalAlgebra (characterUnits k f)) := by
  letI := (CharacterMapSmooth.characterMap (R := k) f).toRingHom.toAlgebra
  letI := CharacterMapSmooth.characterMap_smooth_charZero (k := k) bM f hf Finsupp.basisSingleOne
  apply parameter_smooth (characterUnits k f)
  intro i
  exact CharacterMapSmooth.characterMap_monomial f (Finsupp.single i 1)

#print axioms parameterMap
#print axioms parameterAlgebra
#print axioms parameter_X
#print axioms parameter_formallySmooth
#print axioms parameter_smooth
#print axioms local_character_parameters_smooth
#print axioms local_character_parameters_smooth_charZero
end Verification.LocalExchangeParameters
