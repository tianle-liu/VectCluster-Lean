/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ProductTorusAlgebra
import Verification.PrimitiveCharacters
import Verification.LocalExchangeTransport
import Verification.UniversalExchangeChart

/-!
# Primitive Exchange Split

The AS character splitting puts the entire local exchange chart into
the actual universal polynomial chart over the complementary torus.
-/
noncomputable section
namespace Verification.PrimitiveExchangeSplit
open MonoidAlgebra Verification.CharacterMapSmooth Verification.LocalExchangeSmooth
variable (R : Type) [CommRing R]
variable {M Q ι : Type} [AddCommGroup M] [AddCommGroup Q]

def coefficientEquiv (e : M ≃ₗ[ℤ] ((ι →₀ ℤ) × Q)) :
    Torus R M ≃ₐ[R] Torus (Torus R Q) (ι →₀ ℤ) :=
  (domCongr R R (PrimitiveCharacters.groupSplitting e)).trans
    (ProductTorusAlgebra.equiv R (Multiplicative (ι →₀ ℤ)) (Multiplicative Q))

theorem coefficient_monomial (e : M ≃ₗ[ℤ] ((ι →₀ ℤ) × Q)) (m : M) :
    coefficientEquiv R e (of R (Multiplicative M) (Multiplicative.ofAdd m))=
      algebraMap (Torus R Q) (Torus (Torus R Q) (ι →₀ ℤ))
        (of R (Multiplicative Q) (Multiplicative.ofAdd (e m).2))*
          of (Torus R Q) (Multiplicative (ι →₀ ℤ)) (Multiplicative.ofAdd (e m).1) := by
  change ProductTorusAlgebra.forward R (Multiplicative (ι →₀ ℤ)) (Multiplicative Q)
    ((domCongr R R (PrimitiveCharacters.groupSplitting e))
      (Finsupp.single (Multiplicative.ofAdd m) 1))=_
  rw [domCongr_single]
  exact ProductTorusAlgebra.forward_of R _ _ _ _

variable (f : (ι →₀ ℤ) →ₗ[ℤ] M) (e : M ≃ₗ[ℤ] ((ι →₀ ℤ) × Q))
variable (he : ∀ p,e (f p)=(p,0))

include he in
theorem coefficient_column (i : ι) :
    coefficientEquiv R e (characterUnits R f i : Torus R M)=
      (UniversalExchangeChart.targetUnit (Torus R Q) ι i : Torus (Torus R Q) (ι →₀ ℤ)) := by
  change coefficientEquiv R e (of R (Multiplicative M)
    (Multiplicative.ofAdd (f (Finsupp.single i 1))))=_
  rw [coefficient_monomial,he]
  simp only [Prod.fst,Prod.snd]
  rw [show Multiplicative.ofAdd (0 : Q)=(1 : Multiplicative Q) from rfl,map_one,map_one,one_mul]
  rfl

def localEquiv : LocalAlgebra (characterUnits R f) ≃ₐ[R]
    UniversalExchangeChart.Universal (Torus R Q) ι :=
  LocalExchangeTransport.localEquiv (coefficientEquiv R e) (characterUnits R f)
    (UniversalExchangeChart.targetUnit (Torus R Q) ι) (coefficient_column R f e he)

def chartEquiv : LocalAlgebra (characterUnits R f) ≃ₐ[R]
    UniversalExchangeChart.OpenPolynomial (Torus R Q) ι :=
  (localEquiv R f e he).trans
    ((UniversalExchangeChart.polynomialEquiv (Torus R Q) ι).restrictScalars R)

theorem chartEquiv_x (i : ι) :
    chartEquiv R f e he (x (characterUnits R f) i)=
      algebraMap (UniversalExchangeChart.Polynomial (Torus R Q) ι)
        (UniversalExchangeChart.OpenPolynomial (Torus R Q) ι) (MvPolynomial.X (Sum.inl i)) := by
  change UniversalExchangeChart.toPolynomial (Torus R Q) ι
    (localEquiv R f e he (x (characterUnits R f) i))=_
  rw [show localEquiv R f e he (x (characterUnits R f) i)=
    x (UniversalExchangeChart.targetUnit (Torus R Q) ι) i from
      LocalExchangeTransport.localEquiv_x _ _ _ _ i]
  exact UniversalExchangeChart.toPolynomial_x _ _ _

variable [Module.Finite ℤ M]

def asSplitting (hinj : Function.Injective f)
    (hsat : FreezingLattice.Saturated (LinearMap.range f)) :
    M ≃ₗ[ℤ] ((ι →₀ ℤ) × (M ⧸ LinearMap.range f)) :=
  (PrimitiveLattice.primitive_columns_split_compatible f hinj hsat).choose

theorem asSplitting_column (hinj : Function.Injective f)
    (hsat : FreezingLattice.Saturated (LinearMap.range f)) (p : ι →₀ ℤ) :
    asSplitting f hinj hsat (f p)=(p,0) :=
  (PrimitiveLattice.primitive_columns_split_compatible f hinj hsat).choose_spec p

def asChart (hinj : Function.Injective f)
    (hsat : FreezingLattice.Saturated (LinearMap.range f)) :
    LocalAlgebra (characterUnits R f) ≃ₐ[R]
      UniversalExchangeChart.OpenPolynomial (Torus R (M ⧸ LinearMap.range f)) ι :=
  chartEquiv R f (asSplitting f hinj hsat) (asSplitting_column f hinj hsat)

theorem asChart_x (hinj : Function.Injective f)
    (hsat : FreezingLattice.Saturated (LinearMap.range f)) (i : ι) :
    asChart R f hinj hsat (x (characterUnits R f) i)=
      algebraMap (UniversalExchangeChart.Polynomial (Torus R (M ⧸ LinearMap.range f)) ι)
        (UniversalExchangeChart.OpenPolynomial (Torus R (M ⧸ LinearMap.range f)) ι)
          (MvPolynomial.X (Sum.inl i)) :=
  chartEquiv_x R f (asSplitting f hinj hsat) (asSplitting_column f hinj hsat) i

#print axioms coefficientEquiv
#print axioms coefficient_monomial
#print axioms coefficient_column
#print axioms localEquiv
#print axioms chartEquiv
#print axioms chartEquiv_x
#print axioms asSplitting
#print axioms asSplitting_column
#print axioms asChart
#print axioms asChart_x
end Verification.PrimitiveExchangeSplit
