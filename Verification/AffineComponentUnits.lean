/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.IntegralPolynomialUnits
import Verification.ComponentLaurentUnits

/-!
# Affine Component Units

An explicit unit-group equivalence for an affine space over a finite
union of split tori. Affine variables disappear by a proved degree
argument; every component retains its unique constant and Laurent powers.
The equivalence can be transported along an actual ring isomorphism.
-/
noncomputable section
namespace Verification.AffineComponentUnits
variable {J : Type} (R : J→Type) [∀ j,CommRing (R j)] [∀ j,IsDomain (R j)]
variable (ι κ : Type) [Fintype ι] [Fintype κ]

abbrev Ring := ∀ j,MvPolynomial ι (OriginalTorus.Torus (R j) κ)

def toLaurent : (Ring R ι κ)ˣ ≃* (ComponentLaurentUnits.Ring R κ)ˣ :=
  MulEquiv.piUnits.trans ((MulEquiv.piCongrRight (fun j =>
    (IntegralPolynomialUnits.unitEquiv (OriginalTorus.Torus (R j) κ) ι).symm)).trans
      MulEquiv.piUnits.symm)

def coordinates : (Ring R ι κ)ˣ ≃* ∀ j,(R j)ˣ × Multiplicative (κ→₀ℤ) :=
  (toLaurent R ι κ).trans (MulEquiv.piUnits.trans
    (MulEquiv.piCongrRight (fun j => (LaurentUnitCoordinates.coordinateEquiv (R j) κ).symm)))

def exponents : (Ring R ι κ)ˣ →* (J→Multiplicative (κ→₀ℤ)) :=
  (ComponentLaurentUnits.exponents R κ).comp (toLaurent R ι κ).toMonoidHom

def realize : (J→Multiplicative (κ→₀ℤ)) →* (Ring R ι κ)ˣ :=
  (toLaurent R ι κ).symm.toMonoidHom.comp (ComponentLaurentUnits.realize R κ)

theorem exponents_realize (z : J→Multiplicative (κ→₀ℤ)) :
    exponents R ι κ (realize R ι κ z)=z := by
  simp only [exponents,realize,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply,ComponentLaurentUnits.exponents_realize]

def transportCoordinates {A : Type} [CommRing A] (e : A≃+*Ring R ι κ) :
    Aˣ ≃* ∀ j,(R j)ˣ × Multiplicative (κ→₀ℤ) :=
  (Units.mapEquiv e.toMulEquiv).trans (coordinates R ι κ)

#print axioms Ring
#print axioms toLaurent
#print axioms coordinates
#print axioms exponents
#print axioms realize
#print axioms exponents_realize
#print axioms transportCoordinates
end Verification.AffineComponentUnits
