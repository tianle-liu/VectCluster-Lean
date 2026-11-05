/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LaurentUnitCoordinates
import Mathlib.Algebra.Group.Pi.Units

/-!
# Component Laurent Units

Laurent exponents can be prescribed independently on every connected
factor of a product of domain coefficient rings. The section is an actual
unit in the product ring, not a formal source vector for a residue matrix.
-/
noncomputable section
namespace Verification.ComponentLaurentUnits
attribute [local instance] Classical.propDecidable
variable {J : Type} (R : J→Type) [∀ j,CommRing (R j)] [∀ j,IsDomain (R j)]
variable (κ : Type) [Fintype κ]

abbrev Ring := ∀ j,OriginalTorus.Torus (R j) κ

def component (u : (Ring R κ)ˣ) (j : J) : (OriginalTorus.Torus (R j) κ)ˣ :=
  MulEquiv.piUnits u j

def exponents : (Ring R κ)ˣ →* (J → Multiplicative (κ→₀ℤ)) where
  toFun u j := LaurentUnitCoordinates.exponent (R j) κ (component R κ u j)
  map_one' := by funext j; exact map_one (LaurentUnitCoordinates.exponent (R j) κ)
  map_mul' u v := by
    funext j
    simp only [component,map_mul,Pi.mul_apply]

def realize : (J → Multiplicative (κ→₀ℤ)) →* (Ring R κ)ˣ where
  toFun z := MulEquiv.piUnits.symm (fun j => LaurentUnitCoordinates.monomial (R j) κ 1 (z j).toAdd)
  map_one' := by
    apply MulEquiv.piUnits.injective
    funext j
    apply Units.ext
    simp [LaurentUnitCoordinates.monomial]
  map_mul' z w := by
    apply MulEquiv.piUnits.injective
    funext j
    change LaurentUnitCoordinates.coordinateEquiv (R j) κ (1,z j*w j)=
      LaurentUnitCoordinates.coordinateEquiv (R j) κ (1,z j)*
        LaurentUnitCoordinates.coordinateEquiv (R j) κ (1,w j)
    simpa only [Prod.mk_mul_mk,one_mul] using
      (LaurentUnitCoordinates.coordinateEquiv (R j) κ).map_mul (1,z j) (1,w j)

theorem exponents_realize (z : J→Multiplicative (κ→₀ℤ)) :
    exponents R κ (realize R κ z)=z := by
  funext j
  exact LaurentUnitCoordinates.exponent_monomial (R j) κ 1 (z j).toAdd

theorem independent_exponents : Function.Surjective (exponents R κ) :=
  Function.HasRightInverse.surjective ⟨realize R κ,exponents_realize R κ⟩

def coordinateSelector (c : J) (i : κ) : (Ring R κ)ˣ := by
  classical
  exact realize R κ (fun j => Multiplicative.ofAdd (if j=c then Finsupp.single i 1 else 0))

theorem selector_exponent (c j : J) (i k : κ) :
    ((exponents R κ (coordinateSelector R κ c i) j).toAdd) k=
      if j=c ∧ i=k then 1 else 0 := by
  classical
  simp only [coordinateSelector,exponents_realize]
  by_cases h : j=c
  · simp [h,Finsupp.single_apply,eq_comm]
  · simp [h]

#print axioms Ring
#print axioms component
#print axioms exponents
#print axioms realize
#print axioms exponents_realize
#print axioms independent_exponents
#print axioms coordinateSelector
#print axioms selector_exponent
end Verification.ComponentLaurentUnits
