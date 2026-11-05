/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OrderedLaurentUnits
import Verification.ScalarGlobalUnits
import Mathlib.Data.Finsupp.Lex

/-!
# Finsupp Laurent Units

The Laurent-unit hypothesis used by the original global-unit
argument is now proved over any domain. A lexicographic order gives the
one-monomial theorem; the actual original Laurent generators give its
constant-times-integer-powers expression. No unit classification remains
an external premise in this result.
-/
noncomputable section
namespace Verification.FinsuppLaurentUnits
open scoped BigOperators
open Verification.ScalarGlobalUnits
variable (R κ : Type) [CommRing R] [Fintype κ]

local instance lexOrdered [LinearOrder κ] : IsOrderedAddMonoid (Lex (κ→₀ℤ)) where
  add_le_add_left _ _ h c := add_le_add_left h c

theorem exponent_expansion (a : κ→₀ℤ) :
    (∏ i,Multiplicative.ofAdd (Finsupp.single i (1:ℤ)) ^ a i)=Multiplicative.ofAdd a := by
  classical
  simp only [← ofAdd_zsmul,← ofAdd_sum]
  congr 1
  ext i
  simp [Finsupp.single_apply]

theorem unit_product (a : κ→₀ℤ) :
    (∏ i,laurentVariable R κ i ^ a i)=
      (MonoidAlgebra.of R (Multiplicative (κ→₀ℤ))).toHomUnits (Multiplicative.ofAdd a) := by
  change (∏ i,(MonoidAlgebra.of R (Multiplicative (κ→₀ℤ))).toHomUnits
    (Multiplicative.ofAdd (Finsupp.single i 1)) ^ a i)=_
  simp only [← map_zpow,← map_prod,exponent_expansion]

variable [IsDomain R]

theorem unit_monomial (u : (OriginalTorus.Torus R κ)ˣ) :
    ∃ (a : κ→₀ℤ) (c : Rˣ),(u : OriginalTorus.Torus R κ)=
      Finsupp.single (Multiplicative.ofAdd a) (c : R) := by
  classical
  letI : LinearOrder κ := LinearOrder.lift' (Fintype.equivFin κ) (Fintype.equivFin κ).injective
  exact OrderedLaurentUnits.unit_monomial (A := Lex (κ→₀ℤ)) u

theorem classification : LaurentUnitClassification R κ := by
  intro u
  obtain ⟨a,c,ha⟩ := unit_monomial R κ u
  refine ⟨c,fun i => a i,?_⟩
  apply Units.ext
  rw [unit_product]
  change (u : OriginalTorus.Torus R κ)=
    (MonoidAlgebra.single 1 (c:R) : OriginalTorus.Torus R κ)*
      MonoidAlgebra.single (Multiplicative.ofAdd a) (1:R)
  rw [ha,MonoidAlgebra.single_mul_single,one_mul,mul_one]

#print axioms lexOrdered
#print axioms exponent_expansion
#print axioms unit_product
#print axioms unit_monomial
#print axioms classification
end Verification.FinsuppLaurentUnits
