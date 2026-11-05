/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SingleLaurent
import Verification.ProductTorusAlgebra
import Verification.PrimitiveCharacters

/-!
# Single Laurent Group Algebra

The principal localization in one variable is the group algebra
of the integer character lattice. This identifies the actual principal
open used in localization with a split torus factor.
-/
noncomputable section
namespace Verification.SingleLaurentGroupAlgebra
open Verification.SingleLaurent
variable (R : Type) [CommRing R]

abbrev GroupRing := MonoidAlgebra R (Multiplicative ℤ)

def groupUnit : (GroupRing R)ˣ :=
  (MonoidAlgebra.of R (Multiplicative ℤ)).toHomUnits (Multiplicative.ofAdd 1)

def forward : Laurent R →ₐ[R] GroupRing R :=
  lift (Algebra.ofId R _) (groupUnit R)

def backwardCharacter : Multiplicative ℤ →* Laurent R where
  toFun z := ((parameterUnit R) ^ Multiplicative.toAdd z : (Laurent R)ˣ)
  map_one' := by simp
  map_mul' a b := by simp [zpow_add]

def backward : GroupRing R →ₐ[R] Laurent R :=
  MonoidAlgebra.lift R (Multiplicative ℤ) _ (backwardCharacter R)

theorem backward_of (z : ℤ) :
    backward R (MonoidAlgebra.of R (Multiplicative ℤ) (Multiplicative.ofAdd z)) =
      ((parameterUnit R) ^ z : (Laurent R)ˣ) :=
  MonoidAlgebra.lift_of _ _

theorem backward_forward : (backward R).comp (forward R) = AlgHom.id R _ := by
  apply hom_ext
  · intro r
    simp only [AlgHom.comp_apply,AlgHom.commutes,AlgHom.id_apply]
  · change backward R (lift (Algebra.ofId R _) (groupUnit R) (parameter R)) = parameter R
    rw [lift_parameter]
    change backward R (MonoidAlgebra.of R (Multiplicative ℤ) (Multiplicative.ofAdd 1)) = _
    rw [backward_of,zpow_one,parameterUnit_val]

theorem forward_backward : (forward R).comp (backward R) = AlgHom.id R _ := by
  apply MonoidAlgebra.algHom_ext
  intro z
  change forward R (backward R (MonoidAlgebra.of R (Multiplicative ℤ) z)) =
    MonoidAlgebra.of R (Multiplicative ℤ) z
  have hb := backward_of R (Multiplicative.toAdd z)
  simp only [ofAdd_toAdd] at hb
  rw [hb]
  have hu : Units.map (forward R).toMonoidHom (parameterUnit R) = groupUnit R := by
    apply Units.ext
    change forward R (parameterUnit R : Laurent R) = _
    rw [parameterUnit_val]
    exact lift_parameter _ _
  change (Units.map (forward R).toMonoidHom (parameterUnit R ^ Multiplicative.toAdd z) : GroupRing R) = _
  rw [map_zpow,hu]
  rw [groupUnit,← map_zpow,MonoidHom.coe_toHomUnits]
  congr 1
  rw [← ofAdd_zsmul]
  simp

def equiv : Laurent R ≃ₐ[R] GroupRing R :=
  AlgEquiv.ofAlgHom (forward R) (backward R) (forward_backward R) (backward_forward R)

#print axioms GroupRing
#print axioms groupUnit
#print axioms forward
#print axioms backwardCharacter
#print axioms backward
#print axioms backward_of
#print axioms backward_forward
#print axioms forward_backward
#print axioms equiv
end Verification.SingleLaurentGroupAlgebra
