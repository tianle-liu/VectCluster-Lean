/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LaurentPolynomialUniversal

/-!
# Laurent Sign Change

The genuine Laurent coordinate change u ↦ (-1)^w u, with coefficient
algebra fixed and square the identity.
-/
noncomputable section
namespace Verification.LaurentSignChange
open Verification.LaurentPolynomialUniversal
variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (w : ℕ)

def map : Laurent S →ₐ[R] Laurent S :=
  lift (IsScalarTower.toAlgHom R S (Laurent S)) ((-1)^w*parameterUnit S)

theorem coefficient (a : S) : map R S w (algebraMap S (Laurent S) a)=algebraMap S (Laurent S) a :=
  lift_coefficient _ _ a

theorem parameter : map R S w (LaurentPolynomialUniversal.parameter S)=
    (-1)^w*LaurentPolynomialUniversal.parameter S := by
  rw [map,lift_parameter,Units.val_mul,Units.val_pow_eq_pow_val,Units.val_neg,Units.val_one,parameterUnit_val]

theorem square : (map R S w).comp (map R S w)=AlgHom.id R _ := by
  apply hom_ext
  · intro a
    change map R S w (map R S w (algebraMap S (Laurent S) a))=algebraMap S (Laurent S) a
    rw [coefficient,coefficient]
  · change map R S w (map R S w (LaurentPolynomialUniversal.parameter S))=LaurentPolynomialUniversal.parameter S
    rw [parameter,map_mul,map_pow,map_neg,map_one,parameter,← mul_assoc,← mul_pow]
    simp

#print axioms map
#print axioms coefficient
#print axioms parameter
#print axioms square
end Verification.LaurentSignChange
