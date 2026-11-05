/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.NatComplexIntegerExtension
import Verification.SmithComplex

/-!
# Nat Complex Integer Free

Extension by zero retains genuine degreewise finite free modules,
so the existing simultaneous Smith construction applies to a natural
cochain complex without adding any normal-form input.
-/
noncomputable section
namespace Verification.NatComplexIntegerFree
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
open Verification.NatComplexIntegerExtension
variable {R : Type} [CommRing R]
variable (C : CochainComplex (ModuleCat.{0} R) ℕ)

/-- Every negative degree is the actual zero module. -/
def negativeIso (z : ℤ) (hz : z < 0) : (extended C).X z ≅ ModuleCat.of R PUnit :=
  (C.isZero_extend_X ComplexShape.embeddingUpNat z (by intro i; change (i : ℤ) ≠ z; omega)).iso
    (ModuleCat.isZero_of_subsingleton (ModuleCat.of R PUnit))

variable [∀ p, Module.Free R (C.X p)] [∀ p, Module.Finite R (C.X p)]

def free (z : ℤ) : Module.Free R ((extended C).X z) := by
  by_cases hz : 0 ≤ z
  · exact Module.Free.of_equiv ((C.extendXIso ComplexShape.embeddingUpNat
      (show (z.toNat : ℤ) = z from Int.toNat_of_nonneg hz)).symm.toLinearEquiv)
  · exact Module.Free.of_equiv ((negativeIso C z (by omega)).symm.toLinearEquiv)

def finite (z : ℤ) : Module.Finite R ((extended C).X z) := by
  by_cases hz : 0 ≤ z
  · exact Module.Finite.equiv ((C.extendXIso ComplexShape.embeddingUpNat
      (show (z.toNat : ℤ) = z from Int.toNat_of_nonneg hz)).symm.toLinearEquiv)
  · exact Module.Finite.equiv ((negativeIso C z (by omega)).symm.toLinearEquiv)

#print axioms negativeIso
#print axioms free
#print axioms finite
end Verification.NatComplexIntegerFree
