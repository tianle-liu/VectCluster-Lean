/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SquareClassCharacter
import Verification.PrimitiveCharacters

/-!
# Binary Integral Characters

Reduction of integral characters with involutive values.
-/
noncomputable section
open scoped Classical
namespace Verification.BinaryIntegralCharacters
variable {ι : Type*} [Fintype ι]

def reduce : (ι →₀ ℤ) →+ (ι → ZMod 2) where
  toFun x i := (x i : ZMod 2)
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp

omit [Fintype ι] in
theorem reduce_single (i : ι) : reduce (Finsupp.single i 1) = Pi.single i 1 := by
  funext j
  simp [reduce,Finsupp.single_apply,Pi.single_apply,apply_ite,eq_comm]

def reduction : Multiplicative (ι →₀ ℤ) →* Multiplicative (ι → ZMod 2) :=
  reduce.toMultiplicative

omit [Fintype ι] in
theorem reduction_single (i : ι) : reduction (Multiplicative.ofAdd (Finsupp.single i 1)) =
    Multiplicative.ofAdd (Pi.single i 1) := congrArg Multiplicative.ofAdd (reduce_single i)

theorem signed_compatible (u : ι → ℤˣ) :
    (BinarySignedFiber.character u).comp reduction =
      PrimitiveCharacters.basisCharacter Finsupp.basisSingleOne u := by
  apply MonoidHom.eq_of_eqOn_dense
  · exact PrimitiveCharacters.basis_generates Finsupp.basisSingleOne
  · rintro _ ⟨i,rfl⟩
    change BinarySignedFiber.character u (reduction (Multiplicative.ofAdd (Finsupp.single i 1))) = _
    rw [reduction_single,BinarySignedFiber.character_single]
    exact (PrimitiveCharacters.basisCharacter_apply Finsupp.basisSingleOne u i).symm

#print axioms reduce
#print axioms reduce_single
#print axioms reduction
#print axioms reduction_single
#print axioms signed_compatible
end Verification.BinaryIntegralCharacters
