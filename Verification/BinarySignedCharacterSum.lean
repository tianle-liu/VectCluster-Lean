/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.BinaryIntegralCharacters

/-!
# Binary Signed Character Sum

The normal generators have character value 1, so only the column
coordinates contribute to the sign of a translated character fiber.
-/
noncomputable section
open scoped Classical
namespace Verification.BinarySignedCharacterSum
variable {ι : Type*} [Fintype ι]

def right : Multiplicative (ι → ZMod 2) →* Multiplicative ((ι ⊕ ι) → ZMod 2) :=
  (((LinearEquiv.sumArrowLequivProdArrow ι ι (ZMod 2) (ZMod 2)).symm.toLinearMap.comp
    (LinearMap.inr (ZMod 2) (ι → ZMod 2) (ι → ZMod 2))).toAddMonoidHom.toMultiplicative)

omit [Fintype ι] in
theorem right_single (i : ι) : right (Multiplicative.ofAdd (Pi.single i 1)) =
    Multiplicative.ofAdd (Pi.single (Sum.inr i) 1) := by
  apply Multiplicative.toAdd.injective
  funext j
  cases j <;> simp [right,Pi.single_apply]

theorem character_right :
    (BinarySignedFiber.character (Sum.elim (fun _ : ι => 1) (fun _ : ι => (-1:ℤˣ)))).comp right =
      BinarySignedFiber.character (fun _ : ι => (-1:ℤˣ)) := by
  apply SquareClassCharacter.hom_ext
  intro i
  change BinarySignedFiber.character _ (right (Multiplicative.ofAdd (Pi.single i 1))) = _
  rw [right_single,BinarySignedFiber.character_single]
  have h := BinarySignedFiber.character_single
    (Sum.elim (fun _ : ι => (1:ℤˣ)) (fun _ : ι => (-1:ℤˣ))) (Sum.inr i)
  convert h using 1
  congr 1
  apply congrArg Multiplicative.ofAdd
  funext j
  simp [Pi.single_apply]

theorem character_right_cast (x : ι →₀ ℤ) :
    BinarySignedFiber.character (Sum.elim (fun _ : ι => 1) (fun _ : ι => (-1:ℤˣ)))
      (Multiplicative.ofAdd (Sum.elim (fun _ => 0) (fun i => (x i : ZMod 2)))) =
      PrimitiveCharacters.basisCharacter Finsupp.basisSingleOne (fun _ : ι => (-1:ℤˣ))
        (Multiplicative.ofAdd x) := by
  have h := DFunLike.congr_fun (character_right (ι := ι))
    (BinaryIntegralCharacters.reduction (Multiplicative.ofAdd x))
  exact h.trans (DFunLike.congr_fun (BinaryIntegralCharacters.signed_compatible
    (fun _ : ι => (-1:ℤˣ))) (Multiplicative.ofAdd x))

#print axioms right
#print axioms right_single
#print axioms character_right
#print axioms character_right_cast
end Verification.BinarySignedCharacterSum
