/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.BinarySignedFiber
import Verification.WittSheafLaurentResidue

/-!
# Square Class Character

The character of an elementary abelian 2-group determined by
commuting involutions. This uses the literal binary exponent group.
-/
noncomputable section
open scoped Classical BigOperators
namespace Verification.SquareClassCharacter
variable {ι A : Type*} [Fintype ι] [CommMonoid A]

lemma pow_val_add (g : A) (hg : g*g=1) (a b : ZMod 2) :
    g^(a+b).val = g^a.val * g^b.val := by
  have hab : (a+b).val = (a.val+b.val)%2 := ZMod.val_add a b
  rw [hab]
  rw [← pow_add]
  exact (WittSheafLaurentResidue.involution_power g hg _).symm

def character (f : ι → A) (hf : ∀ i, f i*f i=1) :
    Multiplicative (ι → ZMod 2) →* A where
  toFun a := ∏ i, f i ^ (Multiplicative.toAdd a i).val
  map_one' := by simp
  map_mul' a b := by
    change (∏ i, f i ^ (Multiplicative.toAdd a i+Multiplicative.toAdd b i).val) = _
    simp only [pow_val_add _ (hf _),Finset.prod_mul_distrib]

theorem character_single (f : ι → A) (hf : ∀ i, f i*f i=1) (i : ι) :
    character f hf (Multiplicative.ofAdd (Pi.single i 1)) = f i := by
  simp [character,Pi.single_apply,apply_ite]
  rw [ZMod.val_one_eq_one_mod]
  simp

omit [CommMonoid A] in
theorem hom_ext {M : Type*} [Monoid M]
    (f g : Multiplicative (ι → ZMod 2) →* M)
    (h : ∀ i, f (Multiplicative.ofAdd (Pi.single i 1)) =
      g (Multiplicative.ofAdd (Pi.single i 1))) : f=g := by
  apply MonoidHom.eq_of_eqOn_dense
  · exact BinarySignedFiber.single_generates
  · rintro _ ⟨i,rfl⟩
    exact h i

#print axioms pow_val_add
#print axioms character
#print axioms character_single
#print axioms hom_ext
end Verification.SquareClassCharacter
