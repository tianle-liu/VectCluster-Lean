/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.WittTorusCharacters
import Verification.BinarySignedCharacterSum

/-!
# Witt Signed Characters

The translated fiber's integral sign character maps to the actual
one-dimensional Witt form, by the ordinary value of <-1>.
-/
noncomputable section
open scoped Classical
namespace Verification.WittSignedCharacters
open CategoryTheory AlgebraicGeometry Opposite
open Verification.WittSheafSectionsInput
variable (R : Type) [CommRing R] (W : Scheme.{0}ᵒᵖ ⥤ CommRingCat.{0})
variable (D : Symbols R W) (ι : Type) [Fintype ι]

def smoothBase : Algebra.Smooth R R := by
  letI : Algebra.Smooth R (MvPolynomial Empty R) := {}
  exact Algebra.Smooth.of_equiv (MvPolynomial.isEmptyAlgEquiv R Empty)

omit [Fintype ι] in
theorem scalar_character :
    (form R W D R (smoothBase R)).comp
      (PrimitiveCharacters.basisCharacter Finsupp.basisSingleOne (fun _ : ι => (-1:Rˣ))) =
    (Int.castRingHom (RingSection W R)).toMonoidHom.comp
      (Units.coeHom ℤ |>.comp
        (PrimitiveCharacters.basisCharacter Finsupp.basisSingleOne (fun _ : ι => (-1:ℤˣ)))) := by
  apply MonoidHom.eq_of_eqOn_dense
  · exact PrimitiveCharacters.basis_generates Finsupp.basisSingleOne
  · rintro _ ⟨i,rfl⟩
    simp only [MonoidHom.comp_apply,PrimitiveCharacters.basisCharacter_apply,form_negative_one]
    simp

omit [Fintype ι] in
theorem scalar_character_apply (x : ι →₀ ℤ) :
    form R W D R (smoothBase R)
      (PrimitiveCharacters.basisCharacter Finsupp.basisSingleOne (fun _ : ι => (-1:Rˣ))
        (Multiplicative.ofAdd x)) =
      ((PrimitiveCharacters.basisCharacter Finsupp.basisSingleOne (fun _ : ι => (-1:ℤˣ))
        (Multiplicative.ofAdd x) : ℤ) : RingSection W R) :=
  DFunLike.congr_fun (scalar_character R W D ι) (Multiplicative.ofAdd x)

#print axioms smoothBase
#print axioms scalar_character
#print axioms scalar_character_apply
end Verification.WittSignedCharacters
