/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.BinaryIntegralCharacters
import Verification.WittSheafAffineInvariance

/-!
# Witt Torus Characters

Ordinary torus basis on every actual integral monomial, obtained from
its coordinate normalization and the group-algebra universal property.
-/
noncomputable section
open scoped Classical
namespace Verification.WittTorusCharacters
open CategoryTheory AlgebraicGeometry Opposite
open Verification.WittSheafSectionsInput
variable (R : Type) [CommRing R] (W : Scheme.{0}ᵒᵖ ⥤ CommRingCat.{0})
variable (D : Symbols R W) (T : TorusBasis R W D)
variable (ι : Type) [Fintype ι]

def coordinateUnit (i : ι) : (OriginalTorus.Torus R ι)ˣ :=
  ((MonoidAlgebra.of R (Multiplicative (ι →₀ ℤ))).toHomUnits
    (Multiplicative.ofAdd (Finsupp.single i 1)))

def character : Multiplicative (ι → ZMod 2) →* RingSection W (OriginalTorus.Torus R ι) :=
  SquareClassCharacter.character
    (fun i => form R W D _ (TorusSmooth.torus_smooth R ι) (coordinateUnit R ι i))
    (fun i => form_square R W D _ _ (coordinateUnit R ι i))

theorem basis_monomial (a : Multiplicative (ι → ZMod 2)) :
    T.equiv ι (MonoidAlgebra.of (RingSection W R) _ a) = character R W D ι a := by
  have h : (T.equiv ι).toMonoidHom.comp (MonoidAlgebra.of (RingSection W R) _) =
      character R W D ι := by
    apply SquareClassCharacter.hom_ext
    intro i
    change T.equiv ι (MonoidAlgebra.of (RingSection W R) _
      (Multiplicative.ofAdd (Pi.single i 1))) = _
    rw [T.character]
    change form R W D _ (TorusSmooth.torus_smooth R ι) (coordinateUnit R ι i) = _
    exact (SquareClassCharacter.character_single
      (fun j => form R W D _ (TorusSmooth.torus_smooth R ι) (coordinateUnit R ι j))
      (fun j => form_square R W D _ _ (coordinateUnit R ι j)) i).symm
  exact DFunLike.congr_fun h a

theorem basis_single (a : Multiplicative (ι → ZMod 2)) (c : RingSection W R) :
    T.equiv ι (Finsupp.single a c) =
      pullback W (algebraMap R (OriginalTorus.Torus R ι)) c * character R W D ι a := by
  change T.equiv ι (MonoidAlgebra.single a c) = _
  rw [MonoidAlgebra.single_eq_algebraMap_mul_of,map_mul,T.coefficient,basis_monomial]

theorem integral_character :
    (character R W D ι).comp BinaryIntegralCharacters.reduction =
      (form R W D _ (TorusSmooth.torus_smooth R ι)).comp
        (MonoidAlgebra.of R (Multiplicative (ι →₀ ℤ))).toHomUnits := by
  apply MonoidHom.eq_of_eqOn_dense
  · exact PrimitiveCharacters.basis_generates Finsupp.basisSingleOne
  · rintro _ ⟨i,rfl⟩
    change character R W D ι
      (BinaryIntegralCharacters.reduction (Multiplicative.ofAdd (Finsupp.single i 1))) = _
    rw [BinaryIntegralCharacters.reduction_single]
    exact SquareClassCharacter.character_single _ _ i

theorem basis_integral_monomial (m : ι →₀ ℤ) :
    T.equiv ι (MonoidAlgebra.of (RingSection W R) _
      (Multiplicative.ofAdd (fun i => (m i : ZMod 2)))) =
      form R W D _ (TorusSmooth.torus_smooth R ι)
        ((MonoidAlgebra.of R (Multiplicative (ι →₀ ℤ))).toHomUnits
          (Multiplicative.ofAdd m)) := by
  rw [basis_monomial]
  exact DFunLike.congr_fun (integral_character R W D ι) (Multiplicative.ofAdd m)

#print axioms coordinateUnit
#print axioms character
#print axioms basis_monomial
#print axioms basis_single
#print axioms integral_character
#print axioms basis_integral_monomial
end Verification.WittTorusCharacters
