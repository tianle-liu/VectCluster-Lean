/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOriginalStrictCells
import Verification.PathCanonicalCoefficientSection
import Verification.PathYWordBasis
import Verification.PathZWordBasis
import Verification.StrictTorusSymbolInput

/-!
# Path Original Strict Coordinate Units

The standard torus coordinates of the actual path strict cells are
exactly the canonical fiber's signed original units under its actual section.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.PathOriginalStrictCoordinateUnits
open Classical CategoryTheory AlgebraicGeometry
open Verification.PathCompression Verification.PathSignedStratumCoefficients
open Verification.PathClassRepresentatives Verification.PathCanonicalCoefficientSection
variable (R : Type) [CommRing R]

section Y
variable {d : ℕ} {I : Finset ℕ} (hI : Admissible (2*d) I)
local notation "μ" => PathEvenEndpointTorus.FreeCoordinates hI
local notation "Layer" => GlobalNormalFrame.ZeroLayer R Empty (2*d)
  (PathOriginalStratumTransport.mutableSet (2*d) I) (PathOriginalYPresentation.matrix (2*d))
local notation "Std" => TorusThomInput.BaseRing R I μ
local notation "Fiber" => PathOriginalCoefficientTransport.Fiber (I:=I) R Empty (PathOriginalYPresentation.matrix (2*d))
local notation "Coef" => Coefficients R hI (1:R) 1

theorem y_forward (p : μ) :
    Units.map (PathOriginalStrictCells.yBase R hI).toRingHom.toMonoidHom
      (Units.map (y_section R hI).toRingHom.toMonoidHom (PathYWordBasis.freeUnit R hI p))=
    Units.map (MvPolynomial.C : OriginalTorus.Torus R μ →+* Std).toMonoidHom
      (FinsuppTorusUniversal.unit R μ p) := by
  apply Units.ext
  have hh := congrArg (fun f : Coef →ₐ[R] Layer => f
    (signedCoordinate R hI (1:R) 1 (includeRepresentative p.val) : Coef)) (y_inclusion R hI)
  change y_section R hI (PathOriginalYCoefficient.coefficientEquiv R hI
    (signedCoordinate R hI (1:R) 1 (includeRepresentative p.val) : Coef))=
    PathOriginalYStratum.equiv R hI (toLayer R hI (1:R) 1
      (signedCoordinate R hI (1:R) 1 (includeRepresentative p.val) : Coef)) at hh
  change PathOriginalStrictCells.yBase R hI
    (y_section R hI (PathOriginalYCoefficient.coefficientEquiv R hI
      (signedCoordinate R hI (1:R) 1 (includeRepresentative p.val) : Coef)))=_
  rw [hh,toLayer_signed]
  change PathEvenEndpointTorus.stratumEquiv hI R ((PathOriginalYStratum.equiv R hI).symm
    (PathOriginalYStratum.equiv R hI _))=_
  rw [AlgEquiv.symm_apply_apply]
  exact PathEvenEndpointTorus.stratum_free_coordinate hI R p

theorem y_inverse (p : μ) :
    Units.map (PathOriginalStrictCells.yBase R hI).symm.toRingHom.toMonoidHom
      (Units.map (MvPolynomial.C : OriginalTorus.Torus R μ →+* Std).toMonoidHom
        (FinsuppTorusUniversal.unit R μ p))=
    Units.map (y_section R hI).toRingHom.toMonoidHom (PathYWordBasis.freeUnit R hI p) := by
  apply Units.ext
  apply (PathOriginalStrictCells.yBase R hI).injective
  change PathOriginalStrictCells.yBase R hI ((PathOriginalStrictCells.yBase R hI).symm _) = _
  rw [AlgEquiv.apply_symm_apply]
  exact (congrArg Units.val (y_forward R hI p)).symm

variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (W : GradedMilnorWittSheaf.Standard site N)

theorem y_word (i : BinaryWordCoordinates.Index (Fintype.card μ)) :
    GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of Std) (T:=CommRingCat.of Layer)
      (PathOriginalStrictCells.yBase R hI).symm.toRingHom
      (OrderedBinaryWords.word (Fintype.card μ)
        (fun k => (W.symbols (CommRingCat.of Std)).symbol (StrictTorusSymbolInput.baseUnit R I μ k)) i)=
    GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of Fiber) (T:=CommRingCat.of Layer)
      (y_section R hI).toRingHom (PathYWordBasis.word R hI site N W i) := by
  change (GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of Std) (T:=CommRingCat.of Layer)
    (PathOriginalStrictCells.yBase R hI).symm.toRingHom).toMonoidHom
    (OrderedBinaryWords.word (Fintype.card μ) _ i)=
    (GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of Fiber) (T:=CommRingCat.of Layer)
      (y_section R hI).toRingHom).toMonoidHom
      (OrderedBinaryWords.word (Fintype.card μ) _ i)
  rw [OrderedBinaryWords.map_word,OrderedBinaryWords.map_word]
  congr 1
  funext k
  change GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of Std) (T:=CommRingCat.of Layer)
    (PathOriginalStrictCells.yBase R hI).symm.toRingHom
      ((W.symbols (CommRingCat.of Std)).symbol (StrictTorusSymbolInput.baseUnit R I μ k))=
    GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of Fiber) (T:=CommRingCat.of Layer)
      (y_section R hI).toRingHom ((W.symbols (CommRingCat.of Fiber)).symbol
        (PathYWordBasis.freeUnit R hI (TorusModelWordBasis.ordering μ k)))
  rw [GradedMilnorWittSheaf.pullback_symbol,GradedMilnorWittSheaf.pullback_symbol]
  congr 1
  exact y_inverse R hI _

#print axioms y_forward
#print axioms y_inverse
#print axioms y_word
end Y

section Z
variable {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)
local notation "μ" => PathVariableEndpointMaps.FreeCoordinates hI
local notation "Layer" => GlobalNormalFrame.ZeroLayer R (Fin 1) n
  (PathOriginalStratumTransport.mutableSet n I) (PathOriginalZPresentation.matrix n)
local notation "Std" => TorusThomInput.BaseRing R I μ
local notation "Fiber" => PathOriginalCoefficientTransport.Fiber (I:=I) R (Fin 1) (PathOriginalZPresentation.matrix n)
local notation "Coef" => Coefficients (PathOriginalZPresentation.Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1

theorem z_forward (p : μ) :
    Units.map (PathOriginalStrictCells.zBase R hI).toRingHom.toMonoidHom
      (Units.map (z_section R hI).toRingHom.toMonoidHom (PathZWordBasis.freeUnit R hI p))=
    Units.map (MvPolynomial.C : OriginalTorus.Torus R μ →+* Std).toMonoidHom
      (FinsuppTorusUniversal.unit R μ p) := by
  apply Units.ext
  have hh := congrArg (fun f : Coef →ₐ[R] Layer => f
    (signedCoordinate (PathOriginalZPresentation.Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 (includeRepresentative p.val) : Coef)) (z_inclusion R hI)
  change z_section R hI (PathOriginalZCoefficient.coefficientEquiv R hI
    (signedCoordinate (PathOriginalZPresentation.Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 (includeRepresentative p.val) : Coef))=
    PathOriginalZStratum.equiv R hI (toLayer (PathOriginalZPresentation.Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1
      (signedCoordinate (PathOriginalZPresentation.Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 (includeRepresentative p.val) : Coef)) at hh
  change PathOriginalStrictCells.zBase R hI
    (z_section R hI (PathOriginalZCoefficient.coefficientEquiv R hI
      (signedCoordinate (PathOriginalZPresentation.Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 (includeRepresentative p.val) : Coef)))=_
  rw [hh,toLayer_signed]
  change PathVariableEndpointTorus.stratumEquiv R hI ((PathOriginalZStratum.equiv R hI).symm
    (PathOriginalZStratum.equiv R hI _))=_
  rw [AlgEquiv.symm_apply_apply]
  exact PathVariableEndpointTorus.stratum_free_coordinate R hI p

theorem z_inverse (p : μ) :
    Units.map (PathOriginalStrictCells.zBase R hI).symm.toRingHom.toMonoidHom
      (Units.map (MvPolynomial.C : OriginalTorus.Torus R μ →+* Std).toMonoidHom
        (FinsuppTorusUniversal.unit R μ p))=
    Units.map (z_section R hI).toRingHom.toMonoidHom (PathZWordBasis.freeUnit R hI p) := by
  apply Units.ext
  apply (PathOriginalStrictCells.zBase R hI).injective
  change PathOriginalStrictCells.zBase R hI ((PathOriginalStrictCells.zBase R hI).symm _) = _
  rw [AlgEquiv.apply_symm_apply]
  exact (congrArg Units.val (z_forward R hI p)).symm

variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (W : GradedMilnorWittSheaf.Standard site N)

theorem z_word (i : BinaryWordCoordinates.Index (Fintype.card μ)) :
    GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of Std) (T:=CommRingCat.of Layer)
      (PathOriginalStrictCells.zBase R hI).symm.toRingHom
      (OrderedBinaryWords.word (Fintype.card μ)
        (fun k => (W.symbols (CommRingCat.of Std)).symbol (StrictTorusSymbolInput.baseUnit R I μ k)) i)=
    GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of Fiber) (T:=CommRingCat.of Layer)
      (z_section R hI).toRingHom (PathZWordBasis.word R hI site N W i) := by
  change (GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of Std) (T:=CommRingCat.of Layer)
    (PathOriginalStrictCells.zBase R hI).symm.toRingHom).toMonoidHom
    (OrderedBinaryWords.word (Fintype.card μ) _ i)=
    (GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of Fiber) (T:=CommRingCat.of Layer)
      (z_section R hI).toRingHom).toMonoidHom
      (OrderedBinaryWords.word (Fintype.card μ) _ i)
  rw [OrderedBinaryWords.map_word,OrderedBinaryWords.map_word]
  congr 1
  funext k
  change GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of Std) (T:=CommRingCat.of Layer)
    (PathOriginalStrictCells.zBase R hI).symm.toRingHom
      ((W.symbols (CommRingCat.of Std)).symbol (StrictTorusSymbolInput.baseUnit R I μ k))=
    GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of Fiber) (T:=CommRingCat.of Layer)
      (z_section R hI).toRingHom ((W.symbols (CommRingCat.of Fiber)).symbol
        (PathZWordBasis.freeUnit R hI (TorusModelWordBasis.ordering μ k)))
  rw [GradedMilnorWittSheaf.pullback_symbol,GradedMilnorWittSheaf.pullback_symbol]
  congr 1
  exact z_inverse R hI _

#print axioms z_forward
#print axioms z_inverse
#print axioms z_word
end Z

end Verification.PathOriginalStrictCoordinateUnits
