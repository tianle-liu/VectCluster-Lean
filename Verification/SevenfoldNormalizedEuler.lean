/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SevenfoldEulerClassification
import Verification.OrdinaryEulerNormalizationInput
import Verification.SevenfoldActualIndependentSets
import Verification.OriginalEulerClassification
import Verification.ChowWittNisnevichInput

/-!
# Sevenfold Normalized Euler

The actual sevenfold Euler bijection uses the normalized ordinary Euler map, including its zero on every trivial oriented bundle.
-/
noncomputable section
open scoped Classical TensorProduct
set_option quotPrecheck false
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 100000
namespace Verification.SevenfoldNormalizedEuler
open Verification.OriginalWittUniversalCohomology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Verification.StrictProjectiveModel Verification.FrozenAcyclicCover
open Verification.ExchangeOpenCover Verification.IndependentChartIndex
open Verification.WittSheafSectionsInput
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasBinaryBiproducts A]
variable [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
variable [∀ z : ℤ, (shiftFunctor D z).Additive] [Pretriangulated D] [HasFiniteBiproducts D]
variable (J : DerivedCategory A ⥤ D) [J.Additive] [J.CommShift ℤ] [J.IsTriangulated]
variable (L : DerivedCategory C ⥤ D) [L.Additive] [L.CommShift ℤ] [L.IsTriangulated]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (R : Type) [Field R]

variable (T : StrictLocalizedCells.TorusCells J L G R)
variable (E : OpenConeExcision.StandardExcision G) (P : LocalizedCoordinatePurity.Standard L R G)

variable (H : ChainRepresentability (A := A))
variable (empty : ∀ X : Scheme, IsEmpty X → IsZero (L.obj (DerivedCategory.Q.obj (G.obj X))))

variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)

open scoped BigOperators
local notation "Model" => OriginalPositiveCellular.model J L G R T (Fin 2) 5 SevenfoldExchangeMatrix.matrix SevenfoldExchangeMatrix.positive_order SevenfoldExchangeMatrix.negative_order SevenfoldExchangeMatrix.support (fun I hI => (SevenfoldExchangeMatrix.selected_AS I hI).1) (fun I hI => (SevenfoldExchangeMatrix.selected_AS I hI).2) E P H empty



variable (W : Scheme.{0}ᵒᵖ ⥤ CommRingCat.{0}) (WD : Symbols R W)
variable (WT : TorusBasis R W WD) (WH : WittSheafAffineInvariance.Standard R W)
variable (WE : Comparison R W site N)

variable (Q : LocalizedIndexedPurity.Standard L R G P)
variable (K : LocalizedNormalizedFlag.Standard L R G E P)
variable (U : LocalizedAffineThomInvariance.Standard L R G)


variable (hV : LocalizedThomSections.Naturality J L G R site M N V)
variable (O : ThomPermutationInput.Standard J L G R site M N V)
variable (Cg : StandardThomContractionNormalization.Grading R site N)
variable (hCg : SheafContractionNaturality.Standard R site N Cg)
variable (Norm : ∀ (ι : Type) [Fintype ι] [LinearOrder ι] [DecidableEq ι] (v : ι) (r : ℕ)
  (hr : Fintype.card (CoordinateFlag.Old ι v) = r),
  StandardThomContractionNormalization.Standard J L G R site M N V hV U
    (CoordinateFlag.Old ι v) r hr (K.principal ι v) Cg)

variable (WN : LaurentNormalization R W WD site N WE Cg)
variable (WO : WittThomOrientationInput.Normalization J L G R site M N V O W WD WE)
local notation "TC" => OriginalWittTensorTerms.complex (Fin 2) 5 SevenfoldExchangeMatrix.matrix (RingSection W R) SevenfoldExchangeMatrix.positive_order SevenfoldExchangeMatrix.negative_order SevenfoldExchangeMatrix.support
local notation "RC" => (fun j : ℤ => StrictCoefficientCochains.complex (Model).complex (M j))
local notation "TE" => OriginalWittCoefficientTerms.termEquiv J L G R T (Fin 2) 5 SevenfoldExchangeMatrix.matrix SevenfoldExchangeMatrix.positive_order SevenfoldExchangeMatrix.negative_order SevenfoldExchangeMatrix.support (fun I hI => (SevenfoldExchangeMatrix.selected_AS I hI).1) (fun I hI => (SevenfoldExchangeMatrix.selected_AS I hI).2)
  E P H empty site M N V W WD WT WH WE
local notation "SE" => OriginalOrderedStrictSections.termEquiv J L G R T (Fin 2) 5 SevenfoldExchangeMatrix.matrix SevenfoldExchangeMatrix.positive_order SevenfoldExchangeMatrix.negative_order SevenfoldExchangeMatrix.support (fun I hI => (SevenfoldExchangeMatrix.selected_AS I hI).1) (fun I hI => (SevenfoldExchangeMatrix.selected_AS I hI).2)
  E P H empty site M N V



variable (HC : StrictCoefficientComparison.StandardHomology (A := A))
variable (Nis : StrictNisnevichInput.Theory A)
variable (NR : StrictNisnevichRepresentability.Standard J L G Nis R)


variable (RT : RostAffineInput.Theory) (RF : RostFiniteProducts.Standard RT)
variable (RS : RostSupportInput.Theory RT) (RP : RostPrincipalLocalizationInput.Theory RT)
variable (RZ : RostWeightZero.IntegralConvention RT)
variable (RE : RostCanonicalCoefficients.GenericZeroEvaluation RT RF RZ)
variable (RU : OriginalRostUnitTerms.UnitsConvention RT)
variable (RUN : RostCanonicalCoefficients.UnitsNaturality RT RF RU)
variable (RN : RostPrincipalResidueInput.Normalization RT RP RF RZ RE RU)
variable (RBC : OriginalRostBoundaryCharts.Standard R (Fin 2) 5 SevenfoldExchangeMatrix.matrix SevenfoldExchangeMatrix.positive_order SevenfoldExchangeMatrix.negative_order SevenfoldExchangeMatrix.support
  (OriginalASChowVanishing.selected_injective (Fin 2) 5 SevenfoldExchangeMatrix.matrix (anticliqueAS (Fin 2) 5 SevenfoldExchangeMatrix.matrix (fun I hI => (SevenfoldExchangeMatrix.selected_AS I hI).1) (fun I hI => (SevenfoldExchangeMatrix.selected_AS I hI).2)))
  (OriginalASChowVanishing.tame R (Fin 2) 5 SevenfoldExchangeMatrix.matrix (anticliqueAS (Fin 2) 5 SevenfoldExchangeMatrix.matrix (fun I hI => (SevenfoldExchangeMatrix.selected_AS I hI).1) (fun I hI => (SevenfoldExchangeMatrix.selected_AS I hI).2))) RT RS RP)
variable (CH : Scheme → ℕ → AddCommGrp)
variable (RK : RostMilnorInput.ChowComparison RT CH) (RNeg : RostMilnorInput.NegativeWeights RT)
variable (IP KM : ℕ → A) (CW : Scheme → ℕ → AddCommGrp)
variable (CWQ : ChowWittFiberProductInput.Theory Nis R IP CW CH)
variable (CWH : ChowWittFiberProductInput.Standard Nis R IP CW CH CWQ)
variable [PerfectField R] (h2 : (2 : R) ≠ 0)
variable (IQ : FundamentalIdealCohomologyInput.Theory Nis R IP KM (M 0))
variable (IS : FundamentalIdealCohomologyInput.Standard Nis R IP KM (M 0) IQ CH h2)


variable (PMW : ℕ → A)
variable (CWRef : ChowWittNisnevichInput.Standard J L G Nis R NR PMW CW)
variable (Factor : Type*) [Group Factor]
variable (OE : OrdinaryEulerNormalizationInput.Standard J L G Nis R NR PMW CW CWRef Factor)

def equivalence : ActualOrientations.Classes (R := SevenfoldExchangeMatrix.Ring R) (r := 2) ≃
    CW (Spec (CommRingCat.of (SevenfoldExchangeMatrix.Ring R))) 2 := by
  letI := SevenfoldExchangeMatrix.domain R
  letI := SevenfoldExchangeMatrix.smooth R
  letI := OE.factorAction (SevenfoldExchangeMatrix.Ring R)
  exact SevenfoldEulerClassification.orientedChowWitt J L G R T E P H empty HC Nis NR CW PMW CWRef
    (OE.stages (SevenfoldExchangeMatrix.Ring R)) Factor (OE.euler (SevenfoldExchangeMatrix.Ring R))

omit [PerfectField R] in
theorem equivalence_apply (x : ActualOrientations.Classes (R := SevenfoldExchangeMatrix.Ring R) (r := 2)) :
    letI := SevenfoldExchangeMatrix.domain R
    letI := SevenfoldExchangeMatrix.smooth R
    equivalence J L G R T E P H empty HC Nis NR CW PMW CWRef Factor OE x =
      OrdinaryEulerNormalizationInput.chowWitt J L G Nis R NR PMW CW CWRef Factor OE
        (SevenfoldExchangeMatrix.Ring R) x := rfl

omit [PerfectField R] in
theorem trivial_zero (Q : ActualOrientations.Oriented (SevenfoldExchangeMatrix.Ring R) 2)
    (hQ : ActualProjectiveSplitting.Trivial Q.bundle) :
    equivalence J L G R T E P H empty HC Nis NR CW PMW CWRef Factor OE (Quotient.mk _ Q)=0 := by
  letI := SevenfoldExchangeMatrix.domain R
  letI := SevenfoldExchangeMatrix.smooth R
  rw [equivalence_apply]
  exact OrdinaryEulerNormalizationInput.chowWitt_zero J L G Nis R NR PMW CW CWRef Factor OE
    (SevenfoldExchangeMatrix.Ring R) Q hQ

omit [PerfectField R] in
theorem nonfree_of_nonzero (Q : ActualOrientations.Oriented (SevenfoldExchangeMatrix.Ring R) 2)
    (hQ : equivalence J L G R T E P H empty HC Nis NR CW PMW CWRef Factor OE (Quotient.mk _ Q)≠0) :
    ¬ ActualProjectiveSplitting.Trivial Q.bundle :=
  fun ht => hQ (trivial_zero J L G R T E P H empty HC Nis NR CW PMW CWRef Factor OE Q ht)

omit [PerfectField R] in
theorem unit_action (u : (SevenfoldExchangeMatrix.Ring R)ˣ)
    (Q : ActualOrientations.Oriented (SevenfoldExchangeMatrix.Ring R) 2) :
    letI := CWRef.unitAction (SevenfoldExchangeMatrix.Ring R) 2
    equivalence J L G R T E P H empty HC Nis NR CW PMW CWRef Factor OE (Quotient.mk _ (ActualOrientations.changeOrientation u Q))=
      u • equivalence J L G R T E P H empty HC Nis NR CW PMW CWRef Factor OE (Quotient.mk _ Q) := by
  letI := SevenfoldExchangeMatrix.domain R
  letI := SevenfoldExchangeMatrix.smooth R
  simp only [equivalence_apply]
  exact OrdinaryEulerNormalizationInput.chowWitt_unit J L G Nis R NR PMW CW CWRef Factor OE
    (SevenfoldExchangeMatrix.Ring R) u Q

#print axioms equivalence
#print axioms equivalence_apply
#print axioms trivial_zero
#print axioms nonfree_of_nonzero
#print axioms unit_action
end Verification.SevenfoldNormalizedEuler
