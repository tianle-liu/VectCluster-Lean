/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalEvenChowWittBetti
import Verification.SevenfoldActualBetti

/-!
# Sevenfold Actual Chow Witt

The sevenfold conclusion on the actual scheme and actual Chow--Witt group.
-/
noncomputable section
open scoped Classical TensorProduct
set_option quotPrecheck false
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 100000
namespace Verification.SevenfoldActualChowWitt
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

/-- The actual Chow--Witt group of the displayed sevenfold, over the
original arbitrary perfect base field of characteristic different from two. -/
def chowWitt : CW (Spec (CommRingCat.of (SevenfoldExchangeMatrix.Ring R))) 2 ≃+
    (Fin 2 → RingSection W R) :=
  (OriginalEvenChowWittBetti.freePower J L G R T (Fin 2) 5 SevenfoldExchangeMatrix.matrix SevenfoldExchangeMatrix.positive_order SevenfoldExchangeMatrix.negative_order SevenfoldExchangeMatrix.support (fun I hI => (SevenfoldExchangeMatrix.selected_AS I hI).1) (fun I hI => (SevenfoldExchangeMatrix.selected_AS I hI).2) E P H empty site M N V W WD WT WH WE Q K U hV O Cg hCg Norm WN WO HC Nis NR RT RF RS RP RZ RE RU RUN RN RBC CH RK RNeg IP KM CW CWQ CWH h2 IQ IS
    SevenfoldExchangeMatrix.color (by decide) (fun a i => by rw [SevenfoldExchangeMatrix.frozen_entry]; congr)
    (fun a i hne he => SevenfoldExchangeMatrix.same_color_nonzero a i hne he)
    SevenfoldGraphFreeness.chain_free 2 (by decide)).trans
      (LinearEquiv.piCongrLeft' ℤ (fun _ => RingSection W R)
        (finCongr SevenfoldActualBetti.exponent)).toAddEquiv

def witt : Nis.cohomology (Spec (CommRingCat.of (SevenfoldExchangeMatrix.Ring R))) (M 0) 2 ≃+
    (Fin 2 → RingSection W R) :=
  (OriginalIWittComparison.chowWittEquiv R (Fin 2) 5 SevenfoldExchangeMatrix.matrix
    SevenfoldExchangeMatrix.anticlique_AS SevenfoldExchangeMatrix.positive_order
    SevenfoldExchangeMatrix.negative_order SevenfoldExchangeMatrix.support
    RT RF RS RP RZ RE RU RUN RN RBC CH RK RNeg Nis IP CW CWQ CWH h2 KM (M 0) IQ IS 2 (by decide)).symm.trans
    (chowWitt J L G R T E P H empty site M N V W WD WT WH WE Q K U hV O Cg hCg Norm WN WO HC Nis NR RT RF RS RP RZ RE RU RUN RN RBC CH RK RNeg IP KM CW CWQ CWH h2 IQ IS)

def ideal : Nis.cohomology (Spec (CommRingCat.of (SevenfoldExchangeMatrix.Ring R))) (IP 2) 2 ≃+
    (Fin 2 → RingSection W R) :=
  (OriginalChowWittIComparison.comparisonEquiv R (Fin 2) 5 SevenfoldExchangeMatrix.matrix
    SevenfoldExchangeMatrix.anticlique_AS SevenfoldExchangeMatrix.positive_order
    SevenfoldExchangeMatrix.negative_order SevenfoldExchangeMatrix.support
    RT RF RS RP RZ RE RU RUN RN RBC CH RK RNeg Nis IP CW CWQ CWH 2 (by decide)).symm.trans
    (chowWitt J L G R T E P H empty site M N V W WD WT WH WE Q K U hV O Cg hCg Norm WN WO HC Nis NR RT RF RS RP RZ RE RU RUN RN RBC CH RK RNeg IP KM CW CWQ CWH h2 IQ IS)

#print axioms chowWitt
#print axioms witt
#print axioms ideal
end Verification.SevenfoldActualChowWitt
