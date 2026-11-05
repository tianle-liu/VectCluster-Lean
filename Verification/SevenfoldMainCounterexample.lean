/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SevenfoldNormalizedEuler
import Verification.SevenfoldBundleRange
import Verification.SevenfoldNonfreeIndecomposable
import Verification.WittFieldDimensionInput

/-!
# Main Theorem B: the sevenfold counterexample

Main Theorem B constructs a nontrivial indecomposable rank-two bundle on the
sevenfold whose direct sum with one trivial line is free. The proof is relative
to the explicit hypotheses and reference-theory inputs in this module.
-/

noncomputable section
open scoped Classical TensorProduct
set_option quotPrecheck false
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 100000
namespace Verification.SevenfoldMainCounterexample
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

variable (FP : WittFieldDimensionInput.Standard R W)
variable (Det : DeterminantStandardInput.Standard (SevenfoldExchangeMatrix.Ring R))
variable (SN : letI := SevenfoldExchangeMatrix.domain R; OrientedLineStabilization.Naturality Det)
variable {KG : Scheme → Type*} [∀ X,AddCommGroup (KG X)]
variable (GT : SchemeGZeroInput.Theory KG) (GK : SchemeGZeroInput.Koszul GT)
variable (GTorus : SchemeGZeroInput.SplitAffineTorus GT) (GLocalization : SchemeGZeroInput.Localization GT)
variable (Cartan : SmoothCartanInput.Standard)
variable (SS : letI := SevenfoldExchangeMatrix.domain R;
  ∀ r,2≤r → AmbientPostnikovStages.StabilizationStages Det SN J
    (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of (SevenfoldExchangeMatrix.Ring R)))))) r)

include J L G R T E P H empty site M N V W WD WT WH WE Q K U hV O Cg hCg Norm WN WO HC Nis NR
  RT RF RS RP RZ RE RU RUN RN RBC CH RK RNeg IP KM CW CWQ CWH h2 IQ IS PMW CWRef Factor OE
  FP Det SN GT GK GTorus GLocalization Cartan SS in
/-- Main Theorem B: under the stated hypotheses and explicit reference-theory inputs,
the sevenfold admits a nontrivial indecomposable rank-two bundle that becomes free
after adding one trivial line. -/
theorem exists_bundle :
    letI := SevenfoldExchangeMatrix.domain R
    ∃ Z : ActualProjectiveSplitting.Bundle (SevenfoldExchangeMatrix.Ring R),
      ActualProjectiveSplitting.HasRank Z 2 ∧ ¬ ActualProjectiveSplitting.Trivial Z ∧
      ProjectiveIndecomposable.Indecomposable Z ∧
      Nonempty ((Z.object × SevenfoldExchangeMatrix.Ring R) ≃ₗ[SevenfoldExchangeMatrix.Ring R]
        (Fin 3 → SevenfoldExchangeMatrix.Ring R)) := by
  letI := SevenfoldExchangeMatrix.domain R
  letI := WittFieldDimensionInput.nontrivial R W FP
  letI : Nontrivial (CW (Spec (CommRingCat.of (SevenfoldExchangeMatrix.Ring R))) 2) :=
    (SevenfoldActualChowWitt.chowWitt J L G R T E P H empty site M N V W WD WT WH WE
      Q K U hV O Cg hCg Norm WN WO HC Nis NR RT RF RS RP RZ RE RU RUN RN RBC CH RK RNeg
      IP KM CW CWQ CWH h2 IQ IS).toEquiv.nontrivial
  obtain ⟨x,hx⟩ := exists_ne (0 : CW (Spec (CommRingCat.of (SevenfoldExchangeMatrix.Ring R))) 2)
  obtain ⟨Z,_,hn,hi⟩ := ProjectiveIndecomposable.nonzero_euler
    (SevenfoldNormalizedEuler.equivalence J L G R T E P H empty HC Nis NR CW PMW CWRef Factor OE)
    (SevenfoldNormalizedEuler.trivial_zero J L G R T E P H empty HC Nis NR CW PMW CWRef Factor OE)
    (SevenfoldNonfreeIndecomposable.line_free R Det GT GK GTorus GLocalization Cartan) x hx
  exact ⟨Z.bundle,Z.rank,hn,hi,SevenfoldBundleRange.one_line_stable J L G R T E P H empty HC Det SN
    (FractionRing (SevenfoldExchangeMatrix.Ring R)) GT GK GTorus GLocalization Cartan SS Z.bundle Z.rank⟩

#print axioms exists_bundle
end Verification.SevenfoldMainCounterexample
