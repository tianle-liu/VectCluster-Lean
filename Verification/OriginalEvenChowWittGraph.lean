/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalWittUniversalCohomology
import Verification.OriginalEvenWittTensorCohomology
import Verification.ModuleAdditiveIso

/-!
# Original Even Chow Witt Graph

The literal signed group-ring quotient complex, tensored with the
actual coefficient Witt ring, computes ordinary Nisnevich cohomology of
the represented eta-periodic Witt coefficient. No signature lattice is used.
-/
noncomputable section
open scoped Classical TensorProduct
set_option quotPrecheck false
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 100000
namespace Verification.OriginalEvenChowWittGraph
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
variable [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [HasFiniteBiproducts D]
variable (J : DerivedCategory A ⥤ D) [J.Additive] [J.CommShift ℤ] [J.IsTriangulated]
variable (L : DerivedCategory C ⥤ D) [L.Additive] [L.CommShift ℤ] [L.IsTriangulated]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (R : Type) [Field R]

variable (T : StrictLocalizedCells.TorusCells J L G R)
variable (κ : Type) [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hf : ∀ I, Independent (laterWeights κ n B) I →
  Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (hs : ∀ I, Independent (laterWeights κ n B) I →
  FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)))

variable (E : OpenConeExcision.StandardExcision G) (P : LocalizedCoordinatePurity.Standard L R G)

variable (H : ChainRepresentability (A := A))
variable (empty : ∀ X : Scheme, IsEmpty X → IsZero (L.obj (DerivedCategory.Q.obj (G.obj X))))

variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)

open scoped BigOperators
local notation "Model" => OriginalPositiveCellular.model J L G R T κ n B hpos hneg hsupport hf hs E P H empty



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
local notation "TC" => OriginalWittTensorTerms.complex κ n B (RingSection W R) hpos hneg hsupport
local notation "RC" => (fun j : ℤ => StrictCoefficientCochains.complex (Model).complex (M j))
local notation "TE" => OriginalWittCoefficientTerms.termEquiv J L G R T κ n B hpos hneg hsupport hf hs
  E P H empty site M N V W WD WT WH WE
local notation "SE" => OriginalOrderedStrictSections.termEquiv J L G R T κ n B hpos hneg hsupport hf hs
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
variable (RBC : OriginalRostBoundaryCharts.Standard R κ n B hpos hneg hsupport
  (OriginalASChowVanishing.selected_injective κ n B (anticliqueAS κ n B hf hs))
  (OriginalASChowVanishing.tame R κ n B (anticliqueAS κ n B hf hs)) RT RS RP)
variable (CH : Scheme → ℕ → AddCommGrp)
variable (RK : RostMilnorInput.ChowComparison RT CH) (RNeg : RostMilnorInput.NegativeWeights RT)
variable (IP KM : ℕ → A) (CW : Scheme → ℕ → AddCommGrp)
variable (CWQ : ChowWittFiberProductInput.Theory Nis R IP CW CH)
variable (CWH : ChowWittFiberProductInput.Standard Nis R IP CW CH CWQ)
variable [PerfectField R] (h2 : (2 : R) ≠ 0)
variable (IQ : FundamentalIdealCohomologyInput.Theory Nis R IP KM (M 0))
variable (IS : FundamentalIdealCohomologyInput.Standard Nis R IP KM (M 0) IQ CH h2)

variable (c : Fin n → κ)
variable (hm : ∀ a i : Fin n, Even (B (Sum.inl a) (Sum.inl i)))
variable (hcoeff : ∀ a i, B (Sum.inr a) (Sum.inl i) = if c i = a then 1 else 0)
variable (hclique : ∀ a i : Fin n, a ≠ i → c a = c i → B (Sum.inl a) (Sum.inl i) ≠ 0)

/-- The actual positive Chow--Witt group has the full uncompressed
independence-cohomology decomposition, retaining integral torsion effects. -/
def uncompressed (p : ℕ) (hp : 0 < p) :
    CW (Spec (CommRingCat.of (Global R κ n B))) p ≃+
      ((SF : Finset (Fin n) × Finset κ) →
        (GraphTensorCohomology.simplex (OriginalEvenWittGraph.graph κ n B) c (RingSection W R) SF).homology p) :=
  (OriginalWittUniversalCohomology.chowWittEquiv J L G R T κ n B hpos hneg hsupport hf hs E P H empty
    site M N V W WD WT WH WE Q K U hV O Cg hCg Norm WN WO HC Nis NR
    RT RF RS RP RZ RE RU RUN RN RBC CH RK RNeg IP KM CW CWQ CWH h2 IQ IS p hp).trans
      (ModuleAdditiveIso.additive (OriginalEvenWittTensorCohomology.cohomologyIso κ n B c hm hcoeff
        hpos hneg hsupport hclique (RingSection W R) p))

#print axioms uncompressed
end Verification.OriginalEvenChowWittGraph
