/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OrderedPathForestBundles
import Verification.DynkinFreezingOrder
import Verification.FiniteDynkinClassificationInput

/-!
# Original Finite Dynkin Bundles

Actual cohomological dimension and vector-bundle triviality for every
irreducible finite Dynkin acyclic seed satisfying AS. The matrix classification
is ordinary; each Dynkin deletion and every geometric step is internal.
-/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000
namespace Verification.OriginalFiniteDynkinBundles
open CategoryTheory.MonoidalCategory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
attribute [local instance] Abelian.hasFiniteBiproducts
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.ExchangeOpenCover Verification.IndependentBasicOpen
open Verification.IndependentOpenCoordinates Verification.GlobalExchangeSmooth
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasBinaryBiproducts A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {Z : Type*} [Category Z] [Preadditive Z] [HasFiniteBiproducts Z]
variable [HasZeroObject Z] [HasShift Z ℤ] [∀ q : ℤ, (CategoryTheory.shiftFunctor Z q).Additive] [Pretriangulated Z]
variable (J : DerivedCategory A ⥤ Z) [J.Additive] [J.CommShift ℤ] [J.IsTriangulated]
variable (L : DerivedCategory C ⥤ Z) [L.Additive] [L.CommShift ℤ] [L.IsTriangulated]
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)

open Verification.PathCompression Verification.PathOriginalStratumTransport
open Verification.PathOriginalIndependence Verification.PathSignedFaceUnits
open Verification.GradedSectionTotal Verification.SheafGradedLaurentResidue
open Verification.PathMilnorWittCoefficients
variable (R : Type) [Field R]
variable (P : LocalizedCoordinatePurity.Standard L R G)
variable (H : LocalizedAffineThomInvariance.Standard L R G)
variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (hV : LocalizedThomSections.Naturality J L G R site M N V)
variable (Cg : StandardThomContractionNormalization.Grading R site N)
variable (hCg : SheafContractionNaturality.Standard R site N Cg)
variable (O : ThomPermutationInput.Standard J L G R site M N V)
variable (W : GradedMilnorWittSheaf.Standard site N)
variable (QO : GradedMilnorWittThomOrientation.Normalization J L G R site M N V O W)
variable (MW : GradedMilnorWittLaurent.Standard R site N W Cg)

variable (T : StrictLocalizedCells.TorusCells J L G R)
variable (CR : StrictProjectiveModel.ChainRepresentability (A:=A))
variable (empty : ∀ X : Scheme,IsEmpty X → IsZero (L.obj (DerivedCategory.Q.obj (G.obj X))))
variable (Q : LocalizedIndexedPurity.Standard L R G P)
variable (K : LocalizedNormalizedFlag.Standard L R G E P)
variable (Norm : ∀ (ι : Type) [Fintype ι] [LinearOrder ι] [DecidableEq ι] (v : ι) (r : ℕ)
  (hr : Fintype.card (CoordinateFlag.Old ι v)=r),
  StandardThomContractionNormalization.Standard J L G R site M N V hV H
    (CoordinateFlag.Old ι v) r hr (K.principal ι v) Cg)

variable (Z₀ : A) (Symbols : StrictTorusSymbolInput.Standard J L G R T Z₀ M site N W V)

variable (PH : GradedMilnorWittHomogeneity.Standard site N W)
variable (SC : GradedMilnorWittStrictScalars.Standard J L G R site M N W PH V)



variable [MonoidalCategory A] [MonoidalPreadditive A]
variable (MS : ContractedStrictProductInput.Standard J L G R)
variable (unit : Z₀≅𝟙_ A) (TensorMW : PositiveMilnorWittTensorInput.Standard M)
variable (FZ : FZForestMutationInput.Standard) (BFZ : BFZForestMutationInput.Standard R)
variable (Nis : StrictNisnevichInput.Theory A)
variable (NR : StrictNisnevichRepresentability.Standard J L G Nis R)
variable (HC : StrictCoefficientComparison.StandardHomology (A:=A))
variable (NP : StrictNisnevichInput.Standard Nis R)
variable (LP : StrictPrincipalLongExact.Standard Nis R)
variable (κ : Type) [Fintype κ] (n : ℕ)
variable (B : (Fin n⊕κ) → (Fin n⊕Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j,earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0)
variable (hall : ∀ I : Finset (Fin n),Independent (laterWeights κ n B) I →
  AnticliqueSubcolumns.AS (fun r i => B r (Sum.inl i)) I)
variable (Classify : FiniteDynkinClassificationInput.Standard)
variable (hfinite : FiniteDynkinClassificationInput.FiniteCartan (fun i j=>B (Sum.inl i) (Sum.inl j)))
variable (hconn : FiniteDynkinClassificationInput.Indecomposable (fun i j=>B (Sum.inl i) (Sum.inl j)))
include E P H V hV Cg hCg O W QO MW T CR empty Q K Norm Symbols PH SC MS unit TensorMW FZ BFZ NR HC NP LP hpos hneg hsupport hall Classify hfinite hconn in
theorem dimension_one : StrictCohomologicalDimension.Bound Nis (Global R κ n B) 1 := by
  obtain ⟨form⟩ := Classify.classify n _ hfinite hconn
  obtain ⟨rank,hinj,horder⟩ := DynkinFreezingOrder.exists_order n _ form (ExchangeRing.Adjacent (laterWeights κ n B))
  exact OrderedPathForestFreezing.original_bound J L G E R P H site M N V hV Cg hCg O W QO MW
    T CR empty Q K Norm Z₀ Symbols PH SC MS unit TensorMW FZ BFZ Nis NR HC NP LP
    κ n B hpos hneg hsupport hall rank hinj horder

variable {GG : Scheme → Type*} [∀ X,AddCommGroup (GG X)]
variable (GT : SchemeGZeroInput.Theory GG) (GK : SchemeGZeroInput.Koszul GT)
variable (GST : SchemeGZeroInput.SplitAffineTorus GT) (GLocal : SchemeGZeroInput.Localization GT)
variable (Cartan : SmoothCartanInput.Standard)
variable (Det : DeterminantStandardInput.Standard (Global R κ n B))
variable (FF : Type) [Field FF] [Algebra (Global R κ n B) FF]
variable (Split : NisnevichSplittingInput.Standard Nis R)
include E P H V hV Cg hCg O W QO MW T CR empty Q K Norm Symbols PH SC MS unit TensorMW FZ BFZ NR HC NP LP hpos hneg hsupport hall Classify hfinite hconn GT GK GST GLocal Cartan Det FF Split in
theorem all_free (Qb : ActualProjectiveSplitting.Bundle (Global R κ n B)) :
    ActualProjectiveSplitting.Trivial Qb := by
  obtain ⟨form⟩ := Classify.classify n _ hfinite hconn
  obtain ⟨rank,hinj,horder⟩ := DynkinFreezingOrder.exists_order n _ form (ExchangeRing.Adjacent (laterWeights κ n B))
  exact OrderedPathForestBundles.all_free J L G E R P H site M N V hV Cg hCg O W QO MW
    T CR empty Q K Norm Z₀ Symbols PH SC MS unit TensorMW FZ BFZ Nis NR HC NP LP
    κ n B hpos hneg hsupport hall rank hinj horder GT GK GST GLocal Cartan Det FF Split Qb

#print axioms dimension_one
#print axioms all_free
end Verification.OriginalFiniteDynkinBundles
