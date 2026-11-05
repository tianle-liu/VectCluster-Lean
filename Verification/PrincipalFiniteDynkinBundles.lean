/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalFiniteDynkinBundles
import Verification.PrincipalCoefficientSeed
import Verification.OriginalRankDomain

/-!
# Main Theorem A: principal-coefficient finite Dynkin bundles

Main Theorem A for the actual principal-coefficient coordinate ring.
The identity frozen block supplies RFR and AS internally; only the ordinary
uniform literature inputs and the stated acyclic finite Dynkin hypotheses remain.
-/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000
namespace Verification.PrincipalFiniteDynkinBundles
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
variable (n : ℕ) (B₀ : Matrix (Fin n) (Fin n) ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B₀ a i).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B₀ a i).toNat=0)
variable (Classify : FiniteDynkinClassificationInput.Standard)
variable (hfinite : FiniteDynkinClassificationInput.FiniteCartan B₀)
variable (hconn : FiniteDynkinClassificationInput.Indecomposable B₀)

include E P H V hV Cg hCg O W QO MW T CR empty Q K Norm Symbols PH SC MS unit TensorMW FZ BFZ NR HC NP LP hpos hneg Classify hfinite hconn in
/-- The principal-coefficient finite Dynkin coordinate ring has strict cohomological
dimension at most one under the stated hypotheses and explicit reference-theory inputs. -/
theorem dimension_one : StrictCohomologicalDimension.Bound Nis
    (Global R (Fin n) n (PrincipalCoefficientSeed.matrix B₀)) 1 :=
  OriginalFiniteDynkinBundles.dimension_one J L G E R P H site M N V hV Cg hCg O W QO MW
    T CR empty Q K Norm Z₀ Symbols PH SC MS unit TensorMW FZ BFZ Nis NR HC NP LP
    (Fin n) n (PrincipalCoefficientSeed.matrix B₀) hpos hneg
    (PrincipalCoefficientSeed.support B₀ hfinite)
    (PrincipalCoefficientSeed.selected_AS B₀ hpos hneg hfinite) Classify hfinite hconn

variable {GG : Scheme → Type*} [∀X,AddCommGroup (GG X)]
variable (GT : SchemeGZeroInput.Theory GG) (GK : SchemeGZeroInput.Koszul GT)
variable (GST : SchemeGZeroInput.SplitAffineTorus GT) (GLocal : SchemeGZeroInput.Localization GT)
variable (Cartan : SmoothCartanInput.Standard)
variable (Det : DeterminantStandardInput.Standard (Global R (Fin n) n (PrincipalCoefficientSeed.matrix B₀)))
variable (Split : NisnevichSplittingInput.Standard Nis R)

include E P H V hV Cg hCg O W QO MW T CR empty Q K Norm Symbols PH SC MS unit TensorMW FZ BFZ NR HC NP LP hpos hneg Classify hfinite hconn GT GK GST GLocal Cartan Det Split in
/-- Main Theorem A: every vector bundle on the principal-coefficient finite Dynkin
coordinate ring is trivial under the stated hypotheses and explicit reference-theory inputs. -/
theorem all_free (Qb : ActualProjectiveSplitting.Bundle
    (Global R (Fin n) n (PrincipalCoefficientSeed.matrix B₀))) : ActualProjectiveSplitting.Trivial Qb := by
  letI := OriginalRankDomain.global_domain R (Fin n) n (PrincipalCoefficientSeed.matrix B₀)
    hpos hneg (PrincipalCoefficientSeed.support B₀ hfinite)
    (fun I hI=>(GlobalSelectedColumns.AS_iff (Fin n) n
      (PrincipalCoefficientSeed.matrix B₀) I).mpr
        (PrincipalCoefficientSeed.selected_AS B₀ hpos hneg hfinite I hI) |>.1)
  exact OriginalFiniteDynkinBundles.all_free J L G E R P H site M N V hV Cg hCg O W QO MW
    T CR empty Q K Norm Z₀ Symbols PH SC MS unit TensorMW FZ BFZ Nis NR HC NP LP
    (Fin n) n (PrincipalCoefficientSeed.matrix B₀) hpos hneg
    (PrincipalCoefficientSeed.support B₀ hfinite)
    (PrincipalCoefficientSeed.selected_AS B₀ hpos hneg hfinite) Classify hfinite hconn
    GT GK GST GLocal Cartan Det (FractionRing (Global R (Fin n) n (PrincipalCoefficientSeed.matrix B₀))) Split Qb

#print axioms dimension_one
#print axioms all_free
end Verification.PrincipalFiniteDynkinBundles
