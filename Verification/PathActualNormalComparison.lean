/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathActualWordRows
import Verification.PathNormalDifferential
import Verification.PathStrictRealizationEntry
import Verification.EqualityConjugation

/-!
# Path Actual Normal Comparison

Equality of the actual geometric path differential and the fully realized normal-word differential in every degree.
-/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000
namespace Verification.PathActualNormalComparison
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
variable (R : Type) [CommRing R] [Nontrivial R]
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

local notation "Action" => PathStrictCoefficientAction.action J L G R site M N W PH V SC 1

section Y
variable (d p : ℕ)
local notation "B" => PathOriginalYPresentation.matrix (2*d)
local notation "pos" => positive_order B y_mutable
local notation "neg" => negative_order B y_mutable
local notation "supp" => support B y_mutable
local notation "hf" => fun I hI => (PathOriginalAS.y d I hI).1
local notation "hs" => fun I hI => (PathOriginalAS.y d I hI).2
local notation "Model" => OriginalPositiveCellular.model J L G R T (Empty) (2*d) B pos neg supp hf hs E P CR empty
local notation "Degree" q => PathActualWordDifferential.yDegree J L G R T Z₀ M site N W V Symbols E P CR empty PH SC d q

include Q Norm hCg QO MW in
theorem y_normal :
    (Degree (p+1)).inv ≫ (Model).complex.d (-((p+1:ℕ):ℤ)) (-(p:ℤ)) ≫ (Degree p).hom=
      PathNormalDifferential.y Z₀ (fun j:ℕ=>M (j:ℤ)) Action d (-((p+1:ℕ):ℤ)) (-(p:ℤ)) := by
  apply biproduct.hom_ext'
  intro b
  apply biproduct.hom_ext
  intro i
  obtain ⟨b,rfl⟩ := (PathStrictTermIndices.yWords d (p+1)).surjective b
  obtain ⟨i,rfl⟩ := (PathStrictTermIndices.yWords d p).surjective i
  let bi := PathStrictTermIndices.yWords d (p+1) b
  let ii := PathStrictTermIndices.yWords d p i
  have hb : PathWeightFiltration.weight bi.val≠0 := by
    intro h
    have hz := PathZeroWeightIndex.weight_zero_degree bi.val h
    have hd := bi.property
    omega
  by_cases hi : PathWeightFiltration.weight ii.val=0
  · have ha := PathActualWordRows.y_zero_target J L G E R P H site M N V hV Cg hCg O W QO MW T CR empty Q K Norm Z₀ Symbols PH SC d p b i hi
    have ht := PathNormalDifferential.y_zero_target Z₀ (fun j:ℕ=>M (j:ℤ)) Action d (-((p+1:ℕ):ℤ)) (-(p:ℤ)) ii hi
    have ht' := congrArg (fun f=>biproduct.ι
      (fun x=>PathOriginalDegreeTerms.wordObject Z₀ M x.val) bi ≫ f) ht
    trans 0
    · simpa only [Category.assoc] using ha
    · simpa only [Category.assoc,comp_zero] using ht'.symm
  · have ha := PathActualWordRows.y_positive J L G E R P H site M N V hV Cg hCg O W QO MW T CR empty Q K Norm Z₀ Symbols PH SC d p b i hi hb
    have ht := PathNormalDifferential.y_positive Z₀ (fun j:ℕ=>M (j:ℤ)) Action d
      (-((p+1:ℕ):ℤ)) (-(p:ℤ)) (by omega)
      ⟨⟨bi.val,Nat.pos_of_ne_zero hb⟩,bi.property⟩
      ⟨⟨ii.val,Nat.pos_of_ne_zero hi⟩,ii.property⟩
    rw [PathStrictRealizationEntry.entry] at ht
    have he := ha.trans ht.symm
    apply EqualityConjugation.cancel
      (show M (PathWeightFiltration.weight bi.val:ℤ)=PathOriginalDegreeTerms.wordObject Z₀ M bi.val from (if_neg hb).symm)
      (show PathOriginalDegreeTerms.wordObject Z₀ M ii.val=M (PathWeightFiltration.weight ii.val:ℤ) from if_neg hi)
    simpa only [Category.assoc] using he

#print axioms y_normal
end Y

section Z
variable (n p : ℕ)
local notation "B" => PathOriginalZPresentation.matrix (n)
local notation "pos" => positive_order B z_mutable
local notation "neg" => negative_order B z_mutable
local notation "supp" => support B z_mutable
local notation "hf" => fun I hI => (PathOriginalAS.z n I hI).1
local notation "hs" => fun I hI => (PathOriginalAS.z n I hI).2
local notation "Model" => OriginalPositiveCellular.model J L G R T (Fin 1) (n) B pos neg supp hf hs E P CR empty
local notation "Degree" q => PathActualWordDifferential.zDegree J L G R T Z₀ M site N W V Symbols E P CR empty PH SC n q

include Q Norm hCg QO MW in
theorem z_normal :
    (Degree (p+1)).inv ≫ (Model).complex.d (-((p+1:ℕ):ℤ)) (-(p:ℤ)) ≫ (Degree p).hom=
      PathNormalDifferential.z Z₀ (fun j:ℕ=>M (j:ℤ)) Action n (-((p+1:ℕ):ℤ)) (-(p:ℤ)) := by
  apply biproduct.hom_ext'
  intro b
  apply biproduct.hom_ext
  intro i
  obtain ⟨b,rfl⟩ := (PathStrictTermIndices.zWords n (p+1)).surjective b
  obtain ⟨i,rfl⟩ := (PathStrictTermIndices.zWords n p).surjective i
  let bi := PathStrictTermIndices.zWords n (p+1) b
  let ii := PathStrictTermIndices.zWords n p i
  have hb : PathWeightFiltration.weight bi.val≠0 := by
    intro h
    have hz := PathZeroWeightIndex.weight_zero_degree bi.val h
    have hd := bi.property
    omega
  by_cases hi : PathWeightFiltration.weight ii.val=0
  · have ha := PathActualWordRows.z_zero_target J L G E R P H site M N V hV Cg hCg O W QO MW T CR empty Q K Norm Z₀ Symbols PH SC n p b i hi
    have ht := PathNormalDifferential.z_zero_target Z₀ (fun j:ℕ=>M (j:ℤ)) Action n (-((p+1:ℕ):ℤ)) (-(p:ℤ)) ii hi
    have ht' := congrArg (fun f=>biproduct.ι
      (fun x=>PathOriginalDegreeTerms.wordObject Z₀ M x.val) bi ≫ f) ht
    trans 0
    · simpa only [Category.assoc] using ha
    · simpa only [Category.assoc,comp_zero] using ht'.symm
  · have ha := PathActualWordRows.z_positive J L G E R P H site M N V hV Cg hCg O W QO MW T CR empty Q K Norm Z₀ Symbols PH SC n p b i hi hb
    have ht := PathNormalDifferential.z_positive Z₀ (fun j:ℕ=>M (j:ℤ)) Action n
      (-((p+1:ℕ):ℤ)) (-(p:ℤ)) (by omega)
      ⟨⟨bi.val,Nat.pos_of_ne_zero hb⟩,bi.property⟩
      ⟨⟨ii.val,Nat.pos_of_ne_zero hi⟩,ii.property⟩
    rw [PathStrictRealizationEntry.entry] at ht
    have he := ha.trans ht.symm
    apply EqualityConjugation.cancel
      (show M (PathWeightFiltration.weight bi.val:ℤ)=PathOriginalDegreeTerms.wordObject Z₀ M bi.val from (if_neg hb).symm)
      (show PathOriginalDegreeTerms.wordObject Z₀ M ii.val=M (PathWeightFiltration.weight ii.val:ℤ) from if_neg hi)
    simpa only [Category.assoc] using he

#print axioms z_normal
end Z

end Verification.PathActualNormalComparison
