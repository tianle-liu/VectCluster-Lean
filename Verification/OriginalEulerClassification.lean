/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalKZero
import Verification.OriginalBundleRange
import Verification.OriginalStrictCohomology
import Verification.OriginalScalarOne
import Verification.StrictModelBundleRange
import Verification.StrictModelEulerClassification

/-!
# Original Euler Classification

Rank-two oriented and unoriented Euler classification for the
actual original exchange algebra and its actual ambient cohomology.
The strict projective model and K_0 input are constructed internally.
-/
noncomputable section
namespace Verification.OriginalEulerClassification
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Verification.StrictProjectiveModel Verification.FrozenAcyclicCover
open Verification.ExchangeOpenCover
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
variable (κ : Type) [Fintype κ] (n : ℕ) (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j,earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0)
variable (hf : ∀ I,Independent (laterWeights κ n B) I → Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (hs : ∀ I,Independent (laterWeights κ n B) I → FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)))
variable (E : OpenConeExcision.StandardExcision G) (P : LocalizedCoordinatePurity.Standard L R G)
variable (H : ChainRepresentability (A := A))
variable (empty : ∀ X : Scheme,IsEmpty X → IsZero (L.obj (DerivedCategory.Q.obj (G.obj X))))


open Verification.OriginalBundleRange

variable (HC : StrictCoefficientComparison.StandardHomology (A := A))
variable (K2 : A)

abbrev H2 := (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of (Global R κ n B)))))) ⟶
  J.obj (StrictCoefficientComparison.target K2 2)

variable (S : letI := originalDomain R κ n B hpos hneg hsupport hf hs;
  AmbientPostnikovStages.EulerStages (R := Global R κ n B) J
    (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of (Global R κ n B)))))) K2)
variable (U : Type*) [Group U] [MulAction U (H2 J L G R κ n B K2)]
variable [MulAction (Global R κ n B)ˣ (H2 J L G R κ n B K2)]
variable (EC : letI := originalDomain R κ n B hpos hneg hsupport hf hs;
  StrictModelEulerClassification.StandardEuler S U)
variable (hh : StrictCellularGlobal.height κ n B≤2)

def orientedEquiv : ActualOrientations.Classes (R := Global R κ n B) (r := 2) ≃
    H2 J L G R κ n B K2 := by
  letI := originalDomain R κ n B hpos hneg hsupport hf hs
  exact StrictModelEulerClassification.chowWittEquiv S EC HC
    (StrictCellularGlobal.globalModel J L G R T κ n B hpos hneg hsupport hf hs E P H empty)
    (StrictCellularGlobal.support_upper J L G R T κ n B hpos hneg hsupport hf hs E P H empty)
    (StrictCellularGlobal.support_lower J L G R T κ n B hpos hneg hsupport hf hs E P H empty) hh

theorem orientedEquiv_apply (Q : ActualOrientations.Classes (R := Global R κ n B) (r := 2)) :
    orientedEquiv J L G R T κ n B hpos hneg hsupport hf hs E P H empty HC K2 S U EC hh Q=
      EC.chowWitt Q := rfl

variable (Det : DeterminantStandardInput.Standard (Global R κ n B))
variable (F : Type) [Field F] [Algebra (Global R κ n B) F]
variable {KG : Scheme → Type*} [∀ X,AddCommGroup (KG X)]
variable (GT : SchemeGZeroInput.Theory KG) (GK : SchemeGZeroInput.Koszul GT)
variable (GTorus : SchemeGZeroInput.SplitAffineTorus GT) (GLocalization : SchemeGZeroInput.Localization GT)
variable (SC : SmoothCartanInput.Standard)

def unorientedEquiv : RankedProjectiveClasses.Classes (Global R κ n B) 2 ≃
    Quotient (MulAction.orbitRel (Global R κ n B)ˣ (H2 J L G R κ n B K2)) := by
  letI := originalDomain R κ n B hpos hneg hsupport hf hs
  exact StrictModelEulerClassification.unorientedEquiv S EC HC
    (StrictCellularGlobal.globalModel J L G R T κ n B hpos hneg hsupport hf hs E P H empty)
    (StrictCellularGlobal.support_upper J L G R T κ n B hpos hneg hsupport hf hs E P H empty)
    (StrictCellularGlobal.support_lower J L G R T κ n B hpos hneg hsupport hf hs E P H empty) hh
    Det F (OriginalKZero.rank_bijective R κ n B hpos hneg hsupport hf hs GT GK GTorus GLocalization SC F).1

#print axioms H2
#print axioms orientedEquiv
#print axioms orientedEquiv_apply
#print axioms unorientedEquiv
end Verification.OriginalEulerClassification
