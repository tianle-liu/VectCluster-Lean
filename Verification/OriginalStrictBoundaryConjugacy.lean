/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalStrictCellTests
import Verification.StrictCoefficientBoundaryEvaluation
import Verification.StrictCellBiproductEvaluation

/-!
# Original Strict Boundary Conjugacy

The actual original coefficient differential, expressed componentwise
in the fixed normal-Thom tests. Every block is the actual ambient
attaching boundary conjugated by constructed excision and purity maps.
-/
noncomputable section
namespace Verification.OriginalStrictBoundaryConjugacy
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Verification.StrictProjectiveModel Verification.FrozenAcyclicCover
open Verification.ExchangeOpenCover Verification.IndependentChartIndex
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasBinaryBiproducts A]
variable [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
variable [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [HasFiniteBiproducts D]
variable (J : DerivedCategory A ⥤ D) [J.Additive] [J.CommShift ℤ] [J.IsTriangulated]
variable (L : DerivedCategory C ⥤ D) [L.Additive] [L.CommShift ℤ] [L.IsTriangulated]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (R : Type) [CommRing R]

variable (T : StrictLocalizedCells.TorusCells J L G R)
variable [Nontrivial R] (κ : Type) [Fintype κ] (n : ℕ)
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

attribute [local instance] Abelian.hasFiniteBiproducts

open scoped BigOperators
local notation "Fil" => PrimeSchemeFiltration.filteredChains (Global R κ n B)
  (fun i => initial R κ n B (Sum.inl i)) G
local notation "Cells" => StrictLocalizedCells.cell J L G R T κ n B hpos hneg hsupport hf hs E P
local notation "EmptyStage" => StrictCellularGlobal.emptyStage L G R κ n B empty
local notation "Model" => OriginalPositiveCellular.model J L G R T κ n B hpos hneg hsupport hf hs E P H empty

theorem global_evaluation (p : ℕ) (M : A)
    (a : (StrictCoefficientCochains.complex (Model).complex M).X p) :
    StrictCoefficientBoundaryEvaluation.termEvaluation J L H Fil Cells EmptyStage p M a =
      (LocalizedActualCellThom.relativeIso L G E R κ n B P hpos hneg hsupport hf hs p).hom ≫
        biproduct.desc
          (OriginalStrictCellTests.termEquiv J L G R T κ n B hpos hneg hsupport hf hs E P H empty M p a) := by
  exact StrictCellBiproductEvaluation.transported J
    (fun i : ActualCellThom.Index κ n B p => L.obj (ActualCellThom.localThom G R κ n B p i))
    (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs p) M
    (LocalizedActualCellThom.relativeIso L G E R κ n B P hpos hneg hsupport hf hs p)
    ((OriginalStrictCellTests.degreeIso J L G R T κ n B hpos hneg hsupport hf hs E P H empty p).inv ≫ a)

def block (p : ℕ) (j : ActualCellThom.Index κ n B (p+1))
    (i : ActualCellThom.Index κ n B p) :
    (L.obj (ActualCellThom.localThom G R κ n B (p+1) j))⟦(-1 : ℤ)⟧ ⟶
      L.obj (ActualCellThom.localThom G R κ n B p i) :=
  (biproduct.ι (fun j : ActualCellThom.Index κ n B (p+1) =>
      L.obj (ActualCellThom.localThom G R κ n B (p+1) j)) j ≫
    (LocalizedActualCellThom.relativeIso L G E R κ n B P hpos hneg hsupport hf hs (p+1)).inv)⟦(-1 : ℤ)⟧' ≫
      StrictCellularBoundary.ambientBoundary L Fil p ≫
        (LocalizedActualCellThom.relativeIso L G E R κ n B P hpos hneg hsupport hf hs p).hom ≫
          biproduct.π (fun i : ActualCellThom.Index κ n B p =>
            L.obj (ActualCellThom.localThom G R κ n B p i)) i

theorem coefficient_sum_shift (p : ℕ) (M : A)
    (a : (StrictCoefficientCochains.complex (Model).complex M).X p)
    (j : ActualCellThom.Index κ n B (p+1)) :
    StrictCoefficientBoundaryEvaluation.shiftTest J p M _
      (OriginalStrictCellTests.termEquiv J L G R T κ n B hpos hneg hsupport hf hs E P H empty M (p+1)
        ((StrictCoefficientCochains.complex (Model).complex M).d p (p+1) a) j) =
      ∑ i : ActualCellThom.Index κ n B p,
        block L G R κ n B hpos hneg hsupport hf hs E P p j i ≫
          OriginalStrictCellTests.termEquiv J L G R T κ n B hpos hneg hsupport hf hs E P H empty M p a i := by
  have h : StrictCoefficientBoundaryEvaluation.shiftTest J p M _
      (StrictCoefficientBoundaryEvaluation.termEvaluation J L H Fil Cells EmptyStage (p+1) M
        ((StrictCoefficientCochains.complex (Model).complex M).d p (p+1) a)) =
      StrictCellularBoundary.ambientBoundary L Fil p ≫
        StrictCoefficientBoundaryEvaluation.termEvaluation J L H Fil Cells EmptyStage p M a := by
    exact (congrArg (StrictCoefficientBoundaryEvaluation.shiftTest J p M _)
      (StrictCoefficientBoundaryEvaluation.differential_conjugate J L H Fil Cells EmptyStage p M a)).trans
        ((StrictCoefficientBoundaryEvaluation.shiftTest J p M _).apply_symm_apply _)
  rw [global_evaluation,global_evaluation,
    StrictCoefficientBoundaryEvaluation.shiftTest_precomp] at h
  have hj := congrArg (fun z => (biproduct.ι
    (fun j : ActualCellThom.Index κ n B (p+1) => L.obj (ActualCellThom.localThom G R κ n B (p+1) j)) j ≫
      (LocalizedActualCellThom.relativeIso L G E R κ n B P hpos hneg hsupport hf hs (p+1)).inv)⟦(-1 : ℤ)⟧' ≫ z) h
  dsimp only at hj
  rw [← (shiftFunctor D (-1 : ℤ)).map_comp_assoc] at hj
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id] at hj
  rw [← StrictCoefficientBoundaryEvaluation.shiftTest_precomp,biproduct.ι_desc] at hj
  rw [biproduct.desc_eq] at hj
  simpa only [block,Functor.map_comp,Preadditive.comp_sum,Category.assoc] using hj

theorem coefficient_sum (p : ℕ) (M : A)
    (a : (StrictCoefficientCochains.complex (Model).complex M).X p)
    (j : ActualCellThom.Index κ n B (p+1)) :
    OriginalStrictCellTests.termEquiv J L G R T κ n B hpos hneg hsupport hf hs E P H empty M (p+1)
        ((StrictCoefficientCochains.complex (Model).complex M).d p (p+1) a) j =
      (StrictCoefficientBoundaryEvaluation.shiftTest J p M _).symm
        (∑ i : ActualCellThom.Index κ n B p,
          block L G R κ n B hpos hneg hsupport hf hs E P p j i ≫
            OriginalStrictCellTests.termEquiv J L G R T κ n B hpos hneg hsupport hf hs E P H empty M p a i) := by
  apply (StrictCoefficientBoundaryEvaluation.shiftTest J p M _).injective
  rw [AddEquiv.apply_symm_apply]
  exact coefficient_sum_shift J L G R T κ n B hpos hneg hsupport hf hs E P H empty p M a j

#print axioms global_evaluation
#print axioms block
#print axioms coefficient_sum_shift
#print axioms coefficient_sum
end Verification.OriginalStrictBoundaryConjugacy
