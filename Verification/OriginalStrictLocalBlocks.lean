/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalOrderedStrictSections

/-!
# Original Strict Local Blocks

Literal local blocks and sparse coefficient tests of the genuine
strict model differential. All identities are finite biproduct identities
and preserve the original cochain differential.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.OriginalStrictLocalBlocks
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

local notation "Model" => OriginalPositiveCellular.model J L G R T κ n B hpos hneg hsupport hf hs E P H empty

def terms (q : ℕ) : ActualCellThom.Index κ n B q → A := fun i => (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs q i).term

def block (p : ℕ) (b : ActualCellThom.Index κ n B (p+1)) (i : ActualCellThom.Index κ n B p) :
    (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs (p+1) b).term ⟶ (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs p i).term :=
  biproduct.ι (terms J L G R T κ n B hpos hneg hsupport hf hs (p+1)) b ≫ (OriginalStrictCellTests.degreeIso J L G R T κ n B hpos hneg hsupport hf hs E P H empty (p+1)).inv ≫
    (Model).complex.d (-((p+1 : ℕ) : ℤ)) (-(p : ℤ)) ≫ (OriginalStrictCellTests.degreeIso J L G R T κ n B hpos hneg hsupport hf hs E P H empty p).hom ≫
      biproduct.π (terms J L G R T κ n B hpos hneg hsupport hf hs p) i

variable (F : A)

def coefficient (q : ℕ) (i : ActualCellThom.Index κ n B q) (f : (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs q i).term ⟶ F) :
    (StrictCoefficientCochains.complex (Model).complex F).X q :=
  (OriginalStrictCellTests.degreeIso J L G R T κ n B hpos hneg hsupport hf hs E P H empty q).hom ≫ biproduct.π (terms J L G R T κ n B hpos hneg hsupport hf hs q) i ≫ f

theorem coefficient_self (q : ℕ) (i : ActualCellThom.Index κ n B q) (f : (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs q i).term ⟶ F) :
    OriginalStrictCellTests.termEquiv J L G R T κ n B hpos hneg hsupport hf hs E P H empty F q
      (coefficient J L G R T κ n B hpos hneg hsupport hf hs E P H empty F q i f) i=
    StrictCellTests.testAddEquiv J (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs q i) F f := by
  change StrictCellTests.testAddEquiv J (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs q i) F
    (biproduct.ι (terms J L G R T κ n B hpos hneg hsupport hf hs q) i ≫
      (OriginalStrictCellTests.degreeIso J L G R T κ n B hpos hneg hsupport hf hs E P H empty q).inv ≫ (OriginalStrictCellTests.degreeIso J L G R T κ n B hpos hneg hsupport hf hs E P H empty q).hom ≫
        biproduct.π (terms J L G R T κ n B hpos hneg hsupport hf hs q) i ≫ f)=_
  rw [Iso.inv_hom_id_assoc,biproduct.ι_π_self_assoc]

theorem coefficient_other (q : ℕ) (i b : ActualCellThom.Index κ n B q) (h : b≠i)
    (f : (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs q i).term ⟶ F) :
    OriginalStrictCellTests.termEquiv J L G R T κ n B hpos hneg hsupport hf hs E P H empty F q
      (coefficient J L G R T κ n B hpos hneg hsupport hf hs E P H empty F q i f) b=0 := by
  change StrictCellTests.testAddEquiv J (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs q b) F
    (biproduct.ι (terms J L G R T κ n B hpos hneg hsupport hf hs q) b ≫
      (OriginalStrictCellTests.degreeIso J L G R T κ n B hpos hneg hsupport hf hs E P H empty q).inv ≫ (OriginalStrictCellTests.degreeIso J L G R T κ n B hpos hneg hsupport hf hs E P H empty q).hom ≫
        biproduct.π (terms J L G R T κ n B hpos hneg hsupport hf hs q) i ≫ f)=_
  rw [Iso.inv_hom_id_assoc,biproduct.ι_π_ne_assoc _ h,zero_comp,map_zero]

theorem differential_test (p : ℕ) (b : ActualCellThom.Index κ n B (p+1))
    (i : ActualCellThom.Index κ n B p) (f : (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs p i).term ⟶ F) :
    OriginalStrictCellTests.termEquiv J L G R T κ n B hpos hneg hsupport hf hs E P H empty F (p+1)
      ((StrictCoefficientCochains.complex (Model).complex F).d p (p+1)
        (coefficient J L G R T κ n B hpos hneg hsupport hf hs E P H empty F p i f)) b=
    StrictCellTests.testAddEquiv J (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs (p+1) b) F
      (block J L G R T κ n B hpos hneg hsupport hf hs E P H empty p b i ≫ f) := by
  rw [StrictCoefficientCochains.differential_apply]
  change StrictCellTests.testAddEquiv J (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs (p+1) b) F
    (biproduct.ι (terms J L G R T κ n B hpos hneg hsupport hf hs (p+1)) b ≫
      (OriginalStrictCellTests.degreeIso J L G R T κ n B hpos hneg hsupport hf hs E P H empty (p+1)).inv ≫ (Model).complex.d (-((p+1 : ℕ) : ℤ)) (-(p : ℤ)) ≫
        (OriginalStrictCellTests.degreeIso J L G R T κ n B hpos hneg hsupport hf hs E P H empty p).hom ≫ biproduct.π (terms J L G R T κ n B hpos hneg hsupport hf hs p) i ≫ f)=_
  simp only [block,Category.assoc]

#print axioms terms
#print axioms block
#print axioms coefficient
#print axioms coefficient_self
#print axioms coefficient_other
#print axioms differential_test
end Verification.OriginalStrictLocalBlocks
