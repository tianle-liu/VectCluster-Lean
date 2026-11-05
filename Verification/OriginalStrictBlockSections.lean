/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalStrictLocalBlocks
import Verification.ActualGlobalBoundary

/-!
# Original Strict Block Sections

Sparse ordered-section tests detect the literal actual local differential.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.OriginalStrictBlockSections
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


variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)

omit [Fintype κ] in
theorem edge_injective (p : ℕ) (b : ActualCellThom.Index κ n B (p+1)) :
    Function.Injective (ActualGlobalBoundary.edgeIndex κ n B p b) := by
  intro v w h
  apply Subtype.ext
  by_contra hn
  have he : b.val.erase v.val = b.val.erase w.val := congrArg Subtype.val h
  have hm : v.val ∈ b.val.erase w.val := Finset.mem_erase.mpr ⟨hn,v.property⟩
  rw [← he] at hm
  exact Finset.not_mem_erase v.val b.val hm

theorem coefficient_self (q : ℕ) (j : ℤ) (i : ActualCellThom.Index κ n B q)
    (f : (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs q i).term ⟶ M j) :
    OriginalOrderedStrictSections.termEquiv J L G R T κ n B hpos hneg hsupport hf hs E P H empty site M N V q j
      (OriginalStrictLocalBlocks.coefficient J L G R T κ n B hpos hneg hsupport hf hs E P H empty (M j) q i f) i =
    OriginalOrderedStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs site M N V q j i
      (StrictCellTests.testAddEquiv J (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs q i) (M j) f) := by
  change (OriginalOrderedStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs site M N V q j i)
    (OriginalStrictCellTests.termEquiv J L G R T κ n B hpos hneg hsupport hf hs E P H empty (M j) q _ i) = _
  rw [OriginalStrictLocalBlocks.coefficient_self]

theorem coefficient_other (q : ℕ) (j : ℤ) (i b : ActualCellThom.Index κ n B q) (h : b≠i)
    (f : (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs q i).term ⟶ M j) :
    OriginalOrderedStrictSections.termEquiv J L G R T κ n B hpos hneg hsupport hf hs E P H empty site M N V q j
      (OriginalStrictLocalBlocks.coefficient J L G R T κ n B hpos hneg hsupport hf hs E P H empty (M j) q i f) b = 0 := by
  change (OriginalOrderedStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs site M N V q j b)
    (OriginalStrictCellTests.termEquiv J L G R T κ n B hpos hneg hsupport hf hs E P H empty (M j) q _ b) = _
  rw [OriginalStrictLocalBlocks.coefficient_other J L G R T κ n B hpos hneg hsupport hf hs E P H empty (M j) q i b h f,map_zero]

theorem differential (p : ℕ) (j : ℤ) (b : ActualCellThom.Index κ n B (p+1))
    (i : ActualCellThom.Index κ n B p)
    (f : (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs p i).term ⟶ M j) :
    OriginalOrderedStrictSections.termEquiv J L G R T κ n B hpos hneg hsupport hf hs E P H empty site M N V (p+1) j
      ((StrictCoefficientCochains.complex (Model).complex (M j)).d p (p+1)
        (OriginalStrictLocalBlocks.coefficient J L G R T κ n B hpos hneg hsupport hf hs E P H empty (M j) p i f)) b =
    OriginalOrderedStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs site M N V (p+1) j b
      (StrictCellTests.testAddEquiv J (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs (p+1) b) (M j)
        (OriginalStrictLocalBlocks.block J L G R T κ n B hpos hneg hsupport hf hs E P H empty p b i ≫ f)) := by
  change (OriginalOrderedStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs site M N V (p+1) j b)
    (OriginalStrictCellTests.termEquiv J L G R T κ n B hpos hneg hsupport hf hs E P H empty (M j) (p+1) _ b) = _
  rw [OriginalStrictLocalBlocks.differential_test]

#print axioms edge_injective
#print axioms coefficient_self
#print axioms coefficient_other
#print axioms differential
end Verification.OriginalStrictBlockSections
