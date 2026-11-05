/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictCellularGlobal
import Verification.StrictCoefficientComparison

/-!
# Original Strict Cohomology

Actual coefficient cochains and cohomological dimension for the
original exchange scheme. The model and its independence-height support
are constructed from the actual filtration. Uniform ordinary derived-Hom
computation is the only extra coefficient-comparison input.
-/
noncomputable section
namespace Verification.OriginalStrictCohomology
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
variable (R : Type) [CommRing R] [Nontrivial R]
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

def cochains (M : A) := StrictCoefficientCochains.complex
  (StrictCellularGlobal.globalModel J L G R T κ n B hpos hneg hsupport hf hs E P H empty).complex M

theorem homology_zero (M : A) (q : ℕ) (hq : StrictCellularGlobal.height κ n B<q) :
    IsZero ((cochains J L G R T κ n B hpos hneg hsupport hf hs E P H empty M).homology q) :=
  StrictCoefficientCochains.homology_zero _ M
    (StrictCellularGlobal.support_lower J L G R T κ n B hpos hneg hsupport hf hs E P H empty) hq

variable (HC : StrictCoefficientComparison.StandardHomology (A := A))

def cohomologyEquiv (M : A) (q : ℕ) :
    (cochains J L G R T κ n B hpos hneg hsupport hf hs E P H empty M).homology q ≃+
      (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of (Global R κ n B))))) ⟶
        J.obj (StrictCoefficientComparison.target M q)) :=
  StrictCoefficientComparison.cohomologyEquiv J HC
    (StrictCellularGlobal.globalModel J L G R T κ n B hpos hneg hsupport hf hs E P H empty)
    (StrictCellularGlobal.support_upper J L G R T κ n B hpos hneg hsupport hf hs E P H empty) M q

include T hpos hneg hsupport hf hs E P H empty HC in
theorem ambient_vanishes (M : A) (q : ℕ) (hq : StrictCellularGlobal.height κ n B<q) :
    Subsingleton (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of (Global R κ n B))))) ⟶
      J.obj (StrictCoefficientComparison.target M q)) :=
  StrictCoefficientComparison.ambient_subsingleton J HC
    (StrictCellularGlobal.globalModel J L G R T κ n B hpos hneg hsupport hf hs E P H empty)
    (StrictCellularGlobal.support_upper J L G R T κ n B hpos hneg hsupport hf hs E P H empty) M q
    (homology_zero J L G R T κ n B hpos hneg hsupport hf hs E P H empty M q hq)

#print axioms cochains
#print axioms homology_zero
#print axioms cohomologyEquiv
#print axioms ambient_vanishes
end Verification.OriginalStrictCohomology
