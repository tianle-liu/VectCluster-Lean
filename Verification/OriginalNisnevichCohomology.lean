/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalStrictCohomology
import Verification.StrictNisnevichRepresentability

/-!
# Original Nisnevich Cohomology

Ordinary Nisnevich cohomology is computed by the actual original
strict cellular coefficient complex, via the proved cross-category
universal property and uniform ordinary representability.
-/
noncomputable section
namespace Verification.OriginalNisnevichCohomology
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

variable (HC : StrictCoefficientComparison.StandardHomology (A := A))
variable (Nis : StrictNisnevichInput.Theory A)
variable (NR : StrictNisnevichRepresentability.Standard J L G Nis R)

def cohomologyEquiv (M : A) (q : ℕ) :
    (OriginalStrictCohomology.cochains J L G R T κ n B hpos hneg hsupport hf hs E P H empty M).homology q ≃+
      Nis.cohomology (Spec (CommRingCat.of (Global R κ n B))) M q := by
  letI := GlobalExchangeSmooth.global_smooth_saturated R κ n B hpos hneg hsupport hf hs
  exact (OriginalStrictCohomology.cohomologyEquiv J L G R T κ n B
    hpos hneg hsupport hf hs E P H empty HC M q).trans
    (NR.comparison (Global R κ n B) M q).symm

include T hpos hneg hsupport hf hs E P H empty HC NR in
theorem vanishes_above_height (M : A) (q : ℕ) (hq : StrictCellularGlobal.height κ n B < q) :
    IsZero (Nis.cohomology (Spec (CommRingCat.of (Global R κ n B))) M q) := by
  letI := GlobalExchangeSmooth.global_smooth_saturated R κ n B hpos hneg hsupport hf hs
  letI := OriginalStrictCohomology.ambient_vanishes J L G R T κ n B
    hpos hneg hsupport hf hs E P H empty HC M q hq
  exact StrictNisnevichRepresentability.cohomology_zero J L G Nis R NR (Global R κ n B) M q

#print axioms cohomologyEquiv
#print axioms vanishes_above_height
end Verification.OriginalNisnevichCohomology
