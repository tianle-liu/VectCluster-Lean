/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictAcyclicExistence
import Verification.LocalizedActualCellThom

/-!
# Strict Localized Acyclic

Strict model existence for the actual original exchange space using
homotopy purity only after the ambient localization L. The strict derived
realization J remains a separate functor; no raw-chain purity equivalence,
derived full faithfulness, or ambient homology concentration is assumed.
-/
noncomputable section
namespace Verification.StrictLocalizedAcyclic
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

variable (T : StrictAcyclicExistence.TorusModels J L G R)
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

def cellModel (r : ℕ) : Model J (L.obj (DerivedCategory.Q.obj (FilteredConeComplex.relative
    (PrimeSchemeFiltration.filteredChains (Global R κ n B)
      (fun i => initial R κ n B (Sum.inl i)) G) r))) :=
  ofIso J (LocalizedActualCellThom.relativeIso L G E R κ n B P hpos hneg hsupport hf hs r)
    (FiniteStrictModels.model J (fun i => L.obj (ActualCellThom.localThom G R κ n B r i))
      (StrictAcyclicExistence.localModel J L G R T κ n B hpos hneg hsupport hf hs r))

variable (H : ChainRepresentability (A := A))
variable (empty : ∀ X : Scheme, IsEmpty X → IsZero (L.obj (DerivedCategory.Q.obj (G.obj X))))

def globalModel : Model J (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of (Global R κ n B)))))) := by
  let x := fun i => initial R κ n B (Sum.inl i)
  have hz : IsEmpty ((PrimeSchemeFiltration.stages (Global R κ n B) x).obj 0) := by
    change IsEmpty (PrimeSchemeFiltration.stageOpen (Global R κ n B) x 0)
    rw [show PrimeSchemeFiltration.stageOpen (Global R κ n B) x 0 = ⊥ from
      PrimeCoordinateFiltration.stage_zero x]
    exact ⟨fun p => p.2⟩
  exact StrictFiniteFiltration.globalModel J L H (Global R κ n B) x G
    (empty _ hz) (fun r _ => cellModel J L G R T κ n B hpos hneg hsupport hf hs E P r)

include T hpos hneg hsupport hf hs E P H empty in
theorem exists_bounded_projective_strict_model :
    Nonempty (Model J (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of (Global R κ n B))))))) :=
  ⟨globalModel J L G R T κ n B hpos hneg hsupport hf hs E P H empty⟩

#print axioms cellModel
#print axioms globalModel
#print axioms exists_bounded_projective_strict_model
end Verification.StrictLocalizedAcyclic
