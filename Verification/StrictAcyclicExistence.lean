/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictFiniteFiltration
import Verification.FiniteStrictModels
import Verification.CompatibleTorusThom

/-!
# Strict Acyclic Existence

The existence part of the original acyclic cellular model: standard
strict torus--Thom models are transported through the actual AS stratum
isomorphisms, summed, and glued through the finite open filtration.
The asserted result is a strict model, not an ambient quasi-isomorphism or
an identification of its differential with the explicit cellular matrix.
-/
noncomputable section
namespace Verification.StrictAcyclicExistence
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

/-- Input only on standard affine split-torus Thom spaces. No exchange
stratum or whole exchange variety is present in this standard input. -/
structure TorusModels where
  model : ∀ (ι τ κ : Type) [Fintype ι] [Fintype τ] [Fintype κ],
    Model J (L.obj (TorusThomInput.thom R ι τ κ G))

variable (T : TorusModels J L G R)
variable [Nontrivial R] (κ : Type) [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hf : ∀ I, Independent (laterWeights κ n B) I →
  Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (hs : ∀ I, Independent (laterWeights κ n B) I →
  FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)))

def localModel (r : ℕ) (i : ActualCellThom.Index κ n B r) :
    Model J (L.obj (ActualCellThom.localThom G R κ n B r i)) :=
  ofIso J (L.mapIso (CompatibleTorusThom.explicitIso G R κ n B hpos hneg hsupport hf hs r i))
    (T.model (Selected n i.val) (Selected n i.val)
      (Fin (IndependentStratumTorus.torusRank κ n i.val B)))

variable (E : OpenConeExcision.StandardExcision G) (P : CoordinatePurityInput.StandardPurity R G)

def cellModel (r : ℕ) : Model J (L.obj (DerivedCategory.Q.obj (FilteredConeComplex.relative
    (PrimeSchemeFiltration.filteredChains (Global R κ n B)
      (fun i => initial R κ n B (Sum.inl i)) G) r))) :=
  ofIso J ((L.mapIso (ActualCellThom.relativeIso G E R κ n B P hpos hneg hsupport hf hs r)) ≪≫
    L.mapBiproduct (ActualCellThom.localThom G R κ n B r))
    (FiniteStrictModels.model J (fun i => L.obj (ActualCellThom.localThom G R κ n B r i))
      (localModel J L G R T κ n B hpos hneg hsupport hf hs r))

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

#print axioms TorusModels
#print axioms localModel
#print axioms cellModel
#print axioms globalModel
#print axioms exists_bounded_projective_strict_model
end Verification.StrictAcyclicExistence
