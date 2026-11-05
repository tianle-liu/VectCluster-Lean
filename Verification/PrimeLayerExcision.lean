/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OpenConeExcision
import Verification.PrimeLayerCover
import Verification.PrimeSchemeFiltration

/-!
# Prime Layer Excision

Uniform open excision is applied to the actual coordinate filtration.
Every covering and intersection condition is proved internally. The global
relative cone, and its boundary on each summand, are identified by the
canonical inclusion maps of actual open subschemes.
-/
noncomputable section
namespace Verification.PrimeLayerExcision
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.PrimeCoordinateFiltration Verification.PrimeLayerCover
universe w
variable (A V : Type) [CommRing A] [Fintype V] [DecidableEq V]
variable (x : V → A) (Allowed : Finset V → Prop)
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)

instance indexFintype (r : ℕ) : Fintype (Index Allowed r) := Fintype.ofFinite _

def openChains : (Spec (CommRingCat.of A)).Opens ⥤ CochainComplex C ℤ :=
  (Spec (CommRingCat.of A)).restrictFunctor ⋙ Over.forget _ ⋙ G

def localRelative (r : ℕ) (i : Index Allowed r) : DerivedCategory C :=
  OpenConeExcision.localCone (Spec (CommRingCat.of A)) (openChains A G)
    (stage x r) (chart x Allowed r) i

def assembly (r : ℕ) : (⨁ fun i : Index Allowed r => localRelative A V x Allowed G r i) ⟶
    DerivedCategory.Q.obj (FilteredConeComplex.relative (PrimeSchemeFiltration.filteredChains A x G) r) :=
  OpenConeExcision.assembly (Spec (CommRingCat.of A)) (openChains A G)
    (stage x r) (stage x (r+1)) (stage_mono x (Nat.le_succ r))
    (chart x Allowed r) (chart_le_stage x Allowed r)

variable (hall : ∀ p : PrimeSpectrum A,Allowed (zeroSet x p))

include E hall in
theorem assembly_isIso (r : ℕ) : IsIso (assembly A V x Allowed G r) :=
  E.isIso_assembly _ _ _ _ (Index Allowed r) _ _ (cover x Allowed r hall) (overlap x Allowed r)

def relativeIso (r : ℕ) : (⨁ fun i : Index Allowed r => localRelative A V x Allowed G r i) ≅
    DerivedCategory.Q.obj (FilteredConeComplex.relative (PrimeSchemeFiltration.filteredChains A x G) r) := by
  letI := assembly_isIso A V x Allowed G E hall r
  exact asIso (assembly A V x Allowed G r)

theorem relativeIso_boundary (r : ℕ) (i : Index Allowed r) :
    biproduct.ι (localRelative A V x Allowed G r) i ≫ (relativeIso A V x Allowed G E hall r).hom ≫
      TransverseDerivedBoundary.boundary
        (FilteredConeComplex.inclusion (PrimeSchemeFiltration.filteredChains A x G) r) =
    TransverseDerivedBoundary.boundary (OpenConeExcision.localArrow
      (Spec (CommRingCat.of A)) (openChains A G) (stage x r) (chart x Allowed r) i) ≫
      DerivedCategory.Q.map (((openChains A G).map (homOfLE inf_le_left))⟦(1 : ℤ)⟧') := by
  rw [← Category.assoc]
  change (biproduct.ι _ i ≫ OpenConeExcision.assembly (Spec (CommRingCat.of A))
    (openChains A G) (stage x r) (stage x (r+1)) (stage_mono x (Nat.le_succ r))
    (chart x Allowed r) (chart_le_stage x Allowed r)) ≫ _ = _
  rw [OpenConeExcision.assembly_inclusion]
  exact OpenConeExcision.local_boundary _ _ _ _ _ _ _ i

section Actual
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)

def actualRelativeIso (r : ℕ) := relativeIso (Global R κ n B) (Fin n)
  (fun i => initial R κ n B (Sum.inl i)) (Independent (laterWeights κ n B)) G E
    (actual_zeroSet_independent R κ n B hpos hneg hsupport) r

end Actual
#print axioms indexFintype
#print axioms openChains
#print axioms localRelative
#print axioms assembly
#print axioms assembly_isIso
#print axioms relativeIso
#print axioms relativeIso_boundary
#print axioms actualRelativeIso
end Verification.PrimeLayerExcision
