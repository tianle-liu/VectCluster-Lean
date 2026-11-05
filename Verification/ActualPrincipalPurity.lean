/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrincipalPurityInterface
import Verification.TransverseClosedFiber
import Verification.ActualTransversePairSmooth
import Verification.ActualTransversePurity

/-!
# Actual Principal Purity

Apply the uniform cited principal-purity theorem to the original cluster
transverse pair. Smoothness of all four rings, regularity of the original
parameter, and its exact pullback are proved from the original AS hypotheses.
No paper-specific differential or purity comparison is assumed.
-/
namespace Verification.ActualPrincipalPurity
open CategoryTheory CategoryTheory.Limits Opposite CochainComplex
open Verification.ActualOpenChart Verification.ActualOpenGeometry
open Verification.ActualTransverseSlice Verification.ActualTransverseLocalization
open Verification.ExchangeTransverseSlice Verification.TransverseClosedFiber
universe u w
variable (R ι κ τ : Type u) [CommRing R] [Fintype ι] [Fintype κ]
variable (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
variable (hB : ∀ l i : ι, B (Sum.inl l) (Sum.inl i) = 0) (v : ι)
variable {D : Type*} [Category D] [Abelian D] [HasBinaryBiproducts D] [HasDerivedCategory.{w} D]
variable (F : (Under (CommRingCat.of R))ᵒᵖ ⥤ CochainComplex D ℤ)
variable (T : (Under (CommRingCat.of R))ᵒᵖ ⥤ DerivedCategory D)

theorem principalOpen_eq : PrincipalPairMaps.openMap R
    (Intermediate R ι κ τ j B v) (Slice (characters R ι κ τ B))
    (originalParameter R ι κ τ j B v) Polynomial.X
    (transverseSlice R ι κ τ j B hB v) (transverse_parameter R ι κ τ j B hB v) =
      localizedSlice R ι κ τ j B hB v := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (originalParameter R ι κ τ j B v))
  apply RingHom.ext
  intro z
  rfl

theorem principalCone_eq : PrincipalPurityInterface.pairConeMap R F
    (Intermediate R ι κ τ j B v) (Slice (characters R ι κ τ B))
    (originalParameter R ι κ τ j B v) Polynomial.X
    (transverseSlice R ι κ τ j B hB v) (transverse_parameter R ι κ τ j B hB v) =
      ActualTransversePurity.derivedConeMap R ι κ τ j B hB v F := by
  simp only [PrincipalPurityInterface.pairConeMap, principalOpen_eq]
  rfl

noncomputable def closedArrowIso :
    Arrow.mk (ActualTransversePurity.closedThomMap R ι κ τ j B hB v T) ≅
      Arrow.mk (PrincipalPurityInterface.closedTheoryMap R T
        (Intermediate R ι κ τ j B v) (Slice (characters R ι κ τ B))
        (originalParameter R ι κ τ j B v) Polynomial.X
        (transverseSlice R ι κ τ j B hB v) (transverse_parameter R ι κ τ j B hB v)) :=
  Arrow.isoMk (T.mapIso (fiberEquiv R ι κ τ B).toUnder.op) (Iso.refl _) (by
    change T.map (fiberEquiv R ι κ τ B).toAlgHom.toUnder.op ≫
      T.map (principalClosedMap R ι κ τ j B hB v).toUnder.op =
        T.map (closedSlice R ι κ τ j B hB v).toUnder.op ≫ 𝟙 _
    rw [Category.comp_id, ← Functor.map_comp]
    change T.map ((fiberEquiv R ι κ τ B).toAlgHom.comp
      (principalClosedMap R ι κ τ j B hB v)).toUnder.op = _
    rw [closedMap_fiber])

noncomputable def comparison_AS
    (hf : Function.Injective (columnMap ι κ τ B))
    (hs : FreezingLattice.Saturated (LinearMap.range (columnMap ι κ τ B)))
    (purity : PrincipalPurityInterface.StandardPurity R F T) :
    ActualTransversePurity.PurityComparison R ι κ τ j B hB v F T := by
  have hh := ActualTransversePairSmooth.pair_smooth_AS R ι κ τ j B hB hf hs v
  letI : Algebra.Smooth R (Fiber (characters R ι κ τ B)) := hh.1
  have hq : Algebra.Smooth R (PrincipalPairMaps.Closed (Slice (characters R ι κ τ B)) Polynomial.X) :=
    Algebra.Smooth.of_equiv (fiberEquiv R ι κ τ B).symm
  let P := purity.comparison
    (Intermediate R ι κ τ j B v) (Slice (characters R ι κ τ B))
    (originalParameter R ι κ τ j B v) Polynomial.X
    (transverseSlice R ι κ τ j B hB v) (transverse_parameter R ι κ τ j B hB v)
    (ActualTransverseSmooth.intermediate_smooth_AS R ι κ τ j B v hB hf hs)
    hh.2.2 hh.2.1 hq (ActualTransverseRegular.parameter_regular R ι κ τ j B hB hf v)
    Polynomial.isRegular_X.left
  exact closedArrowIso R ι κ τ j B hB v T ≪≫ P ≪≫
    eqToIso (congrArg Arrow.mk (principalCone_eq R ι κ τ j B hB v F))

#print axioms principalOpen_eq
#print axioms principalCone_eq
#print axioms closedArrowIso
#print axioms comparison_AS
end Verification.ActualPrincipalPurity
