/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LaurentSheafBaseChange

/-!
# Actual Laurent Sheaf Base Change

The actual character-fiber face is ordinary Laurent base change.
Consequently its genuine u=1 kernel restriction is the ordinary kernel map.
-/
noncomputable section
namespace Verification.ActualLaurentSheafBaseChange
open CategoryTheory AlgebraicGeometry Opposite
variable (R ι κ τ : Type) [CommRing R] [Fintype κ]
variable (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) (v : ι)
local notation "New" => ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R ι κ τ B)
local notation "Old" => ActualTorusReducedRestriction.OldBase R ι κ τ B v

theorem torusFace_eq : ActualTorusFace.torusFace R ι κ τ B v =
    LaurentSheafBaseChange.laurentMap R Old New
      (ActualTorusReducedRestriction.fiberRestriction R ι κ τ B v) := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial Old))
  apply Polynomial.ringHom_ext
  · intro a
    change ActualTorusFace.torusFace R ι κ τ B v (algebraMap Old (LaurentBasepoint.Laurent Old) a) =
      LaurentSheafBaseChange.laurentMap R Old New
        (ActualTorusReducedRestriction.fiberRestriction R ι κ τ B v)
        (algebraMap Old (LaurentBasepoint.Laurent Old) a)
    rw [LaurentSheafBaseChange.map_coefficient]
    exact AlgHom.congr_fun (ActualTorusReducedRestriction.coefficient_square R ι κ τ B v) a
  · change ActualTorusFace.torusFace R ι κ τ B v
      (algebraMap (Polynomial Old) (LaurentBasepoint.Laurent Old) Polynomial.X) =
      LaurentSheafBaseChange.laurentMap R Old New
        (ActualTorusReducedRestriction.fiberRestriction R ι κ τ B v)
        (algebraMap (Polynomial Old) (LaurentBasepoint.Laurent Old) Polynomial.X)
    rw [LaurentSheafBaseChange.map_parameter]
    change LocalTransverseTorusFace.torusFace (ActualOpenChart.characters R ι κ τ B) v
      (algebraMap (Polynomial Old) (LaurentBasepoint.Laurent Old) Polynomial.X) = _
    rw [← LocalTransverseOpen.targetUnit_val]
    exact LocalTransverseTorusFace.torusFace_parameter _ v

variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ)) (q : ℤ)

theorem kernelMap_eq : ActualSheafContractionRestriction.restriction site R ι κ τ B v N q =
    LaurentSheafBaseChange.kernelMap R Old New
      (ActualTorusReducedRestriction.fiberRestriction R ι κ τ B v) site N q := by
  apply AddMonoidHom.ext
  intro a
  apply Subtype.ext
  change ActualSheafContractionRestriction.pullback site (N q)
    (ActualTorusFace.torusFace R ι κ τ B v).toRingHom a.val =
    ActualSheafContractionRestriction.pullback site (N q)
      (LaurentSheafBaseChange.laurentMap R Old New
        (ActualTorusReducedRestriction.fiberRestriction R ι κ τ B v)).toRingHom a.val
  rw [torusFace_eq]

#print axioms torusFace_eq
#print axioms kernelMap_eq
end Verification.ActualLaurentSheafBaseChange
