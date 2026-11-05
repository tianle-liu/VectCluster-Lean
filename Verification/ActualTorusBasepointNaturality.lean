/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualTorusReducedRestriction

/-!
# Actual Torus Basepoint Naturality

The actual torus-face map preserves the Laurent basepoint u=1.
This is a ring-coordinate calculation, and therefore gives the basepoint
square for every functor before or after localization.
-/
noncomputable section
namespace Verification.ActualTorusBasepointNaturality
open CategoryTheory Opposite
open Verification.ActualOpenChart Verification.ExchangeTransverseSlice
open Verification.ActualTorusReducedRestriction
universe u
variable (R ι κ τ : Type u) [CommRing R] [Fintype κ]
variable (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) (v : ι)
local notation "χ" => characters R ι κ τ B
local notation "New" => Fiber (characters R ι κ τ B)
local notation "Old" => OldBase R ι κ τ B v

theorem atOne_square :
    (LaurentBasepoint.atOne R New).comp (ActualTorusFace.torusFace R ι κ τ B v) =
      (fiberRestriction R ι κ τ B v).comp (LaurentBasepoint.atOne R Old) := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial Old))
  apply Polynomial.ringHom_ext
  · intro a
    change LaurentBasepoint.atOne R New
      (ActualTorusFace.torusFace R ι κ τ B v (algebraMap Old (LaurentBasepoint.Laurent Old) a)) =
      fiberRestriction R ι κ τ B v
        (LaurentBasepoint.atOne R Old (algebraMap Old (LaurentBasepoint.Laurent Old) a))
    have hc := AlgHom.congr_fun (coefficient_square R ι κ τ B v) a
    change ActualTorusFace.torusFace R ι κ τ B v (algebraMap Old (LaurentBasepoint.Laurent Old) a) =
      algebraMap New (LaurentBasepoint.Laurent New) (fiberRestriction R ι κ τ B v a) at hc
    rw [hc]
    have hn := AlgHom.congr_fun (LaurentBasepoint.atOne_coefficient R New) (fiberRestriction R ι κ τ B v a)
    have ho := AlgHom.congr_fun (LaurentBasepoint.atOne_coefficient R Old) a
    exact hn.trans (congrArg (fiberRestriction R ι κ τ B v) ho).symm
  · change LaurentBasepoint.atOne R New
      (ActualTorusFace.torusFace R ι κ τ B v
        (algebraMap (Polynomial Old) (LaurentBasepoint.Laurent Old) Polynomial.X)) =
      fiberRestriction R ι κ τ B v
        (LaurentBasepoint.atOne R Old
          (algebraMap (Polynomial Old) (LaurentBasepoint.Laurent Old) Polynomial.X))
    have hx : ActualTorusFace.torusFace R ι κ τ B v
        (algebraMap (Polynomial Old) (LaurentBasepoint.Laurent Old) Polynomial.X) =
        algebraMap (Polynomial New) (LaurentBasepoint.Laurent New) Polynomial.X := by
      change LocalTransverseTorusFace.torusFace χ v
        (algebraMap (Polynomial Old) (LaurentBasepoint.Laurent Old) Polynomial.X) = _
      rw [← LocalTransverseOpen.targetUnit_val]
      exact LocalTransverseTorusFace.torusFace_parameter χ v
    rw [hx, LaurentBasepoint.atOne_parameter, LaurentBasepoint.atOne_parameter, map_one]

variable {C : Type*} [Category C] (F : (Under (CommRingCat.of R))ᵒᵖ ⥤ C)
theorem section_square :
    LaurentBasepoint.sectionMap R New F ≫ F.map (ActualTorusFace.torusFace R ι κ τ B v).toUnder.op =
      F.map (fiberRestriction R ι κ τ B v).toUnder.op ≫ LaurentBasepoint.sectionMap R Old F := by
  unfold LaurentBasepoint.sectionMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun f => F.map (AlgHom.toUnder f).op) (atOne_square R ι κ τ B v)

#print axioms atOne_square
#print axioms section_square
end Verification.ActualTorusBasepointNaturality
