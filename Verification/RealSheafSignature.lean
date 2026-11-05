/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RealTorusScheme
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Real Sheaf Signature

Signature evaluation is defined on actual sections of an actual sheaf:
pull back to Spec R along the real point, then apply ordinary signature.
-/
noncomputable section
namespace Verification.RealSheafSignature
open CategoryTheory AlgebraicGeometry
variable (J : GrothendieckTopology Scheme.{0})
variable (M : Sheaf J (ModuleCat.{0} ℤ))
variable (ordinary : M.val.obj (Opposite.op RealTorusScheme.base) →ₗ[ℤ] ℚ)

abbrev sections (X : Scheme.{0}) := M.val.obj (Opposite.op X)

def evaluation (X : Scheme.{0}) (p : RealTorusScheme.base ⟶ X) :
    sections J M X →ₗ[ℤ] ℚ := ordinary.comp
      ((M.val.map p.op).hom : M.val.obj (Opposite.op X) →ₗ[ℤ]
        M.val.obj (Opposite.op RealTorusScheme.base))

theorem natural {X Y : Scheme.{0}} (u : X ⟶ Y) (p : RealTorusScheme.base ⟶ X) :
    (evaluation J M ordinary X p).comp
      ((M.val.map u.op).hom : M.val.obj (Opposite.op Y) →ₗ[ℤ] M.val.obj (Opposite.op X))=
      evaluation J M ordinary Y (p ≫ u) := by
  apply LinearMap.ext
  intro z
  change ordinary ((M.val.map p.op) ((M.val.map u.op) z))=
    ordinary ((M.val.map (p ≫ u).op) z)
  rw [op_comp,CategoryTheory.Functor.map_comp]
  rfl

variable (α : Type) [Fintype α] [DecidableEq α]

def samples : sections J M (RealTorusScheme.torus α) →ₗ[ℤ] (Finset α → ℚ) where
  toFun z T := evaluation J M ordinary (RealTorusScheme.torus α)
    (RealTorusScheme.point α (RealTorusScheme.sample α T)) z
  map_add' _ _ := by funext T;exact map_add _ _ _
  map_smul' _ _ := by funext T;exact map_smul _ _ _

#print axioms sections
#print axioms evaluation
#print axioms natural
#print axioms samples
end Verification.RealSheafSignature
