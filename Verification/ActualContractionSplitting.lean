/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualTransverseBasepoint
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Actual Contraction Splitting

The contraction summand is the actual categorical kernel of projection
from the punctured transverse line. Its decomposition uses the actual u=1
section, so the normalization of the reduced factor is fixed geometrically.
-/
namespace Verification.ActualContractionSplitting
open CategoryTheory CategoryTheory.Limits Opposite
open Verification.ActualOpenChart Verification.ActualTransverseLocalization
open Verification.ExchangeTransverseSlice Verification.ActualTransverseBasepoint
universe u
variable (R ι κ τ : Type u) [CommRing R] [Fintype κ]
variable (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
variable {D : Type*} [Category D] [Abelian D]
variable (F : (Under (CommRingCat.of R))ᵒᵖ ⥤ D)

noncomputable def reduced := kernel (projection R ι κ τ B F)

noncomputable def contraction :
    F.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (OpenTarget R ι κ τ B))) ⟶
      reduced R ι κ τ B F :=
  kernel.lift (projection R ι κ τ B F)
    (𝟙 _ - projection R ι κ τ B F ≫ sectionMap R ι κ τ B F) (by
      rw [Preadditive.sub_comp, Category.id_comp, Category.assoc,
        section_projection, Category.comp_id, sub_self])

theorem contraction_inclusion : contraction R ι κ τ B F ≫ kernel.ι (projection R ι κ τ B F) =
    𝟙 _ - projection R ι κ τ B F ≫ sectionMap R ι κ τ B F :=
  kernel.lift_ι _ _ _

theorem inclusion_contraction : kernel.ι (projection R ι κ τ B F) ≫ contraction R ι κ τ B F = 𝟙 _ := by
  apply (cancel_mono (kernel.ι (projection R ι κ τ B F))).1
  rw [Category.assoc, contraction_inclusion, Preadditive.comp_sub, Category.comp_id,
    ← Category.assoc, kernel.condition, zero_comp, sub_zero, Category.id_comp]

theorem section_contraction : sectionMap R ι κ τ B F ≫ contraction R ι κ τ B F = 0 := by
  apply (cancel_mono (kernel.ι (projection R ι κ τ B F))).1
  rw [Category.assoc, contraction_inclusion, Preadditive.comp_sub, Category.comp_id,
    ← Category.assoc, section_projection, Category.id_comp, sub_self, zero_comp]

noncomputable def splitting :
    (ShortComplex.mk (kernel.ι (projection R ι κ τ B F)) (projection R ι κ τ B F)
      (kernel.condition _)).Splitting where
  r := contraction R ι κ τ B F
  s := sectionMap R ι κ τ B F
  f_r := inclusion_contraction R ι κ τ B F
  s_g := section_projection R ι κ τ B F
  id := by
    change contraction R ι κ τ B F ≫ kernel.ι (projection R ι κ τ B F) +
      projection R ι κ τ B F ≫ sectionMap R ι κ τ B F = _
    rw [contraction_inclusion, sub_add_cancel]

attribute [local instance] Abelian.hasFiniteBiproducts

noncomputable def decomposition :
    F.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (OpenTarget R ι κ τ B))) ≅
      reduced R ι κ τ B F ⊞
        F.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (Fiber (characters R ι κ τ B)))) :=
  (splitting R ι κ τ B F).isoBinaryBiproduct

theorem decomposition_contraction : (decomposition R ι κ τ B F).hom ≫ biprod.fst =
    contraction R ι κ τ B F := by
  exact biprod.lift_fst _ _

theorem decomposition_projection : (decomposition R ι κ τ B F).hom ≫ biprod.snd =
    projection R ι κ τ B F := by
  exact biprod.lift_snd _ _

#print axioms reduced
#print axioms contraction
#print axioms contraction_inclusion
#print axioms inclusion_contraction
#print axioms section_contraction
#print axioms splitting
#print axioms decomposition
#print axioms decomposition_contraction
#print axioms decomposition_projection
end Verification.ActualContractionSplitting
