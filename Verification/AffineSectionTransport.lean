/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PolynomialSectionIso

/-!
# Affine Section Transport

Transport of the proved polynomial zero-section inverse through an actual
algebra coordinate equivalence. The only theory input is inversion of the
polynomial projection, not inversion of the closed-stratum map.
-/
namespace Verification.AffineSectionTransport
open CategoryTheory Opposite
open Verification.PolynomialSectionIso
universe u
variable (R A ι W : Type u) [CommRing R] [CommRing A] [CommRing W]
variable [Algebra R A] [Algebra R W]
variable (e : W ≃ₐ[R] MvPolynomial ι A)
variable {D : Type*} [Category D] (F : (Under (CommRingCat.of R))ᵒᵖ ⥤ D)

noncomputable def sectionIso [IsIso (projectionMap R A ι F)] :
    F.obj (op (CommRingCat.mkUnder (CommRingCat.of R) A)) ≅
      F.obj (op (CommRingCat.mkUnder (CommRingCat.of R) W)) :=
  zeroSectionIso R A ι F ≪≫ F.mapIso e.toUnder.op

theorem sectionIso_hom [IsIso (projectionMap R A ι F)] :
    (sectionIso R A ι W e F).hom =
      F.map ((zeroEvaluation R A ι).comp e.toAlgHom).toUnder.op := by
  change F.map (zeroEvaluation R A ι).toUnder.op ≫ F.map e.toAlgHom.toUnder.op = _
  rw [← Functor.map_comp]
  rfl

theorem actual_section_isIso (f : W →ₐ[R] A)
    (hf : f = (zeroEvaluation R A ι).comp e.toAlgHom)
    [IsIso (projectionMap R A ι F)] : IsIso (F.map f.toUnder.op) := by
  rw [hf, ← sectionIso_hom R A ι W e F]
  infer_instance

#print axioms sectionIso
#print axioms sectionIso_hom
#print axioms actual_section_isIso
end Verification.AffineSectionTransport
