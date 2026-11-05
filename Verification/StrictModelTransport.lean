/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictProjectiveModel

/-!
# Strict Model Transport

Transport of an actual strict universal model along an isomorphism
of strict complexes. This does not assert any full faithfulness of J.
-/
noncomputable section
namespace Verification.StrictModelTransport
open CategoryTheory CategoryTheory.Limits
open Verification.StrictProjectiveModel
universe w
variable {A : Type*} [Category A] [Abelian A] [HasBinaryBiproducts A] [HasDerivedCategory.{w} A]
variable {D : Type*} [Category D] [Preadditive D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable {X : D} (M : Model J X) (K : CochainComplex A ℤ) (e : M.complex ≅ K)

def ofComplexIso : Model J X where
  complex := K
  bounded := by
    obtain ⟨a,b,ha,hb⟩ := M.bounded
    refine ⟨a,b,?_,?_⟩
    · rw [CochainComplex.isStrictlyGE_iff] at ha ⊢
      exact fun i hi => (ha i hi).of_iso (HomologicalComplex.Hom.isoApp e i).symm
    · rw [CochainComplex.isStrictlyLE_iff] at hb ⊢
      exact fun i hi => (hb i hi).of_iso (HomologicalComplex.Hom.isoApp e i).symm
  projective i := Projective.of_iso (HomologicalComplex.Hom.isoApp e i) (M.projective i)
  comparison := M.comparison ≫ J.map (DerivedCategory.Q.map e.hom)
  universal := ActualStrictCone.universal_postcompose_iso J M.comparison
    (DerivedCategory.Q.mapIso e) M.universal

#print axioms ofComplexIso
end Verification.StrictModelTransport
