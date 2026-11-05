/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.TransverseDerivedBoundary

/-!
# Cone Factor Through Identity

A square whose ambient map factors through the target source induces
zero on actual derived cones. The proof factors the cone map through the
contractible cone of an identity, rather than assuming support vanishing.
-/
noncomputable section
namespace Verification.ConeFactorThroughIdentity
open CategoryTheory CategoryTheory.Limits CochainComplex
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]

theorem identityCone_zero (X : CochainComplex C ℤ) :
    IsZero (DerivedCategory.Q.obj (mappingCone (𝟙 X))) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  have h : DerivedCategory.Q.map (𝟙 (mappingCone (𝟙 X))) = DerivedCategory.Q.map 0 :=
    HomologicalComplexUpToQuasiIso.Q_map_eq_of_homotopy (mappingCone.homotopyToZeroOfId X)
  simpa only [CategoryTheory.Functor.map_id, Functor.map_zero] using h

theorem map_zero {U V U' V' : CochainComplex C ℤ} (f : U ⟶ V) (g : U' ⟶ V')
    (a : U ⟶ U') (b : V ⟶ V') (h : f ≫ b = a ≫ g)
    (c : V ⟶ U') (hc : f ≫ c = a) (hb : c ≫ g = b) :
    TransverseDerivedBoundary.coneMap f g a b h = 0 := by
  let t := mappingCone.map f (𝟙 V) f (𝟙 V) (by simp)
  let z := mappingCone.map (𝟙 V) g c b (by simpa only [Category.id_comp] using hb.symm)
  have he : t ≫ z = TransverseConeBoundary.coneMap f g a b h := by
    dsimp only [t,z,TransverseConeBoundary.coneMap]
    rw [← mappingCone.map_comp]
    simp only [hc,Category.id_comp]
  change DerivedCategory.Q.map (TransverseConeBoundary.coneMap f g a b h) = 0
  rw [← he, CategoryTheory.Functor.map_comp]
  rw [(identityCone_zero V).eq_of_tgt (DerivedCategory.Q.map t) 0, zero_comp]

#print axioms identityCone_zero
#print axioms map_zero
end Verification.ConeFactorThroughIdentity
