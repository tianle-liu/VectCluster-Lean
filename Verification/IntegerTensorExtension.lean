/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalWittIntegerModel
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Integer Tensor Extension

Ordinary tensor extension by an arbitrary abelian coefficient group,
with the actual tensor map on every differential.
-/
noncomputable section
open scoped TensorProduct
namespace Verification.IntegerTensorExtension
open CategoryTheory
variable (R : Type) [CommRing R] (A : Type) [AddCommGroup A] [Module R A]

def functor : ModuleCat.{0} R ⥤ ModuleCat.{0} R where
  obj M := ModuleCat.of R (M ⊗[R] A)
  map f := ModuleCat.ofHom (TensorProduct.map f.hom (LinearMap.id : A →ₗ[R] A))
  map_id M := by
    apply ModuleCat.hom_ext
    exact TensorProduct.map_id
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact (TensorProduct.map_comp g.hom f.hom (LinearMap.id : A →ₗ[R] A) (LinearMap.id : A →ₗ[R] A))

def additive : (functor R A).Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    exact TensorProduct.map_add_left f.hom g.hom (LinearMap.id : A →ₗ[R] A)

attribute [instance] additive

def complex (C : CochainComplex (ModuleCat.{0} R) ℕ) : CochainComplex (ModuleCat.{0} R) ℕ :=
  ((functor R A).mapHomologicalComplex (ComplexShape.up ℕ)).obj C

theorem differential (C : CochainComplex (ModuleCat.{0} R) ℕ) (p q : ℕ) :
    ((complex R A C).d p q).hom = TensorProduct.map (C.d p q).hom (LinearMap.id : A →ₗ[R] A) := rfl

#print axioms functor
#print axioms additive
#print axioms complex
#print axioms differential
end Verification.IntegerTensorExtension
