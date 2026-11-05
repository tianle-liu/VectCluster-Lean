/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SmithScaledComplex
import Verification.SmithScalarExtension

/-!
# Smith Extended Complex

Actual scalar extension and scaling of the simultaneous Smith chain
isomorphism. This supplies the integral-complex to h-times-Smith-blocks step
over an arbitrary commutative coefficient algebra.
-/

noncomputable section
namespace Verification.SmithExtendedComplex
open CategoryTheory
open scoped TensorProduct
open Verification.SmithComplexCoordinates Verification.SmithComplex
open Verification.SmithScaledComplex

variable {R : Type} [CommRing R] (S : Type) [CommRing S] [Algebra R S]

/-- The actual tensor extension functor, using the given coefficient-algebra action. -/
def extensionFunctor : ModuleCat.{0} R ⥤ ModuleCat.{0} S where
  obj M := ModuleCat.of S (S ⊗[R] M)
  map f := ModuleCat.ofHom (TensorProduct.AlgebraTensorModule.map LinearMap.id f.hom)
  map_id M := by
    apply ModuleCat.hom_ext
    exact TensorProduct.AlgebraTensorModule.map_id
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact TensorProduct.AlgebraTensorModule.map_comp LinearMap.id LinearMap.id g.hom f.hom

instance extensionFunctor_additive : (extensionFunctor (R := R) S).Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    exact TensorProduct.AlgebraTensorModule.map_add_right LinearMap.id f.hom g.hom

/-- Extend every object and differential by the actual tensor functor. -/
def extendComplex (C : CochainComplex (ModuleCat.{0} R) ℤ) :
    CochainComplex (ModuleCat.{0} S) ℤ :=
  ((extensionFunctor (R := R) S).mapHomologicalComplex (ComplexShape.up ℤ)).obj C

variable [IsDomain R] [IsPrincipalIdealRing R]
variable (C : CochainComplex (ModuleCat.{0} R) ℤ)
variable [∀ n, Module.Free R (C.X n)] [∀ n, Module.Finite R (C.X n)]

/-- The full extended hA complex is isomorphic to the extended scalar-block complex. -/
def extendedSmithIso (h : S) :
    scale h (extendComplex S C) ≅ scale h (extendComplex S (normalComplex C)) :=
  scaleIso h (((extensionFunctor (R := R) S).mapHomologicalComplex
    (ComplexShape.up ℤ)).mapIso (smithIso C))

/-- On a lifted pair generator the actual extended differential is multiplication by h a_i. -/
theorem extended_pair (h : S) (n : ℤ) (i : Fin (boundaryRank C (n+1))) :
    ((scale h (extendComplex S (normalComplex C))).d n (n+1)).hom
        (1 ⊗ₜ[R] (0,Finsupp.single i 1)) =
      (h * algebraMap R S ((smith C (n+1)).a i)) •
        (1 ⊗ₜ[R] (Finsupp.single ((smith C (n+1)).f i) 1,0)) := by
  change h • ((extensionFunctor (R := R) S).map
    ((normalComplex C).d n (n+1))).hom (1 ⊗ₜ[R] (0,Finsupp.single i 1)) = _
  rw [normalComplex_d]
  change h • (1 ⊗ₜ[R] normalDifferential C n (0,Finsupp.single i 1)) = _
  rw [normalDifferential_pair]
  have hpair : ((Finsupp.single ((smith C (n+1)).f i) (1 * (smith C (n+1)).a i),0) :
      NormalModule C (n+1)) =
      (smith C (n+1)).a i • (Finsupp.single ((smith C (n+1)).f i) 1,0) := by simp
  rw [hpair, TensorProduct.tmul_smul,
    ← IsScalarTower.algebraMap_smul S ((smith C (n+1)).a i), smul_smul]

#print axioms extensionFunctor
#print axioms extensionFunctor_additive
#print axioms extendComplex
#print axioms extendedSmithIso
#print axioms extended_pair

end Verification.SmithExtendedComplex
