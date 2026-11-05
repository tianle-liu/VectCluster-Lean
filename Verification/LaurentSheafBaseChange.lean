/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualSheafContractionRestriction

/-!
# Laurent Sheaf Base Change

The ordinary base change of a Laurent line and of its true u=1
coefficient-sheaf kernel, over arbitrary coefficient algebras.
-/
noncomputable section
namespace Verification.LaurentSheafBaseChange
open CategoryTheory AlgebraicGeometry Opposite
variable (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
variable (f : S →ₐ[R] T)

def polynomialMap : Polynomial S →ₐ[R] LaurentBasepoint.Laurent T :=
  Polynomial.aevalTower ((LaurentBasepoint.coefficient R T).comp f)
    (algebraMap (Polynomial T) (LaurentBasepoint.Laurent T) Polynomial.X)

theorem polynomial_units (m : Submonoid.powers (Polynomial.X : Polynomial S)) :
    IsUnit (polynomialMap R S T f m) := by
  obtain ⟨n,hn⟩ := m.2
  rw [← hn,map_pow]
  change IsUnit ((Polynomial.aevalTower _ _ Polynomial.X) ^ n)
  rw [Polynomial.aevalTower_X]
  exact (IsLocalization.Away.algebraMap_isUnit (Polynomial.X : Polynomial T)).pow n

def laurentMap : LaurentBasepoint.Laurent S →ₐ[R] LaurentBasepoint.Laurent T :=
  IsLocalization.liftAlgHom (polynomial_units R S T f)

theorem map_polynomial (p : Polynomial S) :
    laurentMap R S T f (algebraMap (Polynomial S) (LaurentBasepoint.Laurent S) p) =
      polynomialMap R S T f p := IsLocalization.lift_eq _ _

theorem map_coefficient (a : S) :
    laurentMap R S T f (algebraMap S (LaurentBasepoint.Laurent S) a) =
      algebraMap T (LaurentBasepoint.Laurent T) (f a) := by
  rw [IsScalarTower.algebraMap_apply S (Polynomial S) (LaurentBasepoint.Laurent S),map_polynomial]
  exact Polynomial.aevalTower_C _ _ _

theorem map_parameter :
    laurentMap R S T f (algebraMap (Polynomial S) (LaurentBasepoint.Laurent S) Polynomial.X) =
      algebraMap (Polynomial T) (LaurentBasepoint.Laurent T) Polynomial.X := by
  rw [map_polynomial]
  exact Polynomial.aevalTower_X _ _

theorem atOne_square :
    (LaurentBasepoint.atOne R T).comp (laurentMap R S T f) =
      f.comp (LaurentBasepoint.atOne R S) := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial S))
  apply Polynomial.ringHom_ext
  · intro a
    change LaurentBasepoint.atOne R T
      (laurentMap R S T f (algebraMap S (LaurentBasepoint.Laurent S) a)) =
      f (LaurentBasepoint.atOne R S (algebraMap S (LaurentBasepoint.Laurent S) a))
    rw [map_coefficient]
    exact (AlgHom.congr_fun (LaurentBasepoint.atOne_coefficient R T) (f a)).trans
      (congrArg f (AlgHom.congr_fun (LaurentBasepoint.atOne_coefficient R S) a)).symm
  · change LaurentBasepoint.atOne R T
      (laurentMap R S T f (algebraMap (Polynomial S) (LaurentBasepoint.Laurent S) Polynomial.X)) =
      f (LaurentBasepoint.atOne R S (algebraMap (Polynomial S) (LaurentBasepoint.Laurent S) Polynomial.X))
    rw [map_parameter, LaurentBasepoint.atOne_parameter, LaurentBasepoint.atOne_parameter, map_one]

variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ)) (q : ℤ)

theorem kernel_square
    (a : (N q).val.obj (op (Spec (CommRingCat.of (LaurentBasepoint.Laurent S))))) :
    AffineSheafContraction.sheafAtOne R T site N q
      (ActualSheafContractionRestriction.pullback site (N q) (laurentMap R S T f).toRingHom a) =
    ActualSheafContractionRestriction.pullback site (N q) f.toRingHom
      (AffineSheafContraction.sheafAtOne R S site N q a) := by
  have h := congrArg (fun g : LaurentBasepoint.Laurent S →ₐ[R] T =>
    ActualSheafContractionRestriction.pullback site (N q) g.toRingHom) (atOne_square R S T f)
  change ActualSheafContractionRestriction.pullback site (N q)
      ((LaurentBasepoint.atOne R T).toRingHom.comp (laurentMap R S T f).toRingHom) =
    ActualSheafContractionRestriction.pullback site (N q)
      (f.toRingHom.comp (LaurentBasepoint.atOne R S).toRingHom) at h
  rw [ActualSheafContractionRestriction.pullback_comp, ActualSheafContractionRestriction.pullback_comp] at h
  exact DFunLike.congr_fun h a

def kernelMap : (AffineSheafContraction.sheafAtOne R S site N q).ker →+
    (AffineSheafContraction.sheafAtOne R T site N q).ker where
  toFun a := ⟨ActualSheafContractionRestriction.pullback site (N q) (laurentMap R S T f).toRingHom a.val, by
    change AffineSheafContraction.sheafAtOne R T site N q _ = 0
    rw [kernel_square]
    exact (congrArg (ActualSheafContractionRestriction.pullback site (N q) f.toRingHom) a.property).trans (map_zero _)⟩
  map_zero' := by apply Subtype.ext; simp only [AddSubgroup.coe_zero, map_zero]
  map_add' a b := by apply Subtype.ext; simp only [AddSubgroup.coe_add, map_add]

#print axioms polynomialMap
#print axioms polynomial_units
#print axioms laurentMap
#print axioms map_polynomial
#print axioms map_coefficient
#print axioms map_parameter
#print axioms atOne_square
#print axioms kernel_square
#print axioms kernelMap
end Verification.LaurentSheafBaseChange
