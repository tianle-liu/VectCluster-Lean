/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ProjectiveClasses

/-!
# Projective Grothendieck

The universal Grothendieck group of actual finite projective modules.
Its direct-sum relation also holds for every actual short exact sequence,
whose splitting is constructed from projectivity.
-/
noncomputable section
universe u v
namespace Verification.ProjectiveGrothendieck
open Verification.ProjectiveClasses
variable (R : Type u) [CommRing R]

def inclusion : IsoClass R →+ Completion R :=
  (AddLocalization.addMonoidOf (⊤ : AddSubmonoid (IsoClass R))).toAddMonoidHom

theorem inclusion_class (P : Object R) : inclusion R (classOf R P) = completionClass R P := rfl

theorem completionClass_add (P Q : Object R) :
    completionClass R (of R (P × Q)) = completionClass R P + completionClass R Q := by
  change inclusion R (classOf R (of R (P × Q))) = _
  rw [classOf_add, map_add]
  rfl

variable {G : Type v} [AddCommGroup G]
variable (f : Object R → G)
variable (hi : ∀ P Q : Object R, Nonempty (P ≃ₗ[R] Q) → f P=f Q)
variable (hz : f (of R (Fin 0 → R))=0)
variable (ha : ∀ P Q : Object R, f (of R (P × Q))=f P+f Q)

def classMap : IsoClass R →+ G where
  toFun := Quotient.lift f hi
  map_zero' := hz
  map_add' := by
    intro a b
    induction a using Quotient.inductionOn with | _ P =>
      induction b using Quotient.inductionOn with | _ Q =>
        exact ha P Q

def descend : Completion R →+ G :=
  (AddLocalization.addMonoidOf (⊤ : AddSubmonoid (IsoClass R))).lift
    (g := classMap R f hi hz ha) (fun _ => AddGroup.isAddUnit _)

theorem descend_class (P : Object R) :
    descend R f hi hz ha (completionClass R P)=f P := by
  exact AddSubmonoid.LocalizationMap.lift_eq _ _ (classOf R P)

theorem descend_unique (g : Completion R →+ G)
    (hg : ∀ P : Object R, g (completionClass R P)=f P) : descend R f hi hz ha=g := by
  apply AddSubmonoid.LocalizationMap.lift_unique
  intro a
  induction a using Quotient.inductionOn with | _ P => exact hg P

def splitExact (P Q S : Object R) (i : P →ₗ[R] Q) (p : Q →ₗ[R] S)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : LinearMap.range i=LinearMap.ker p) : Q ≃ₗ[R] (P × S) := by
  let h := p.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hp)
  let s := h.choose
  have hs := h.choose_spec
  let e : P ≃ₗ[R] LinearMap.ker p :=
    (LinearEquiv.ofInjective i hi).trans (LinearEquiv.ofEq _ _ hex)
  exact ((ProjectiveStabilization.splitKernel p s hs).trans
    ((LinearEquiv.refl R S).prodCongr e.symm)).trans (LinearEquiv.prodComm R S P)

theorem completionClass_exact (P Q S : Object R) (i : P →ₗ[R] Q) (p : Q →ₗ[R] S)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : LinearMap.range i=LinearMap.ker p) :
    completionClass R Q=completionClass R P+completionClass R S := by
  rw [←completionClass_add]
  apply congrArg (inclusion R)
  exact (classOf_eq_iff R Q (of R (P × S))).mpr ⟨splitExact R P Q S i p hi hp hex⟩

#print axioms inclusion
#print axioms inclusion_class
#print axioms completionClass_add
#print axioms classMap
#print axioms descend
#print axioms descend_class
#print axioms descend_unique
#print axioms splitExact
#print axioms completionClass_exact
end Verification.ProjectiveGrothendieck
