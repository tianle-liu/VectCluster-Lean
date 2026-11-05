/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ProjectiveStabilization
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Projective Classes

Isomorphism classes of actual finite projective modules, with direct
sum as addition. Equality in their group completion supplies the finite
projective stabilizer used in the manuscript's stable-freeness argument.
-/
noncomputable section
universe u
namespace Verification.ProjectiveClasses
variable (R : Type u) [CommRing R]

structure Object where
  module : ModuleCat.{u} R
  finite : Module.Finite R module
  projective : Module.Projective R module

instance : CoeSort (Object R) (Type u) := ⟨fun P => P.module⟩
instance (P : Object R) : AddCommGroup P := inferInstanceAs (AddCommGroup P.module)
instance (P : Object R) : Module R P := inferInstanceAs (Module R P.module)
instance (P : Object R) : Module.Finite R P := P.finite
instance (P : Object R) : Module.Projective R P := P.projective

def of (P : Type u) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P] : Object R :=
  ⟨ModuleCat.of R P, inferInstance, inferInstance⟩

def objectSetoid : Setoid (Object R) where
  r P Q := Nonempty (P ≃ₗ[R] Q)
  iseqv := ⟨fun P => ⟨LinearEquiv.refl R P⟩,
    fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

def IsoClass := Quotient (objectSetoid R)
def classOf (P : Object R) : IsoClass R := Quotient.mk _ P

def zeroProduct (P : Object R) : (((Fin 0 → R) × P) ≃ₗ[R] P) where
  toFun := Prod.snd
  invFun p := (0,p)
  left_inv x := by apply Prod.ext; exact Subsingleton.elim _ _; rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance classZero : Zero (IsoClass R) := ⟨classOf R (of R (Fin 0 → R))⟩
instance classAdd : Add (IsoClass R) := ⟨Quotient.map₂ (fun P Q => of R (P × Q))
    (by intro P P' h Q Q' h'; exact ⟨h.some.prodCongr h'.some⟩)⟩

instance classAddCommMonoid : AddCommMonoid (IsoClass R) where
  add_assoc := by
    intro a b c
    induction a using Quotient.inductionOn with | _ P =>
      induction b using Quotient.inductionOn with | _ Q =>
        induction c using Quotient.inductionOn with | _ S =>
          exact Quotient.sound ⟨LinearEquiv.prodAssoc R P Q S⟩
  zero_add := by
    intro a
    induction a using Quotient.inductionOn with | _ P =>
      exact Quotient.sound ⟨zeroProduct R P⟩
  add_zero := by
    intro a
    induction a using Quotient.inductionOn with | _ P =>
      exact Quotient.sound ⟨(LinearEquiv.prodComm R P (Fin 0 → R)).trans (zeroProduct R P)⟩
  add_comm := by
    intro a b
    induction a using Quotient.inductionOn with | _ P =>
      induction b using Quotient.inductionOn with | _ Q =>
        exact Quotient.sound ⟨LinearEquiv.prodComm R P Q⟩
  nsmul := nsmulRec

theorem classOf_eq_iff (P Q : Object R) :
    classOf R P = classOf R Q ↔ Nonempty (P ≃ₗ[R] Q) := Quotient.eq

theorem classOf_add (P Q : Object R) :
    classOf R (of R (P × Q)) = classOf R P + classOf R Q := rfl

abbrev Completion := AddLocalization (⊤ : AddSubmonoid (IsoClass R))

theorem completion_exists_neg (a : Completion R) : ∃ b : Completion R, b+a=0 := by
  induction a using AddLocalization.induction_on with | _ a =>
    refine ⟨AddLocalization.mk a.2.val ⟨a.1, trivial⟩, ?_⟩
    rw [AddLocalization.mk_add]
    change AddLocalization.mk (a.2.val+a.1)
      (⟨a.1+a.2.val, trivial⟩ : (⊤ : AddSubmonoid (IsoClass R)))=0
    rw [add_comm a.2.val a.1]
    exact AddLocalization.mk_self
      (⟨a.1+a.2.val, trivial⟩ : (⊤ : AddSubmonoid (IsoClass R)))

instance completionNeg : Neg (Completion R) := ⟨fun a => (completion_exists_neg R a).choose⟩

instance completionAddCommGroup : AddCommGroup (Completion R) where
  neg_add_cancel a := (completion_exists_neg R a).choose_spec
  zsmul := zsmulRec

def completionClass (P : Object R) : Completion R := AddLocalization.mk (classOf R P) 0

theorem completionClass_eq_iff (P Q : Object R) :
    completionClass R P = completionClass R Q ↔
      ∃ S : Object R, Nonempty ((P × S) ≃ₗ[R] (Q × S)) := by
  rw [completionClass, completionClass, AddLocalization.mk_eq_mk_iff,
    AddLocalization.r_iff_exists]
  constructor
  · rintro ⟨c,hc⟩
    rcases c with ⟨c,hc'⟩
    induction c using Quotient.inductionOn with | _ S =>
      refine ⟨S,?_⟩
      apply (classOf_eq_iff R (of R (P × S)) (of R (Q × S))).mp
      change classOf R P + classOf R S = classOf R Q + classOf R S
      simpa only [ZeroMemClass.coe_zero, zero_add, add_comm] using hc
  · rintro ⟨S,⟨e⟩⟩
    refine ⟨⟨classOf R S, trivial⟩,?_⟩
    have h := (classOf_eq_iff R (of R (P × S)) (of R (Q × S))).mpr ⟨e⟩
    simpa only [classOf_add,ZeroMemClass.coe_zero,zero_add,add_comm] using h

theorem stable_free_of_completionClass (P : Object R) (r : ℕ)
    (h : completionClass R P = completionClass R (of R (Fin r → R))) :
    ∃ n : ℕ, Nonempty ((P × (Fin n → R)) ≃ₗ[R]
      ((Fin r → R) × (Fin n → R))) := by
  obtain ⟨S,⟨e⟩⟩ := (completionClass_eq_iff R P _).mp h
  exact ProjectiveStabilization.stable_free_of_projective_stabilizer e

theorem completionClass_eq_iff_stable_free (P : Object R) (r : ℕ) :
    completionClass R P = completionClass R (of R (Fin r → R)) ↔
      ∃ n : ℕ, Nonempty ((P × (Fin n → R)) ≃ₗ[R]
        ((Fin r → R) × (Fin n → R))) := by
  constructor
  · exact stable_free_of_completionClass R P r
  · rintro ⟨n, h⟩
    exact (completionClass_eq_iff R P _).mpr ⟨of R (Fin n → R),h⟩

#print axioms of
#print axioms objectSetoid
#print axioms IsoClass
#print axioms classOf
#print axioms zeroProduct
#print axioms classZero
#print axioms classAdd
#print axioms classAddCommMonoid
#print axioms classOf_eq_iff
#print axioms classOf_add
#print axioms Completion
#print axioms completion_exists_neg
#print axioms completionNeg
#print axioms completionAddCommGroup
#print axioms completionClass
#print axioms completionClass_eq_iff
#print axioms stable_free_of_completionClass
#print axioms completionClass_eq_iff_stable_free
end Verification.ProjectiveClasses

-- Explicit dependency audit of the early module constructions.
#print axioms Verification.ProjectiveClasses.Object
