/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ProjectiveGrothendieck
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Module Grothendieck

The Grothendieck group of actual finite modules, presented by actual
short exact sequences. On a Noetherian ring this is the usual module G₀.
The definitions are independent of the subsequent Koszul computation.
-/
noncomputable section
universe u
namespace Verification.ModuleGrothendieck
variable (R : Type u) [CommRing R]

structure Object where
  module : ModuleCat.{u} R
  finite : Module.Finite R module

instance : CoeSort (Object R) (Type u) := ⟨fun P => P.module⟩
instance (P : Object R) : AddCommGroup P := inferInstanceAs (AddCommGroup P.module)
instance (P : Object R) : Module R P := inferInstanceAs (Module R P.module)
instance (P : Object R) : Module.Finite R P := P.finite

def of (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] : Object R :=
  ⟨ModuleCat.of R M,inferInstance⟩

def relations : Set (FreeAbelianGroup (Object R)) :=
  {z | ∃ P Q S : Object R, ∃ i : P →ₗ[R] Q, ∃ p : Q →ₗ[R] S,
    Function.Injective i ∧ Function.Surjective p ∧ LinearMap.range i=LinearMap.ker p ∧
    z=FreeAbelianGroup.of Q-FreeAbelianGroup.of P-FreeAbelianGroup.of S}

def relationSubgroup : AddSubgroup (FreeAbelianGroup (Object R)) := AddSubgroup.closure (relations R)
abbrev Group := FreeAbelianGroup (Object R) ⧸ relationSubgroup R

def classOf (P : Object R) : Group R :=
  (QuotientAddGroup.mk' (relationSubgroup R)) (FreeAbelianGroup.of P)

theorem exact_class (P Q S : Object R) (i : P →ₗ[R] Q) (p : Q →ₗ[R] S)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (he : LinearMap.range i=LinearMap.ker p) : classOf R Q=classOf R P+classOf R S := by
  have hz : (QuotientAddGroup.mk' (relationSubgroup R))
      (FreeAbelianGroup.of Q-FreeAbelianGroup.of P-FreeAbelianGroup.of S)=0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr
      (AddSubgroup.subset_closure ⟨P,Q,S,i,p,hi,hp,he,rfl⟩)
  change classOf R Q-classOf R P-classOf R S=0 at hz
  exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp hz)).trans (add_comm _ _)

theorem zero_class : classOf R (of R (Fin 0 → R))=0 := by
  let Z := of R (Fin 0 → R)
  letI : Subsingleton Z := inferInstanceAs (Subsingleton (Fin 0 → R))
  have h := exact_class R Z Z Z (0 : Z →ₗ[R] Z) (0 : Z →ₗ[R] Z)
    (fun a b _ => Subsingleton.elim _ _) (fun a => ⟨0,Subsingleton.elim _ _⟩)
    (by ext a; simp [Subsingleton.elim a 0])
  change classOf R (of R (Fin 0 → R))=classOf R (of R (Fin 0 → R))+classOf R (of R (Fin 0 → R)) at h
  exact add_left_cancel (a := classOf R (of R (Fin 0 → R))) (by simpa using h.symm)

theorem iso_class (P Q : Object R) (e : P ≃ₗ[R] Q) : classOf R P=classOf R Q := by
  letI : Subsingleton (of R (Fin 0 → R)) := inferInstanceAs (Subsingleton (Fin 0 → R))
  have h := exact_class R (of R (Fin 0 → R)) P Q 0 e.toLinearMap
    (fun a b _ => Subsingleton.elim _ _) e.surjective
    (by rw [LinearMap.range_zero,LinearMap.ker_eq_bot.mpr e.injective])
  simpa only [zero_class,zero_add] using h

theorem product_class (P Q : Object R) : classOf R (of R (P × Q))=classOf R P+classOf R Q := by
  apply exact_class R P (of R (P × Q)) Q (LinearMap.inl R P Q) (LinearMap.snd R P Q)
  · intro a b hab
    exact congrArg Prod.fst hab
  · intro q
    exact ⟨(0,q),rfl⟩
  · ext z
    constructor
    · rintro ⟨p,rfl⟩
      rfl
    · intro hz
      exact ⟨z.1,Prod.ext rfl (LinearMap.mem_ker.mp hz).symm⟩

def forget (P : Verification.ProjectiveClasses.Object R) : Object R := of R P

def cartan : Verification.ProjectiveClasses.Completion R →+ Group R :=
  Verification.ProjectiveGrothendieck.descend R (fun P => classOf R (forget R P))
    (fun P Q h => iso_class R (forget R P) (forget R Q) h.some)
    (zero_class R) (fun P Q => product_class R (forget R P) (forget R Q))

theorem cartan_class (P : Verification.ProjectiveClasses.Object R) :
    cartan R (Verification.ProjectiveClasses.completionClass R P)=classOf R (forget R P) :=
  Verification.ProjectiveGrothendieck.descend_class _ _ _ _ _ _

#print axioms of
#print axioms relations
#print axioms relationSubgroup
#print axioms Group
#print axioms classOf
#print axioms exact_class
#print axioms zero_class
#print axioms iso_class
#print axioms product_class
#print axioms forget
#print axioms cartan
#print axioms cartan_class
end Verification.ModuleGrothendieck

-- Explicit dependency audit of the early module constructions.
#print axioms Verification.ModuleGrothendieck.Object
