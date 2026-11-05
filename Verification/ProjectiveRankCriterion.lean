/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ProjectiveFieldRank

/-!
# Projective Rank Criterion

For the actual Grothendieck group, rank is an isomorphism exactly
when every finite projective module is stably free. The rank is the
already constructed field-fiber rank, not an assumed group map.
-/
noncomputable section
universe u
namespace Verification.ProjectiveRankCriterion
open Verification.ProjectiveClasses Verification.ProjectiveGrothendieck
open Verification.ProjectiveFieldRank
variable (R k : Type u) [CommRing R] [Field k] [Algebra R k]

def freeSucc (n : ℕ) : (Fin (n+1) → R) ≃ₗ[R] ((Fin 1 → R) × (Fin n → R)) where
  toFun x := (fun _ => x 0, fun i => x i.succ)
  invFun x := Fin.cases (x.1 0) x.2
  left_inv x := by funext i; exact Fin.cases rfl (fun _ => rfl) i
  right_inv x := by
    apply Prod.ext
    · funext i
      have : i=0 := Fin.eq_zero i
      subst i
      rfl
    · rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def unitClass : Completion R := completionClass R (of R (Fin 1 → R))

theorem free_class (n : ℕ) : completionClass R (of R (Fin n → R))=n • unitClass R := by
  induction n with
  | zero =>
    rw [zero_nsmul]
    change AddLocalization.mk (0 : IsoClass R) (0 : (⊤ : AddSubmonoid (IsoClass R)))=0
    exact AddLocalization.mk_zero
  | succ n ih =>
    have he := congrArg (inclusion R) ((classOf_eq_iff R
      (of R (Fin (n+1) → R)) (of R ((Fin 1 → R) × (Fin n → R)))).mpr ⟨freeSucc R n⟩)
    change completionClass R (of R (Fin (n+1) → R))=
      completionClass R (of R ((Fin 1 → R) × (Fin n → R))) at he
    rw [he]
    have hp : completionClass R (of R ((Fin 1 → R) × (Fin n → R)))=
        unitClass R+completionClass R (of R (Fin n → R)) :=
      completionClass_add R (of R (Fin 1 → R)) (of R (Fin n → R))
    rw [hp,ih]
    exact (succ_nsmul' (unitClass R) n).symm

theorem difference_of_classes (x : Completion R) :
    ∃ P Q : Object R, x=completionClass R P-completionClass R Q := by
  obtain ⟨⟨a,b⟩,h⟩ := (AddLocalization.addMonoidOf (⊤ : AddSubmonoid (IsoClass R))).surj' x
  obtain ⟨P,rfl⟩ := Quotient.exists_rep a
  rcases b with ⟨b,hb⟩
  obtain ⟨Q,rfl⟩ := Quotient.exists_rep b
  exact ⟨P,Q,eq_sub_iff_add_eq.mpr h⟩

def StablyFree (P : Object R) : Prop :=
  ∃ r n : ℕ, Nonempty ((P × (Fin n → R)) ≃ₗ[R] ((Fin r → R) × (Fin n → R)))

theorem class_eq_rank (P : Object R) (h : StablyFree R P) :
    completionClass R P=(rank R k P : ℤ) • unitClass R := by
  obtain ⟨r,n,h⟩ := h
  have hc := (completionClass_eq_iff_stable_free R P r).mpr ⟨n,h⟩
  have hr := congrArg (rankMap R k) hc
  rw [rankMap_class,rankMap_free] at hr
  rw [hr,hc,free_class]
  simp

theorem rankMap_bijective_of_stably_free (h : ∀ P : Object R, StablyFree R P) :
    Function.Bijective (rankMap R k) := by
  have hleft (x : Completion R) : (rankMap R k x) • unitClass R=x := by
    obtain ⟨P,Q,rfl⟩ := difference_of_classes R x
    rw [map_sub,rankMap_class,rankMap_class,sub_smul]
    rw [←class_eq_rank R k P (h P),←class_eq_rank R k Q (h Q)]
  constructor
  · intro x y hxy
    rw [←hleft x,←hleft y,hxy]
  · intro z
    refine ⟨z • unitClass R,?_⟩
    rw [map_zsmul]
    change z • rankMap R k (completionClass R (of R (Fin 1 → R)))=z
    rw [rankMap_free]
    simp

theorem stably_free_of_rankMap_injective (h : Function.Injective (rankMap R k))
    (P : Object R) : StablyFree R P := by
  have hc : completionClass R P=completionClass R (of R (Fin (rank R k P) → R)) := by
    apply h
    rw [rankMap_class,rankMap_free]
  obtain ⟨n,hn⟩ := stable_free_of_completionClass R P _ hc
  exact ⟨rank R k P,n,hn⟩

theorem rankMap_bijective_iff_stably_free :
    Function.Bijective (rankMap R k) ↔ ∀ P : Object R, StablyFree R P :=
  ⟨fun h => stably_free_of_rankMap_injective R k h.1,rankMap_bijective_of_stably_free R k⟩

#print axioms freeSucc
#print axioms unitClass
#print axioms free_class
#print axioms difference_of_classes
#print axioms StablyFree
#print axioms class_eq_rank
#print axioms rankMap_bijective_of_stably_free
#print axioms stably_free_of_rankMap_injective
#print axioms rankMap_bijective_iff_stably_free
end Verification.ProjectiveRankCriterion
