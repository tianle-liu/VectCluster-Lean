/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.KoszulCone
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Koszul Recursive

A Koszul complex built by actual signed cones. Prepending an element
adjoins its cone to the previous complex; regularity is therefore read in
the reversed list order. The augmentation has the actual equation ideal
as its kernel, and positive exactness follows by induction from regularity.
-/
noncomputable section
universe u
namespace Verification.KoszulRecursive
open CategoryTheory Verification.KoszulCone RingTheory.Sequence
variable (R : Type u) [CommRing R]

def positiveTerm : List R → ℕ → ModuleCat.{u} R
  | [],_ => ModuleCat.of R (Fin 0 → R)
  | _::l,p =>
      let T : ModuleCat.{u} R := match p with
        | 0 => ModuleCat.of R R
        | q+1 => positiveTerm l q
      ModuleCat.of R (positiveTerm l p × T)

abbrev term (l : List R) : ℕ → ModuleCat.{u} R
  | 0 => ModuleCat.of R R
  | p+1 => positiveTerm R l p

def differential : (l : List R) → (p : ℕ) → term R l (p+1) →ₗ[R] term R l p
  | [],_ => 0
  | x::l,0 => first (differential l 0) x
  | x::l,p+1 => block (differential l (p+1)) (differential l p) x

theorem differential_squared (l : List R) (p : ℕ) :
    (differential R l p).comp (differential R l (p+1))=0 := by
  induction l generalizing p with
  | nil => simp [differential]
  | cons x l ih =>
    cases p with
    | zero => exact first_squared _ _ x (ih 0)
    | succ p => exact block_squared _ _ _ x (ih (p+1)) (ih p)

def complex (l : List R) : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of (term R l) (fun p => ModuleCat.ofHom (differential R l p))
    (fun p => by apply ModuleCat.hom_ext; exact differential_squared R l p)

theorem term_free (l : List R) (p : ℕ) : Module.Free R (term R l p) := by
  induction l generalizing p with
  | nil => cases p <;> dsimp [term,positiveTerm] <;> infer_instance
  | cons x l ih =>
    cases p with
    | zero => exact inferInstanceAs (Module.Free R R)
    | succ p =>
      letI := ih (p+1)
      letI := ih p
      exact inferInstanceAs (Module.Free R (term R l (p+1) × term R l p))

theorem term_finite (l : List R) (p : ℕ) : Module.Finite R (term R l p) := by
  induction l generalizing p with
  | nil => cases p <;> dsimp [term,positiveTerm] <;> infer_instance
  | cons x l ih =>
    cases p with
    | zero => exact inferInstanceAs (Module.Finite R R)
    | succ p =>
      letI := ih (p+1)
      letI := ih p
      exact inferInstanceAs (Module.Finite R (term R l (p+1) × term R l p))

theorem first_image (l : List R) :
    LinearMap.range (differential R l 0)=Ideal.ofList l := by
  induction l with
  | nil => simp [differential]
  | cons x l ih =>
    apply le_antisymm
    · rintro _ ⟨⟨a,b⟩,rfl⟩
      change (differential R l 0 a : R)+x*b ∈ Ideal.ofList (x::l)
      rw [Ideal.ofList_cons]
      apply Submodule.add_mem
      · apply (show Ideal.ofList l ≤ Ideal.span {x} ⊔ Ideal.ofList l from le_sup_right)
        rw [←ih]
        exact LinearMap.mem_range_self _ a
      · apply (show Ideal.span {x} ≤ Ideal.span {x} ⊔ Ideal.ofList l from le_sup_left)
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton x))
    · apply Ideal.span_le.mpr
      rintro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · refine ⟨(0,1),?_⟩
        change (differential R l 0 0 : R)+y*1=y
        simp
      · have hm : y ∈ LinearMap.range (differential R l 0) := by
          rw [ih]
          exact Ideal.subset_span hy
        obtain ⟨a,ha⟩ := hm
        refine ⟨(a,0),?_⟩
        change (differential R l 0 a : R)+x*0=y
        simpa using ha

def augmentation (l : List R) : term R l 0 →ₗ[R] (R ⧸ Ideal.ofList l) :=
  (Ideal.ofList l).mkQ

theorem augmentation_exact (l : List R) :
    LinearMap.range (differential R l 0)=LinearMap.ker (augmentation R l) := by
  rw [first_image]
  exact (Submodule.ker_mkQ _).symm

theorem augmentation_surjective (l : List R) : Function.Surjective (augmentation R l) :=
  Submodule.mkQ_surjective _

theorem positive_exact (l : List R) (hl : IsWeaklyRegular R l.reverse) (p : ℕ) :
    LinearMap.range (differential R l (p+1))=LinearMap.ker (differential R l p) := by
  induction l generalizing p with
  | nil =>
    apply le_antisymm
    · rw [differential,LinearMap.range_zero]
      exact bot_le
    · intro z _
      refine ⟨0,?_⟩
      exact @Subsingleton.elim (Fin 0 → R) inferInstance _ _
  | cons x l ih =>
    have hsplit := (isWeaklyRegular_append_iff R l.reverse [x]).mp
      (by simpa only [List.reverse_cons] using hl)
    have hx : IsSMulRegular (R ⧸ Ideal.ofList l) x := by
      have hh := (isWeaklyRegular_singleton_iff _ x).mp hsplit.2
      have hI : Ideal.ofList l.reverse=Ideal.ofList l := by
        apply congrArg Ideal.span
        ext a
        exact List.mem_reverse
      have hJ : (Ideal.ofList l.reverse • (⊤ : Submodule R R)) = Ideal.ofList l := by
        change Ideal.ofList l.reverse * (⊤ : Ideal R) = _
        rw [Ideal.mul_top,hI]
      rw [hJ] at hh
      exact hh
    cases p with
    | zero =>
      exact first_exact _ _ (augmentation R l) x
        (ih hsplit.1 0) (augmentation_exact R l) hx
    | succ p => exact block_exact _ _ _ x (ih hsplit.1 (p+1)) (ih hsplit.1 p)

#print axioms positiveTerm
#print axioms term
#print axioms differential
#print axioms differential_squared
#print axioms complex
#print axioms term_free
#print axioms term_finite
#print axioms first_image
#print axioms augmentation
#print axioms augmentation_exact
#print axioms augmentation_surjective
#print axioms positive_exact
end Verification.KoszulRecursive
