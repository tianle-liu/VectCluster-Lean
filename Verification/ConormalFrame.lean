/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.Algebra.TrivSqZeroExt
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Conormal Frame

A frame for the actual conormal module I/I² from independent first-order
directions. The hypothesis is a ring map to a square-zero extension, not a
presupposed basis or conormal equivalence.
-/

noncomputable section
universe u
namespace Verification.ConormalFrame
variable {A ι : Type u} [CommRing A]
variable (x : ι → A)

def ideal : Ideal A := Ideal.span (Set.range x)
abbrev Quotient := A ⧸ ideal x
abbrev Directions := ι →₀ Quotient x

def frame (i : ι) : (ideal x).Cotangent :=
  (ideal x).toCotangent ⟨x i, Ideal.subset_span (Set.mem_range_self i)⟩

theorem span_frame : Submodule.span (Quotient x) (Set.range (frame x)) = ⊤ := by
  apply top_unique
  intro z hz
  clear hz
  obtain ⟨⟨a, ha⟩, rfl⟩ := (ideal x).toCotangent_surjective z
  induction ha using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨i, rfl⟩ := ha
      exact Submodule.subset_span (Set.mem_range_self i)
  | zero => exact Submodule.zero_mem _
  | add a b ha hb ia ib =>
      exact Submodule.add_mem _ ia ib
  | smul r a ha ia =>
      exact Submodule.smul_mem _ (Ideal.Quotient.mk (ideal x) r) ia

variable (f : A →+* TrivSqZeroExt (Quotient x) (Directions x))
variable (hf : ∀ a, (f a).fst = Ideal.Quotient.mk (ideal x) a)

def onIdeal : ideal x →ₗ[A] Directions x where
  toFun a := (f a).snd
  map_add' a b := by simp only [Submodule.coe_add, map_add, TrivSqZeroExt.snd_add]
  map_smul' r a := by
    have ha : (f a).fst = 0 := (hf a).trans (Ideal.Quotient.eq_zero_iff_mem.mpr a.2)
    change (f (r * a)).snd = r • (f a).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, hf r, ha]
    simp only [MulOpposite.op_zero, zero_smul, add_zero]
    rfl

def cotangentMapAux : (ideal x).Cotangent →ₗ[A] Directions x :=
  (ideal x • ⊤ : Submodule A (ideal x)).liftQ (onIdeal x f hf) (by
    apply Submodule.smul_le.mpr
    intro r hr a _
    rw [LinearMap.mem_ker, map_smul]
    change (Ideal.Quotient.mk (ideal x) r) • (onIdeal x f hf a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_smul])

def cotangentMap : (ideal x).Cotangent →ₗ[Quotient x] Directions x where
  toFun := cotangentMapAux x f hf
  map_add' := map_add _
  map_smul' r z := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact (cotangentMapAux x f hf).map_smul a z

theorem cotangentMap_frame (i : ι) :
    cotangentMap x f hf (frame x i) = (f (x i)).snd := rfl

variable (hx : ∀ i, f (x i) = TrivSqZeroExt.inr (Finsupp.single i 1))

include hf hx in
theorem frame_independent : LinearIndependent (Quotient x) (frame x) := by
  have h : (fun i => cotangentMap x f hf (frame x i)) =
      (fun i => Finsupp.single i (1 : Quotient x)) := by
    funext i
    rw [cotangentMap_frame, hx i, TrivSqZeroExt.snd_inr]
  apply LinearIndependent.of_comp (cotangentMap x f hf)
  change LinearIndependent (Quotient x) (fun i => cotangentMap x f hf (frame x i))
  rw [h]
  exact Finsupp.linearIndependent_single_one (Quotient x) ι

def basis : Basis ι (Quotient x) (ideal x).Cotangent :=
  Basis.mk (frame_independent x f hf hx) (by rw [span_frame])

theorem basis_apply (i : ι) : basis x f hf hx i = frame x i := Basis.mk_apply _ _ i

#print axioms ideal
#print axioms Quotient
#print axioms Directions
#print axioms frame
#print axioms span_frame
#print axioms onIdeal
#print axioms cotangentMapAux
#print axioms cotangentMap
#print axioms cotangentMap_frame
#print axioms frame_independent
#print axioms basis
#print axioms basis_apply
end Verification.ConormalFrame
