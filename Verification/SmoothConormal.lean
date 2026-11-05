/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ConormalFrame
import Mathlib.RingTheory.Smooth.Basic

/-!
# Smooth Conormal

The original-coordinate conormal frame is derived from formal smoothness
over the parameter polynomial ring by a square-zero lifting argument.
-/
noncomputable section
universe u
namespace Verification.SmoothConormal
open MvPolynomial Verification.ConormalFrame
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
variable [Algebra (MvPolynomial ι R) A] [IsScalarTower R (MvPolynomial ι R) A]

def coordinate (i : ι) : A := algebraMap (MvPolynomial ι R) A (X i)

theorem exists_directions_for [Algebra.FormallySmooth (MvPolynomial ι R) A]
    (x : ι → A) (hx : ∀ i, algebraMap (MvPolynomial ι R) A (X i) = x i) :
    ∃ f : A →+* TrivSqZeroExt (ConormalFrame.Quotient x) (Directions x),
      (∀ a, (f a).fst = Ideal.Quotient.mk (ideal x) a) ∧
      ∀ i, f (x i) = TrivSqZeroExt.inr (Finsupp.single i 1) := by
  let Q := ConormalFrame.Quotient x
  let E := TrivSqZeroExt Q (Directions x)
  let t : MvPolynomial ι R →ₐ[R] E := aeval (fun i => TrivSqZeroExt.inr (Finsupp.single i 1))
  letI : Algebra (MvPolynomial ι R) E := t.toRingHom.toAlgebra
  have hcomm : (TrivSqZeroExt.fstHom R Q (Directions x)).comp t =
      IsScalarTower.toAlgHom R (MvPolynomial ι R) Q := by
    apply MvPolynomial.algHom_ext
    intro i
    change (t (X i)).fst = algebraMap (MvPolynomial ι R) Q (X i)
    rw [show t (X i) = TrivSqZeroExt.inr (Finsupp.single i 1) from aeval_X _ _]
    change 0 = algebraMap (MvPolynomial ι R) Q (X i)
    symm
    rw [IsScalarTower.algebraMap_apply (MvPolynomial ι R) A Q]
    rw [hx i]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
  let π : E →ₐ[MvPolynomial ι R] Q :=
    { (TrivSqZeroExt.fstHom R Q (Directions x)).toRingHom with
      commutes' := fun p => AlgHom.congr_fun hcomm p }
  have hsurj : Function.Surjective π := TrivSqZeroExt.fst_surjective
  have hnil : IsNilpotent (RingHom.ker π.toRingHom) := by
    refine ⟨2, ?_⟩
    change RingHom.ker π.toRingHom ^ (2 : ℕ) = ⊥
    rw [_root_.pow_two (RingHom.ker π.toRingHom), eq_bot_iff]
    apply Ideal.mul_le.mpr
    intro a ha b hb
    change a * b = 0
    change a.fst = 0 at ha
    change b.fst = 0 at hb
    apply TrivSqZeroExt.ext
    · change a.fst * b.fst = 0
      rw [ha, zero_mul]
    · change a.fst • b.snd + MulOpposite.op b.fst • a.snd = 0
      rw [ha, hb, MulOpposite.op_zero, zero_smul, zero_smul, add_zero]
  let f := Algebra.FormallySmooth.liftOfSurjective
    (Ideal.Quotient.mkₐ (MvPolynomial ι R) (ideal x)) π hsurj hnil
  refine ⟨f.toRingHom, ?_, ?_⟩
  · intro a
    exact Algebra.FormallySmooth.liftOfSurjective_apply
      (Ideal.Quotient.mkₐ (MvPolynomial ι R) (ideal x)) π hsurj hnil a
  · intro i
    change f (x i) = _
    rw [← hx i]
    rw [AlgHom.commutes]
    exact aeval_X _ _

theorem exists_directions [Algebra.FormallySmooth (MvPolynomial ι R) A] :
    ∃ f : A →+* TrivSqZeroExt (ConormalFrame.Quotient (coordinate R A ι))
        (Directions (coordinate R A ι)),
      (∀ a, (f a).fst = Ideal.Quotient.mk (ideal (coordinate R A ι)) a) ∧
      ∀ i, f (coordinate R A ι i) = TrivSqZeroExt.inr (Finsupp.single i 1) :=
  exists_directions_for R A ι (coordinate R A ι) (fun _ => rfl)

def basis [Algebra.FormallySmooth (MvPolynomial ι R) A] :
    Basis ι (ConormalFrame.Quotient (coordinate R A ι)) (ideal (coordinate R A ι)).Cotangent :=
  ConormalFrame.basis (coordinate R A ι) (exists_directions R A ι).choose
    (exists_directions R A ι).choose_spec.1 (exists_directions R A ι).choose_spec.2

theorem basis_apply [Algebra.FormallySmooth (MvPolynomial ι R) A] (i : ι) :
    basis R A ι i = frame (coordinate R A ι) i := ConormalFrame.basis_apply _ _ _ _ i

#print axioms coordinate
#print axioms exists_directions_for
#print axioms exists_directions
#print axioms basis
#print axioms basis_apply
end Verification.SmoothConormal
