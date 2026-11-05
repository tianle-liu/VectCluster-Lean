/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SmoothConormal

/-!
# Smooth Partial Conormal

Formal smoothness over all original parameters supplies the actual
conormal basis for any chosen subset. Unkilled parameters retain their
quotient values in the explicit square-zero lift.
-/
noncomputable section
namespace Verification.SmoothPartialConormal
open MvPolynomial Verification.ConormalFrame
variable (R A ι : Type) [CommRing R] [CommRing A] [Algebra R A]
variable [Algebra (MvPolynomial ι R) A] [IsScalarTower R (MvPolynomial ι R) A]
variable (s : Set ι) (x : ι → A) (hx : ∀ i,algebraMap (MvPolynomial ι R) A (X i) = x i)

include hx in
theorem exists_directions [Algebra.FormallySmooth (MvPolynomial ι R) A] :
    ∃ f : A →+* TrivSqZeroExt (ConormalFrame.Quotient (fun i : s => x i.val))
        (Directions (fun i : s => x i.val)),
      (∀ a,(f a).fst = Ideal.Quotient.mk (ideal (fun i : s => x i.val)) a) ∧
      ∀ i : s,f (x i.val) = TrivSqZeroExt.inr (Finsupp.single i 1) := by
  classical
  let y := fun i : s => x i.val
  let Q := ConormalFrame.Quotient y
  let E := TrivSqZeroExt Q (Directions y)
  let t : MvPolynomial ι R →ₐ[R] E := aeval (fun i =>
    if h : i ∈ s then TrivSqZeroExt.inr (Finsupp.single ⟨i,h⟩ 1)
    else TrivSqZeroExt.inl (Ideal.Quotient.mk (ideal y) (x i)))
  letI : Algebra (MvPolynomial ι R) E := t.toRingHom.toAlgebra
  have hcomm : (TrivSqZeroExt.fstHom R Q (Directions y)).comp t =
      IsScalarTower.toAlgHom R (MvPolynomial ι R) Q := by
    apply MvPolynomial.algHom_ext
    intro i
    change (t (X i)).fst = algebraMap (MvPolynomial ι R) Q (X i)
    rw [IsScalarTower.algebraMap_apply (MvPolynomial ι R) A Q,hx i]
    change (t (X i)).fst = Ideal.Quotient.mk (ideal y) (x i)
    dsimp only [t]
    rw [aeval_X]
    by_cases hi : i ∈ s
    · rw [dif_pos hi,TrivSqZeroExt.fst_inr]
      symm
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨⟨i,hi⟩,rfl⟩)
    · rw [dif_neg hi,TrivSqZeroExt.fst_inl]
  let π : E →ₐ[MvPolynomial ι R] Q :=
    { (TrivSqZeroExt.fstHom R Q (Directions y)).toRingHom with
      commutes' := fun p => AlgHom.congr_fun hcomm p }
  have hsurj : Function.Surjective π := TrivSqZeroExt.fst_surjective
  have hnil : IsNilpotent (RingHom.ker π.toRingHom) := by
    refine ⟨2, ?_⟩
    change RingHom.ker π.toRingHom ^ (2 : ℕ) = ⊥
    rw [_root_.pow_two (RingHom.ker π.toRingHom),eq_bot_iff]
    apply Ideal.mul_le.mpr
    intro a ha b hb
    change a * b = 0
    change a.fst = 0 at ha
    change b.fst = 0 at hb
    apply TrivSqZeroExt.ext
    · change a.fst * b.fst = 0
      rw [ha,zero_mul]
    · change a.fst • b.snd + MulOpposite.op b.fst • a.snd = 0
      rw [ha,hb,MulOpposite.op_zero,zero_smul,zero_smul,add_zero]
  let f := Algebra.FormallySmooth.liftOfSurjective
    (Ideal.Quotient.mkₐ (MvPolynomial ι R) (ideal y)) π hsurj hnil
  refine ⟨f.toRingHom,?_,?_⟩
  · intro a
    exact Algebra.FormallySmooth.liftOfSurjective_apply
      (Ideal.Quotient.mkₐ (MvPolynomial ι R) (ideal y)) π hsurj hnil a
  · intro i
    change f (x i.val) = _
    rw [← hx i.val,AlgHom.commutes]
    change t (X i.val) = _
    simp only [t,aeval_X,dif_pos i.property]

def basis [Algebra.FormallySmooth (MvPolynomial ι R) A] :
    Basis s (ConormalFrame.Quotient (fun i : s => x i.val)) (ideal (fun i : s => x i.val)).Cotangent :=
  ConormalFrame.basis (fun i : s => x i.val) (exists_directions R A ι s x hx).choose
    (exists_directions R A ι s x hx).choose_spec.1
    (exists_directions R A ι s x hx).choose_spec.2

theorem basis_apply [Algebra.FormallySmooth (MvPolynomial ι R) A] (i : s) :
    basis R A ι s x hx i = frame (fun i : s => x i.val) i := ConormalFrame.basis_apply _ _ _ _ i

#print axioms exists_directions
#print axioms basis
#print axioms basis_apply
end Verification.SmoothPartialConormal
