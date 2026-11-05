/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Nonpositive Complex Comparison

Adjacent comparisons in nonpositive degrees suffice for an isomorphism
of the whole integer-indexed cochain complexes, including the zero extension.
-/
noncomputable section
namespace Verification.NonpositiveComplexComparison
open CategoryTheory CategoryTheory.Limits CochainComplex
variable {C : Type*} [Category C] [HasZeroMorphisms C]
variable (P Q : CochainComplex C ℤ) [P.IsStrictlyLE 0] [Q.IsStrictlyLE 0]
variable (e : ∀ p : ℕ,P.X (-(p:ℤ)) ≅ Q.X (-(p:ℤ)))

def termIso (i : ℤ) : P.X i ≅ Q.X i := by
  by_cases hi : i≤0
  · have he : i= -((-i).toNat:ℤ) := by omega
    exact eqToIso (congrArg P.X he) ≪≫ e (-i).toNat ≪≫ eqToIso (congrArg Q.X he.symm)
  · exact (P.isZero_of_isStrictlyLE 0 i (by omega)).iso
      (Q.isZero_of_isStrictlyLE 0 i (by omega))

omit [P.IsStrictlyLE 0] [Q.IsStrictlyLE 0] in
theorem transport (n p : ℕ) (h : n=p) :
    eqToIso (congrArg (fun q:ℕ=>P.X (-(q:ℤ))) h.symm) ≪≫ e n ≪≫
      eqToIso (congrArg (fun q:ℕ=>Q.X (-(q:ℤ))) h)=e p := by
  subst n
  simp

theorem termIso_nat (p : ℕ) : termIso P Q e (-(p:ℤ))=e p := by
  unfold termIso
  rw [dif_pos (show -(p:ℤ)≤0 by omega)]
  exact transport P Q e _ p (by omega)

def iso (h : ∀ p : ℕ,P.d (-((p+1:ℕ):ℤ)) (-(p:ℤ)) ≫ (e p).hom =
    (e (p+1)).hom ≫ Q.d (-((p+1:ℕ):ℤ)) (-(p:ℤ))) : P ≅ Q :=
  HomologicalComplex.Hom.isoOfComponents (termIso P Q e) (by
    intro i j hij
    by_cases hj : j≤0
    · obtain ⟨p,hp⟩ := Int.eq_ofNat_of_zero_le (show 0≤ -j by omega)
      have je : j= -(p:ℤ) := by omega
      have ie : i= -((p+1:ℕ):ℤ) := by change i+1=j at hij;omega
      subst i j
      rw [termIso_nat,termIso_nat]
      exact (h p).symm
    · exact (Q.isZero_of_isStrictlyLE 0 j (by omega)).eq_of_tgt _ _)

#print axioms termIso
#print axioms transport
#print axioms termIso_nat
#print axioms iso
end Verification.NonpositiveComplexComparison
