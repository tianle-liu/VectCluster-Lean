/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FiniteTorusSectionSplit
import Verification.BinaryWordCoordinates

/-!
# Finite Torus Word Basis

Ordered subset words provide actual additive coordinates for all total
MW sections of a finite split torus. The basis is constructed recursively
from the geometric Laurent split.
-/
noncomputable section
namespace Verification.FiniteTorusWordBasis
open CategoryTheory AlgebraicGeometry
open Verification.OriginalTorus Verification.BinaryWordCoordinates
variable (R : Type) [CommRing R]
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (D : GradedMilnorWittSheaf.Standard site N)
variable (K : StandardThomContractionNormalization.Grading R site N)
local notation "C" => D.Total (CommRingCat.of R)
local notation "T" n => D.Total (CommRingCat.of (Torus R (Fin n)))

def basis : ∀ n,(Index n → C) ≃+ T n
  | 0 => (BinaryWordCoordinates.zeroEquiv C).trans (FiniteTorusSectionSplit.zeroEquiv R site N D)
  | n+1 => (succEquiv C n).trans
      (((basis n).prodCongr (basis n)).trans (FiniteTorusSectionSplit.equiv R site N D K n).symm)

def value : ∀ n,Index n → C → T n
  | 0,_,a => FiniteTorusSectionSplit.zeroEquiv R site N D a
  | n+1,(false,i),a => FiniteTorusSectionSplit.coefficient R site N D n (value n i a)
  | n+1,(true,i),a => FiniteTorusSectionSplit.firstSymbol R site N D n*
      FiniteTorusSectionSplit.coefficient R site N D n (value n i a)

variable (P : GradedMilnorWittLaurent.Standard R site N D K)
include P

theorem basis_single (n : ℕ) (i : Index n) (a : C) :
    basis R site N D K n (Pi.single i a)=value R site N D n i a := by
  induction n with
  | zero =>
    cases i
    simp [basis,value,BinaryWordCoordinates.zeroEquiv]
  | succ n ih =>
    rcases i with ⟨b,i⟩
    cases b
    · change (FiniteTorusSectionSplit.equiv R site N D K n).symm
        (((basis R site N D K n).prodCongr (basis R site N D K n))
          (succEquiv C n (Pi.single (false,i) a)))=_
      rw [succ_false]
      change (FiniteTorusSectionSplit.equiv R site N D K n).symm
        (basis R site N D K n (Pi.single i a),basis R site N D K n 0)=_
      rw [map_zero,FiniteTorusSectionSplit.inverse_words R site N D K P,ih,map_zero,mul_zero,add_zero]
      rfl
    · change (FiniteTorusSectionSplit.equiv R site N D K n).symm
        (((basis R site N D K n).prodCongr (basis R site N D K n))
          (succEquiv C n (Pi.single (true,i) a)))=_
      rw [succ_true]
      change (FiniteTorusSectionSplit.equiv R site N D K n).symm
        (basis R site N D K n 0,basis R site N D K n (Pi.single i a))=_
      rw [map_zero,FiniteTorusSectionSplit.inverse_words R site N D K P,ih,map_zero,zero_add]
      rfl

theorem basis_expansion (n : ℕ) (a : Index n → C) :
    basis R site N D K n a=∑ i,value R site N D n i (a i) := by
  have h : a=∑ i,Pi.single i (a i) := by
    funext i
    simp
  conv_lhs => rw [h]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact basis_single R site N D K P n i (a i)

#print axioms basis
#print axioms value
#print axioms basis_single
#print axioms basis_expansion
end Verification.FiniteTorusWordBasis
