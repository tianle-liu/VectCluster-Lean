/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RostRowTruncation
import Verification.AdditiveTerminalHomology

/-!
# Rost Weight Zero

In weight zero the actual support row has no outgoing map from
degree zero. Its degree-zero homology is the degree-zero cycle group of
the empty-coordinate stratum. The only new ordinary Milnor convention
is H^0 of K^M_0 on an integral affine scheme = Z.
-/
noncomputable section
namespace Verification.RostWeightZero
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable (T : RostAffineInput.Theory)

structure IntegralConvention where
  zero : ∀ (A : Type) [CommRing A] [IsDomain A],
    (T.cycles (Spec (CommRingCat.of A)) 0).homology 0 ≅ AddCommGrp.of ℤ

def homologyZeroIso (K : CochainComplex AddCommGrp ℕ) (hd : K.d 0 1=0) :
    K.homology 0 ≅ K.X 0 :=
  K.homologyIsoSc' 0 0 1 (by simp) (by simp) ≪≫
    (ShortComplex.HomologyData.ofZeros (K.sc' 0 0 1) (K.shape 0 0 (by decide)) hd).left.homologyIso

variable (A V : Type) [CommRing A] [Fintype V] [DecidableEq V]
variable (x : V→A) (Allowed : Finset V→Prop) (he : Allowed ∅)

def emptyIndex : PrimeLayerCover.Index Allowed 0 := ⟨∅,Finset.card_empty,he⟩

omit [Fintype V] [DecidableEq V] in
theorem index_zero (I : PrimeLayerCover.Index Allowed 0) : I=emptyIndex V Allowed he :=
  Subtype.ext (Finset.card_eq_zero.mp I.property.1)

def emptyLayerIso : RostSupportInput.Layer T A V x Allowed 0 0 0 ≅
    (T.cycles (Spec (CommRingCat.of (PrimeStratumPresentation.ClosedRing x ∅))) 0).homology 0 := by
  let i := emptyIndex V Allowed he
  letI : Unique (PrimeLayerCover.Index Allowed 0) := ⟨⟨i⟩,index_zero V Allowed he⟩
  exact (AddEquiv.piUnique (fun I : PrimeLayerCover.Index Allowed 0 =>
    (T.cycles (Spec (CommRingCat.of (PrimeStratumPresentation.ClosedRing x I.val)))
      (0-(0:ℕ))).homology 0)).toAddCommGrpIso

def rowZeroIso (N : RostMilnorInput.NegativeWeights T)
    (D : RostSupportInput.Data T A V x Allowed 0) :
    D.row.homology 0 ≅
      (T.cycles (Spec (CommRingCat.of (PrimeStratumPresentation.ClosedRing x ∅))) 0).homology 0 :=
  homologyZeroIso D.row (RostRowTruncation.outgoing_zero T N A V x Allowed 0 D) ≪≫
    D.rowTerm 0 ≪≫ emptyLayerIso T A V x Allowed he

#print axioms IntegralConvention
#print axioms homologyZeroIso
#print axioms emptyIndex
#print axioms index_zero
#print axioms emptyLayerIso
#print axioms rowZeroIso
end Verification.RostWeightZero
