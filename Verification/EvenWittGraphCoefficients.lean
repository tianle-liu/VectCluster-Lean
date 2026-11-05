/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.EvenWittWordBasis
import Verification.EvenWittGraphRealization

/-!
# Even Witt Graph Coefficients

The actual product of quotient-ring stratum terms is the free integer
module on the graph's original (I,A_x,F) monomials.
-/
noncomputable section
open scoped Classical
namespace Verification.EvenWittGraphCoefficients
open Verification.OriginalWittIntegerDifferential Verification.OriginalWittQuotient
open Verification.GraphBlocks Verification.EvenWittPfisterResidue
open Verification.EvenWittGraphRealization
variable {V C : Type} [Fintype V] [Fintype C] [LinearOrder V]
variable (G : SimpleGraph V) (c : V → C)
variable (hc : ∀ I : Finset V, G.IsIndepSet (I : Set V) → Function.Injective (fun i : I => c i.val))

def sigmaEquiv : (Σ I : Index (Allowed G), EvenWittWordIndex.LocalIndex c I.val) ≃ MonomialIndex G c where
  toFun x := ⟨x.1.val,x.2.val.1,x.2.val.2,x.1.property,x.2.property.1,x.2.property.2⟩
  invFun x := ⟨⟨x.I,x.independent⟩,⟨(x.A,x.F),x.disjoint,x.avoids⟩⟩
  left_inv x := by rcases x with ⟨⟨I,hI⟩,⟨⟨A,F⟩,ha⟩⟩; rfl
  right_inv x := by cases x; rfl

def equiv : Coefficients G c ≃ₗ[ℤ] (MonomialIndex G c →₀ ℤ) :=
  (LinearEquiv.piCongrRight (fun I : Index (Allowed G) =>
    (EvenWittWordBasis.basis c I.val (hc I.val I.property)).repr)).trans
    ((Finsupp.sigmaFinsuppLEquivPiFinsupp ℤ).symm.trans (Finsupp.domLCongr (sigmaEquiv G c)))

theorem apply_value (f : Coefficients G c) (x : MonomialIndex G c) :
    equiv G c hc f x =
      (EvenWittWordBasis.basis c x.I (hc x.I x.independent)).repr
        (f ⟨x.I,x.independent⟩) ⟨(x.A,x.F),x.disjoint,x.avoids⟩ := rfl

theorem word (x : MonomialIndex G c) :
    equiv G c hc (EvenWittGraphRealization.word G c x) = Finsupp.single x 1 := by
  ext y
  rw [apply_value]
  by_cases hI : y.I = x.I
  · let ax : EvenWittWordIndex.LocalIndex c y.I :=
      ⟨(x.A,x.F),hI.symm ▸ x.disjoint,hI.symm ▸ x.avoids⟩
    have hw : EvenWittGraphRealization.word G c x ⟨y.I,y.independent⟩ =
        EvenWittWordBasis.basis c y.I (hc y.I y.independent) ax := by
      rw [EvenWittWordBasis.basis_word]
      simp only [EvenWittGraphRealization.word,if_pos hI,ax]
    rw [hw,Basis.repr_self,Finsupp.single_apply,Finsupp.single_apply]
    have he : ax = ⟨(y.A,y.F),y.disjoint,y.avoids⟩ ↔ x = y := by
      constructor
      · intro h
        have hh := congrArg Subtype.val h
        exact MonomialIndex.ext hI.symm (congrArg Prod.fst hh) (congrArg Prod.snd hh)
      · intro h
        subst y
        rfl
    simp only [he]
  · have hw : EvenWittGraphRealization.word G c x ⟨y.I,y.independent⟩ = 0 := by
      simp only [EvenWittGraphRealization.word,if_neg hI]
    have hxy : x ≠ y := by intro h; subst y; exact hI rfl
    simp [hw,hxy]

theorem realization_eq : realization G c = (equiv G c hc).symm.toLinearMap := by
  apply Finsupp.lhom_ext
  intro x r
  apply (equiv G c hc).injective
  rw [EvenWittGraphRealization.single,map_smul,word]
  simp

theorem differential (f : Coefficients G c) :
    equiv G c hc (OriginalWittIntegerDifferential.differential (EvenWittColumns.frozenMatrix c)
      (Allowed G) (hereditary G) (independentEntries G c) f) =
      monomialDifferential ℤ (equiv G c hc f) := by
  have hh : (OriginalWittIntegerDifferential.differential (EvenWittColumns.frozenMatrix c)
      (Allowed G) (hereditary G) (independentEntries G c)).toIntLinearMap.comp (realization G c) =
        (realization G c).comp (monomialDifferential ℤ) := by
    apply Finsupp.lhom_ext
    intro x r
    change OriginalWittIntegerDifferential.differential (EvenWittColumns.frozenMatrix c) (Allowed G) (hereditary G) (independentEntries G c) (realization G c (Finsupp.single x r)) =
      realization G c (monomialDifferential ℤ (Finsupp.single x r))
    rw [EvenWittGraphRealization.single,map_zsmul,EvenWittGraphRealization.differential_word]
    simp only [monomialDifferential,Finsupp.linearCombination_single,map_smul]
  obtain ⟨a,rfl⟩ := (equiv G c hc).symm.surjective f
  have ha := LinearMap.congr_fun hh a
  change OriginalWittIntegerDifferential.differential (EvenWittColumns.frozenMatrix c) (Allowed G) (hereditary G) (independentEntries G c) (realization G c a) =
    realization G c (monomialDifferential ℤ a) at ha
  rw [realization_eq G c hc] at ha
  simpa only [LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply] using congrArg (equiv G c hc) ha

#print axioms sigmaEquiv
#print axioms equiv
#print axioms apply_value
#print axioms word
#print axioms realization_eq
#print axioms differential
end Verification.EvenWittGraphCoefficients
