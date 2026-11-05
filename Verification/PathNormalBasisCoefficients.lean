/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathStratumGrading

/-!
# Path Normal Basis Coefficients

The finite endpoint bases have literal singleton word coefficients on
their own stratum, complementing the already proved off-stratum zeros.
-/

namespace Verification.PathNormalBasisCoefficients

open Classical Verification.PathCompression Verification.PathCochains
  Verification.PathEndpointWords Verification.PathNormalizedBasis Verification.PathEndpointCoordinates

variable {R : Type*} [CommRing R]

theorem normalCoordinates_inverse_word (B : List Bool → Prop) (n : ℕ)
    (I : Config n) (w : NormalWord B (available I.val (n+2)).card) :
    (((normalCoordinates (R := R) B n).symm (Pi.single ⟨I,w⟩ 1)) I).val=Finsupp.single w.val 1 := by
  apply Finsupp.ext
  intro v
  by_cases hv : v.length=(available I.val (n+2)).card ∧ B v
  · have he := congrFun ((normalCoordinates (R := R) B n).apply_symm_apply (Pi.single ⟨I,w⟩ 1))
      (⟨I,⟨v,hv⟩⟩ : NormalIndex B n)
    rw [normalCoordinates_apply] at he
    simpa [Pi.single_apply,Sigma.mk.inj_iff,Subtype.ext_iff,
      Finsupp.single_apply,eq_comm] using he
  · have hh := (((normalCoordinates (R := R) B n).symm (Pi.single ⟨I,w⟩ 1)) I).property
    have hz := (Finsupp.mem_supported' R _).mp hh v hv
    have hne : w.val ≠ v := by
      intro he
      apply hv
      exact he ▸ w.property
    rw [hz,Finsupp.single_eq_of_ne hne]

theorem zCoefficients_inverse_word (ρ : R) (n : ℕ)
    (I : Config n) (w : NormalWord RightNormal (available I.val (n+2)).card) :
    ((((zCoefficients ρ n).symm (Pi.single ⟨I,w⟩ 1)).val I).val)=Finsupp.single w.val 1 := by
  exact normalCoordinates_inverse_word RightNormal n I w

theorem yCoefficients_inverse_word (ρ : R) (a : ℕ)
    (I : Config (2*a)) (w : NormalWord BothNormal (available I.val (2*a+2)).card) :
    ((((yCoefficients ρ a).symm (Pi.single ⟨I,w⟩ 1)).val I).val)=Finsupp.single w.val 1 := by
  exact normalCoordinates_inverse_word BothNormal (2*a) I w

#print axioms normalCoordinates_inverse_word
#print axioms zCoefficients_inverse_word
#print axioms yCoefficients_inverse_word

end Verification.PathNormalBasisCoefficients
