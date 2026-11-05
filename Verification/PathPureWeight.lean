/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathRhoGrading
import Verification.PathZeroEndpointCoefficients
import Verification.PathWeightFiltration

/-!
# Path Pure Weight

The rho-zero operator preserves the exact original weight, not just the
weight filtration. This is proved from the actual face coefficients.
-/

namespace Verification.PathPureWeight

open Classical Verification.PathRhoWords Verification.PathRhoGrading
  Verification.PathCochains Verification.PathRhoConfiguration Verification.PathCompression
  Verification.PathWordWeight Verification.PathEndpointWords Verification.PathNormalizedBasis
  Verification.PathEndpointCoordinates Verification.PathWeightFiltration
  Verification.PathZeroEndpointCoefficients

variable {R : Type*} [CommRing R]

theorem face_zero_weight (ε : R) (i : ℕ) (w v : List Bool)
    (h : w.count true ≠ v.count true+1) : faceColumn ε 0 i w v=0 := by
  rcases column_monomial ε (0:R) i w with hz | ⟨k,d,u,hd,hl,hc,hf⟩
  · rw [hz]; rfl
  · rw [hf]
    cases d with
    | zero =>
      have hn : u ≠ v := by intro he; subst u; exact h (by omega)
      simp [Finsupp.single_apply,hn]
    | succ d => simp

def exactWeight (p s : ℕ) : Submodule R (List Bool →₀ R) :=
  Finsupp.supported R R {w | p+w.count true=s}

theorem face_exact (ε : R) (i p s : ℕ) (x : List Bool →₀ R)
    (hx : x ∈ exactWeight (R := R) p s) :
    face ε 0 i x ∈ exactWeight (R := R) (p+1) s := by
  have hh : exactWeight (R := R) p s ≤ (exactWeight (p+1) s).comap (face ε 0 i) := by
    rw [exactWeight,Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨w,hw,rfl⟩
    change face ε 0 i (Finsupp.single w 1) ∈ exactWeight (R := R) (p+1) s
    rw [face_single]
    apply (Finsupp.mem_supported' R _).mpr
    intro v hv
    apply face_zero_weight
    change p+w.count true=s at hw
    change ¬(p+1)+v.count true=s at hv
    omega
  exact hh hx

def TotalExact (n s : ℕ) (x : Total (R := R) n) : Prop :=
  ∀ I, (x I).val ∈ exactWeight (R := R) I.val.card s

theorem differential_exact (g : R) (n s : ℕ) (x : Total (R := R) n)
    (hx : TotalExact n s x) : TotalExact n s (differential g 0 n x) := by
  intro J
  change ambientDifferential g 0 n (inclusion n x) J ∈ exactWeight (R := R) J.val.card s
  rw [ambientDifferential_apply]
  apply Submodule.sum_mem
  intro j hj
  change incidence g (eraseConfig J j).val j •
    face (-g) 0 (faceIndex (eraseConfig J j).val j) (x (eraseConfig J j)).val ∈ _
  apply (exactWeight J.val.card s).smul_mem
  have hc : (eraseConfig J j).val.card+1=J.val.card := Finset.card_erase_add_one hj
  have hh := face_exact (-g) (faceIndex (eraseConfig J j).val j)
    (eraseConfig J j).val.card s (x (eraseConfig J j)).val (hx (eraseConfig J j))
  simpa only [hc] using hh

theorem normal_inverse_exact (B : List Bool → Prop) (n : ℕ) (x : NormalIndex B n) (I : Config n) :
    (((normalCoordinates (R := R) B n).symm (Pi.single x 1)) I).val ∈
      exactWeight (R := R) I.val.card (weight x) := by
  apply (Finsupp.mem_supported' R _).mpr
  intro w hw
  by_cases hn : w.length=(available I.val (n+2)).card ∧ B w
  · have hk : (⟨I,⟨w,hn⟩⟩ : NormalIndex B n) ≠ x := by
      intro he
      apply hw
      change I.val.card+w.count true=weight x
      rw [← he]
      rfl
    have he := congrFun ((normalCoordinates (R := R) B n).apply_symm_apply (Pi.single x 1))
      (⟨I,⟨w,hn⟩⟩ : NormalIndex B n)
    rw [normalCoordinates_apply] at he
    simpa only [Pi.single_eq_of_ne hk] using he
  · exact (Finsupp.mem_supported' R _).mp
      (((normalCoordinates (R := R) B n).symm (Pi.single x 1)) I).property w hn

#print axioms face_zero_weight
#print axioms exactWeight
#print axioms face_exact
#print axioms TotalExact
#print axioms differential_exact
#print axioms normal_inverse_exact

end Verification.PathPureWeight
