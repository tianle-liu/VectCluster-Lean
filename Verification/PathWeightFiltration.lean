/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathWordWeight
import Verification.PathStratumGrading

/-!
# Path Weight Filtration

The actual endpoint quotient matrices preserve the original path weight
filtration. Transposing gives the manuscript's weight-nondecreasing chain maps.
-/

namespace Verification.PathWeightFiltration

open Classical Verification.PathCompression Verification.PathCochains
  Verification.PathRhoConfiguration Verification.PathEndpointComplex
  Verification.PathEndpointWords Verification.PathNormalizedBasis
  Verification.PathEndpointCoordinates Verification.PathWordWeight

variable {R : Type*} [CommRing R]

def weight {B : List Bool → Prop} {n : ℕ} (x : NormalIndex B n) : ℕ :=
  x.1.val.card+x.2.val.count true

def TotalBounded (n s : ℕ) (x : Total (R := R) n) : Prop :=
  ∀ I, (x I).val ∈ bounded (R := R) I.val.card s

theorem differential_bounded (g ρ : R) (n s : ℕ) (x : Total (R := R) n)
    (hx : TotalBounded n s x) : TotalBounded n s (differential g ρ n x) := by
  intro J
  change ambientDifferential g ρ n (inclusion n x) J ∈ bounded (R := R) J.val.card s
  rw [ambientDifferential_apply]
  apply Submodule.sum_mem
  intro j hj
  change incidence g (eraseConfig J j).val j •
    Verification.PathRhoWords.face (-g) ρ (faceIndex (eraseConfig J j).val j)
      (x (eraseConfig J j)).val ∈ bounded (R := R) J.val.card s
  apply (bounded J.val.card s).smul_mem
  have hc : (eraseConfig J j).val.card+1=J.val.card := Finset.card_erase_add_one hj
  have hh := face_bounded (-g) ρ (faceIndex (eraseConfig J j).val j)
    (eraseConfig J j).val.card s (x (eraseConfig J j)).val (hx (eraseConfig J j))
  simpa only [hc] using hh

theorem zDifferential_bounded (g ρ : R) (n s : ℕ) (x : ZModule ρ n)
    (hx : TotalBounded n s x.val) : TotalBounded n s (zDifferential g ρ n x).val := by
  intro I
  exact right_bounded (endpointConstant ρ n) I.val.card s _
    (differential_bounded g ρ n s x.val hx I)

theorem yDifferential_bounded (g ρ : R) (a s : ℕ) (x : YModule ρ a)
    (hx : TotalBounded (2*a) s x.val) : TotalBounded (2*a) s (yDifferential g ρ a x).val := by
  intro I
  exact left_bounded 0 I.val.card s _ (right_bounded (endpointConstant ρ (2*a)) I.val.card s _
    (differential_bounded g ρ (2*a) s x.val hx I))

/-- The actual inverse basis element is concentrated in its stated original weight. -/
theorem normalCoordinates_inverse_bounded (B : List Bool → Prop) (n : ℕ)
    (k : NormalIndex B n) (I : Config n) :
    ((normalCoordinates (R := R) B n).symm (Pi.single k 1) I).val ∈
      bounded (R := R) I.val.card (weight k) := by
  apply (Finsupp.mem_supported' R _).mpr
  intro w hw
  by_cases hn : w.length=(available I.val (n+2)).card ∧ B w
  · have hk : (⟨I,⟨w,hn⟩⟩ : NormalIndex B n) ≠ k := by
      intro he
      apply hw
      change I.val.card+w.count true ≤ weight k
      rw [← he]
      exact le_refl _
    have he := congrFun ((normalCoordinates (R := R) B n).apply_symm_apply (Pi.single k 1))
      (⟨I,⟨w,hn⟩⟩ : NormalIndex B n)
    rw [normalCoordinates_apply] at he
    simpa only [Pi.single_eq_of_ne hk] using he
  · have hh := ((normalCoordinates (R := R) B n).symm (Pi.single k 1) I).property
    exact (Finsupp.mem_supported' R _).mp hh w hn

theorem zCoefficients_inverse_bounded (ρ : R) (n : ℕ) (k : NormalIndex RightNormal n) :
    TotalBounded n (weight k) ((zCoefficients ρ n).symm (Pi.single k 1)).val := by
  intro I
  exact normalCoordinates_inverse_bounded RightNormal n k I

theorem yCoefficients_inverse_bounded (ρ : R) (a : ℕ) (k : NormalIndex BothNormal (2*a)) :
    TotalBounded (2*a) (weight k) ((yCoefficients ρ a).symm (Pi.single k 1)).val := by
  intro I
  exact normalCoordinates_inverse_bounded BothNormal (2*a) k I

/-- The full cochain matrix cannot increase total original weight. -/
theorem zMatrix_weight (g ρ : R) (n : ℕ) (y x : NormalIndex RightNormal n)
    (h : weight x < weight y) : zMatrix g ρ n y x=0 := by
  simp only [zMatrix,matrixOf,LinearMap.toMatrix'_apply,LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [show (fun i : NormalIndex RightNormal n => if i=x then (1 : R) else 0)=Pi.single x 1 by
    funext i; simp [Pi.single_apply,eq_comm]]
  rw [zCoefficients_apply]
  have hh := zDifferential_bounded g ρ n (weight x) ((zCoefficients ρ n).symm (Pi.single x 1))
    (zCoefficients_inverse_bounded ρ n x) y.1
  exact (Finsupp.mem_supported' R _).mp hh y.2.val (by change ¬weight y ≤ weight x; omega)

theorem yMatrix_weight (g ρ : R) (a : ℕ) (y x : NormalIndex BothNormal (2*a))
    (h : weight x < weight y) : yMatrix g ρ a y x=0 := by
  simp only [yMatrix,matrixOf,LinearMap.toMatrix'_apply,LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [show (fun i : NormalIndex BothNormal (2*a) => if i=x then (1 : R) else 0)=Pi.single x 1 by
    funext i; simp [Pi.single_apply,eq_comm]]
  rw [yCoefficients_apply]
  have hh := yDifferential_bounded g ρ a (weight x) ((yCoefficients ρ a).symm (Pi.single x 1))
    (yCoefficients_inverse_bounded ρ a x) y.1
  exact (Finsupp.mem_supported' R _).mp hh y.2.val (by change ¬weight y ≤ weight x; omega)

/-- In the actual chain convention, weight never decreases. -/
theorem zChain_weight (g ρ : R) (n : ℕ) (y x : NormalIndex RightNormal n)
    (h : weight y < weight x) : (zMatrix g ρ n).transpose y x=0 := zMatrix_weight g ρ n x y h

theorem yChain_weight (g ρ : R) (a : ℕ) (y x : NormalIndex BothNormal (2*a))
    (h : weight y < weight x) : (yMatrix g ρ a).transpose y x=0 := yMatrix_weight g ρ a x y h

#print axioms weight
#print axioms TotalBounded
#print axioms differential_bounded
#print axioms zDifferential_bounded
#print axioms yDifferential_bounded
#print axioms normalCoordinates_inverse_bounded
#print axioms zCoefficients_inverse_bounded
#print axioms yCoefficients_inverse_bounded
#print axioms zMatrix_weight
#print axioms yMatrix_weight
#print axioms zChain_weight
#print axioms yChain_weight

end Verification.PathWeightFiltration
