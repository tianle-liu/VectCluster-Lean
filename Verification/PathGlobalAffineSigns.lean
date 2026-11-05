/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathSignCompression

/-!
# Path Global Affine Signs

The normal-orientation compensation assembles full-rho affine signs into
an actual automorphism of the original independent-stratum total complex.
-/

namespace Verification.PathGlobalAffineSigns

open Classical Verification.PathCompression Verification.PathCochains
  Verification.PathRhoFinite Verification.PathRhoConfiguration
  Verification.PathAffineSigns Verification.PathAffineIntertwiner Verification.PathSignCompression

variable {R : Type*} [CommRing R] (g ρ : R)

def stratumFactor (a b : Bool) (I : Finset ℕ) : R := ∏ i ∈ I, vertexFactor g a b i

theorem stratumFactor_insert (a b : Bool) (I : Finset ℕ) (j : ℕ) (hj : j ∉ I) :
    stratumFactor g a b (insert j I)=vertexFactor g a b j*stratumFactor g a b I := by
  exact Finset.prod_insert hj

theorem vertexFactor_squared (hg : g*g=1) (a b : Bool) (j : ℕ) :
    vertexFactor g a b j*vertexFactor g a b j=1 := by
  unfold vertexFactor
  split <;> cases a <;> cases b <;> simp [hg]

theorem stratumFactor_squared (hg : g*g=1) (a b : Bool) (I : Finset ℕ) :
    stratumFactor g a b I*stratumFactor g a b I=1 := by
  unfold stratumFactor
  rw [← Finset.prod_mul_distrib]
  simp only [vertexFactor_squared g hg,Finset.prod_const_one]

/-- Every component uses the original zero-set factor and the full affine coordinate substitution. -/
noncomputable def totalSign (a b : Bool) (n : ℕ) : Total (R := R) n →ₗ[R] Total (R := R) n :=
  LinearMap.pi (fun I => LinearMap.codRestrict _
    ((stratumFactor g a b I.val • signMap g ρ a b).comp
      ((layer (available I.val (n+2)).card).subtype.comp (LinearMap.proj I)))
        (fun x => (layer _).smul_mem _ (signMap_mem_layer g ρ a b _ (x I).val (x I).property)))

theorem totalSign_squared (hg : g*g=1) (hr : (1+g)*ρ=0) (a b : Bool) (n : ℕ) :
    (totalSign g ρ a b n).comp (totalSign g ρ a b n)=LinearMap.id := by
  apply LinearMap.ext
  intro x
  funext I
  apply Subtype.ext
  change stratumFactor g a b I.val • signMap g ρ a b
    (stratumFactor g a b I.val • signMap g ρ a b (x I).val)=(x I).val
  rw [map_smul,smul_smul,stratumFactor_squared g hg,one_smul]
  exact LinearMap.congr_fun (sign_squared g ρ hg hr a b) (x I).val

noncomputable def totalSignEquiv (hg : g*g=1) (hr : (1+g)*ρ=0) (a b : Bool) (n : ℕ) :
    Total (R := R) n ≃ₗ[R] Total (R := R) n :=
  LinearEquiv.ofLinear (totalSign g ρ a b n) (totalSign g ρ a b n)
    (totalSign_squared g ρ hg hr a b n) (totalSign_squared g ρ hg hr a b n)

/-- The global normal factors are derived from compressed-coordinate parity. -/
theorem faceMap_sign (hg : g*g=1) (hr : (1+g)*ρ=0) (a b : Bool)
    {n : ℕ} {I : Finset ℕ} (hI : Admissible n I) (j : ℕ) (hj : j ∈ Finset.Icc 1 n)
    (ha : Addable I j) (x : layer (R := R) (available I (n+2)).card) :
    faceMap g ρ I j (stratumFactor g a b I • signMap g ρ a b x.val)=
      stratumFactor g a b (insert j I) • signMap g ρ a b (faceMap g ρ I j x.val) := by
  have hh := layer_intertwining g ρ hg hr a b (faceIndex I j) (available I (n+2)).card
    (faceIndex_valid hI j hj ha) x.val x.property
  rw [normalFactor_compression g a b hI j (Finset.mem_Icc.mp hj).1 ha] at hh
  have hjI : j ∉ I := fun hm => ha.1 (Finset.mem_union_left _ hm)
  simp only [faceMap,LinearMap.smul_apply,map_smul,hh,stratumFactor_insert g a b I j hjI,smul_smul]
  congr 1
  ring

/-- A genuine chain identity for all original strata and every rho term. -/
theorem differential_intertwining (hg : g*g=1) (hr : (1+g)*ρ=0) (a b : Bool) (n : ℕ) :
    (differential g ρ n).comp (totalSign g ρ a b n)=
      (totalSign g ρ a b n).comp (differential g ρ n) := by
  apply LinearMap.ext
  intro x
  funext J
  apply Subtype.ext
  change ambientDifferential g ρ n (inclusion n (totalSign g ρ a b n x)) J=
    stratumFactor g a b J.val • signMap g ρ a b (ambientDifferential g ρ n (inclusion n x) J)
  simp only [ambientDifferential_apply,map_sum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hsub : insert j (eraseConfig J j).val=J.val := Finset.insert_erase hj
  have ha := addable_of_insert (hsub.symm ▸ J.property) (Finset.not_mem_erase _ _)
  have hh := faceMap_sign g ρ hg hr a b (eraseConfig J j).property j (J.property.1 hj) ha
    (x (eraseConfig J j))
  rw [hsub] at hh
  exact hh

#print axioms stratumFactor
#print axioms stratumFactor_insert
#print axioms vertexFactor_squared
#print axioms stratumFactor_squared
#print axioms totalSign
#print axioms totalSign_squared
#print axioms totalSignEquiv
#print axioms faceMap_sign
#print axioms differential_intertwining

end Verification.PathGlobalAffineSigns
