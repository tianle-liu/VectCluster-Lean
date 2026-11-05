/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathCochains
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Path Cochain Square

Square-zero of the assembled independent-zero-set rho differential. The
sum is paired by exchanging the two original zero vertices; compression,
incidence, and every local rho coefficient were proved in preceding modules.
-/

namespace Verification.PathCochainSquare

open Classical Verification.PathCompression Verification.PathRhoWords
  Verification.PathRhoFinite Verification.PathRhoConfiguration Verification.PathCochains

variable {R : Type*} [CommRing R] (g ρ : R) (n : ℕ)

noncomputable def twoStep (x : Total (R := R) n) (J : Config n) (i j : ℕ) : List Bool →₀ R :=
  faceMap g ρ (eraseConfig J j).val j
    (faceMap g ρ (eraseConfig (eraseConfig J j) i).val i
      (x (eraseConfig (eraseConfig J j) i)).val)

theorem twoStep_ordered (hg : g*g=1) (hr : (1+g)*ρ=0)
    (x : Total (R := R) n) (J : Config n) (i j : ℕ)
    (hi : i ∈ J.val) (hj : j ∈ J.val) (hij : i < j) :
    twoStep g ρ n x J i j+twoStep g ρ n x J j i=0 := by
  let K := eraseConfig (eraseConfig J j) i
  have hki : i ∉ K.val := Finset.not_mem_erase _ _
  have hkj : j ∉ K.val := by simp [K,eraseConfig]
  have hleft : insert i K.val=(eraseConfig J j).val :=
    Finset.insert_erase (Finset.mem_erase.mpr ⟨by omega,hi⟩)
  have he : eraseConfig (eraseConfig J i) j=K := eraseConfig_comm J i j
  have hright : insert j K.val=(eraseConfig J i).val := by
    rw [← he]
    exact Finset.insert_erase (Finset.mem_erase.mpr ⟨by omega,hj⟩)
  have ha := addable_of_insert (hleft.symm ▸ (eraseConfig J j).property) hki
  have hb := addable_of_insert (hright.symm ▸ (eraseConfig J i).property) hkj
  have hs := admissible_pair J.property hi hj hij
  have hh := configuration_pair_cancellation g ρ hg hr K.property i j
    (J.property.1 hi) (J.property.1 hj) ha hb hs (x K)
  rw [hleft,hright] at hh
  unfold twoStep
  rw [he]
  exact hh

theorem twoStep_swap (hg : g*g=1) (hr : (1+g)*ρ=0)
    (x : Total (R := R) n) (J : Config n) (i j : ℕ)
    (hi : i ∈ J.val) (hj : j ∈ J.val) (hij : i ≠ j) :
    twoStep g ρ n x J i j+twoStep g ρ n x J j i=0 := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact twoStep_ordered g ρ n hg hr x J i j hi hj h
  · simpa only [add_comm] using twoStep_ordered g ρ n hg hr x J j i hj hi h

theorem twoStep_sum_zero (hg : g*g=1) (hr : (1+g)*ρ=0)
    (x : Total (R := R) n) (J : Config n) :
    (∑ j ∈ J.val, ∑ i ∈ J.val.erase j, twoStep g ρ n x J i j)=0 := by
  have he : (∑ j ∈ J.val, ∑ i ∈ J.val.erase j, twoStep g ρ n x J i j)=
      ∑ p ∈ J.val ×ˢ J.val, if p.2=p.1 then 0 else twoStep g ρ n x J p.2 p.1 := by
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.filter_ne',Finset.sum_filter]
    simp only [ne_eq,ite_not]
  rw [he]
  apply Finset.sum_involution (fun p _ => (p.2,p.1))
  · intro p hp
    by_cases h : p.2=p.1
    · simp only [h,↓reduceIte,add_zero]
    · simp only [h,Ne.symm h,↓reduceIte]
      exact twoStep_swap g ρ n hg hr x J p.2 p.1
        (Finset.mem_product.mp hp).2 (Finset.mem_product.mp hp).1 h
  · intro p _ hn heq
    have hh : p.2=p.1 := congrArg Prod.fst heq
    exact hn (by simp only [hh,↓reduceIte])
  · intro p hp
    exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp hp).2,(Finset.mem_product.mp hp).1⟩
  · intro p _
    cases p
    rfl

/-- The ambient second differential is zero on the actual minimal-coordinate finite module. -/
theorem ambient_squared (hg : g*g=1) (hr : (1+g)*ρ=0)
    (x : Total (R := R) n) (J : Config n) :
    ambientDifferential g ρ n (ambientDifferential g ρ n (inclusion n x)) J=0 := by
  simp only [ambientDifferential_apply,map_sum]
  exact twoStep_sum_zero g ρ n hg hr x J

/-- The complete finite free path operator squares to zero over the unspecialized formal relations. -/
theorem differential_squared (hg : g*g=1) (hr : (1+g)*ρ=0) :
    (differential g ρ n).comp (differential g ρ n)=0 := by
  apply LinearMap.ext
  intro x
  apply inclusion_injective n
  change inclusion n (differential g ρ n (differential g ρ n x))=inclusion n 0
  have hinc (y : Total (R := R) n) :
      inclusion n (differential g ρ n y)=ambientDifferential g ρ n (inclusion n y) := rfl
  rw [hinc,hinc,map_zero]
  funext J
  exact ambient_squared g ρ n hg hr x J

#print axioms twoStep
#print axioms twoStep_ordered
#print axioms twoStep_swap
#print axioms twoStep_sum_zero
#print axioms ambient_squared
#print axioms differential_squared

end Verification.PathCochainSquare
