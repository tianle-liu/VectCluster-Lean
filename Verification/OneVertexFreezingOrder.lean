/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FreezingOrder

/-!
# One Vertex Freezing Order

If deleting one vertex leaves a hereditary principal-matrix class,
putting that vertex first gives the exact ordering required by freezing.
This isolates the finite Dynkin deletion argument from the geometry.
-/
noncomputable section
namespace Verification.OneVertexFreezingOrder
variable (C : ∀ n : ℕ,(Fin n → Fin n → ℤ) → Prop)

def Hereditary : Prop := ∀ (n m : ℕ) (A : Fin n → Fin n → ℤ),
  C n A → ∀ f : Fin m ↪ Fin n, C m (fun i j => A (f i) (f j))

variable {n : ℕ} (v : Fin n)
def rank (w : Fin n) : ℕ := if w=v then 0 else w.val+1

theorem rank_injective : Function.Injective (rank v) := by
  intro i j hij
  by_cases hi : i=v
  · subst i
    by_cases hj : j=v
    · exact hj.symm
    · simp [rank,hj] at hij
  · by_cases hj : j=v
    · subst j
      simp [rank,hi] at hij
    · simp only [rank,if_neg hi,if_neg hj,Nat.add_right_cancel_iff] at hij
      exact Fin.ext hij

theorem rank_first : rank v v=0 := by simp [rank]

include C in
theorem good (hc : Hereditary C) (A : Fin n → Fin n → ℤ) (E : Fin n → Fin n → Prop)
    (m : ℕ) (f : Fin m ↪ Fin n) (hf : ∀ w,w∈Set.range f ↔ w≠v)
    (hA : C m (fun i j => A (f i) (f j))) : FreezingOrder.Good C A E (rank v) := by
  classical
  intro u k g hg
  have hm : ∀ i : Fin k,∃ j : Fin m,f j=g i := by
    intro i
    apply (hf (g i)).mpr
    intro hi
    have hlt := ((hg (g i)).mp ⟨i,rfl⟩).1
    rw [hi,rank_first] at hlt
    omega
  let g' : Fin k ↪ Fin m :=
    ⟨fun i => Classical.choose (hm i),fun i j hij => g.injective (by
      dsimp only at hij
      rw [←Classical.choose_spec (hm i),←Classical.choose_spec (hm j),hij])⟩
  have hfg : ∀ i,f (g' i)=g i := fun i => Classical.choose_spec (hm i)
  simpa only [hfg] using hc m k (fun i j=>A (f i) (f j)) hA g'

#print axioms Hereditary
#print axioms rank
#print axioms rank_injective
#print axioms rank_first
#print axioms good
end Verification.OneVertexFreezingOrder
