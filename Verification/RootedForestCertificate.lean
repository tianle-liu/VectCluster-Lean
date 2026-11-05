/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib

/-!
# Rooted Forest Certificate

A uniform finite-forest certificate: every vertex has at most one parent
and the parent strictly lowers a natural height. This describes arbitrary
rooted forests, not just paths.
-/
namespace Verification.RootedForestCertificate
structure Forest (V : Type*) where
  parent : V→Option V
  height : V→ℕ
  decrease : ∀i j,parent i=some j→height j<height i

variable {V W : Type*}
namespace Forest
def Adj (P : Forest V) (i j : V) : Prop := P.parent i=some j ∨ P.parent j=some i

theorem irreflexive (P : Forest V) (i : V) : ¬P.Adj i i := by
  rintro (h|h) <;> exact (Nat.lt_irrefl _ (P.decrease i i h))

def transport (P : Forest V) (e : V≃W) : Forest W where
  parent w := (P.parent (e.symm w)).map e
  height w := P.height (e.symm w)
  decrease i j h := by
    obtain ⟨v,hv,hj⟩ := Option.map_eq_some_iff.mp h
    subst j
    simpa using P.decrease (e.symm i) v hv

theorem transport_adj (P : Forest V) (e : V≃W) (i j : W) :
    (P.transport e).Adj i j ↔ P.Adj (e.symm i) (e.symm j) := by
  have he (v : V) (w : W) : (P.parent v).map e=some w ↔ P.parent v=some (e.symm w) := by
    constructor
    · intro hh
      obtain ⟨x,hx,rfl⟩ := Option.map_eq_some_iff.mp hh
      simpa using hx
    · intro hh
      rw [hh]
      simp
  exact or_congr (he _ _) (he _ _)

def disjoint {I : Type*} {K : I→Type*} (P : ∀i,Forest (K i)) : Forest (Sigma K) where
  parent v := ((P v.1).parent v.2).map (Sigma.mk v.1)
  height v := (P v.1).height v.2
  decrease v w h := by
    obtain ⟨x,hx,hvw⟩ := Option.map_eq_some_iff.mp h
    subst w
    exact (P v.1).decrease v.2 x hx

end Forest

#print axioms Forest
#print axioms Forest.Adj
#print axioms Forest.irreflexive
#print axioms Forest.transport
#print axioms Forest.transport_adj
#print axioms Forest.disjoint
end Verification.RootedForestCertificate
