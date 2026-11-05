/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Order.Extension.Linear
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Relation

/-!
# Acyclic Enumeration

A genuine finite directed acyclic relation admits a topological
numbering. Acyclicity is the absence of a nonempty directed cycle.
-/
noncomputable section
namespace Verification.AcyclicEnumeration
variable {V : Type} (r : V → V → Prop) (h : ∀ v,¬ Relation.TransGen r v v)

def partialOrder : PartialOrder V where
  le := Relation.ReflTransGen r
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ := Relation.ReflTransGen.trans
  le_antisymm a b hab hba := by
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp hab with he | hab
    · exact he.symm
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp hba with he | hba
    · exact he
    exact (h a (hab.trans hba)).elim

def linearOrder : LinearOrder V := by
  letI := partialOrder r h
  exact (inferInstance : LinearOrder (LinearExtension V))

theorem edge_lt (a b : V) (hab : r a b) : @LT.lt V (linearOrder r h).toLT a b := by
  letI := partialOrder r h
  change (toLinearExtension a)<toLinearExtension b
  apply lt_of_le_of_ne
  · exact toLinearExtension.monotone (Relation.ReflTransGen.single hab)
  · intro he
    have he' : a=b := he
    subst b
    exact h a (Relation.TransGen.single hab)

variable [Fintype V]

def enumeration : Fin (Fintype.card V) ≃ V := by
  letI := linearOrder r h
  exact (Fintype.orderIsoFinOfCardEq V rfl).toEquiv

theorem index_lt (a b : V) (hab : r a b) :
    (enumeration r h).symm a<(enumeration r h).symm b := by
  letI := linearOrder r h
  exact (Fintype.orderIsoFinOfCardEq V rfl).symm.strictMono (edge_lt r h a b hab)

#print axioms partialOrder
#print axioms linearOrder
#print axioms edge_lt
#print axioms enumeration
#print axioms index_lt
end Verification.AcyclicEnumeration
