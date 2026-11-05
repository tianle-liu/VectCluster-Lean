/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ProjectiveGrothendieck
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Projective Field Rank

The Grothendieck-group rank map is constructed by scalar extension
to a field. Over a domain, the fraction field supplies this particular
rank; no unproved rank homomorphism is passed as input.
-/
noncomputable section
universe u
namespace Verification.ProjectiveFieldRank
open Verification.ProjectiveClasses Verification.ProjectiveGrothendieck
open scoped TensorProduct
variable (R k : Type u) [CommRing R] [Field k] [Algebra R k]

def rank (P : Object R) : ℕ := Module.finrank k (k ⊗[R] P)

theorem rank_iso (P Q : Object R) (h : Nonempty (P ≃ₗ[R] Q)) : rank R k P=rank R k Q := by
  obtain ⟨e⟩ := h
  exact (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl k k) e).finrank_eq

theorem rank_free (n : ℕ) : rank R k (of R (Fin n → R))=n := by
  have h := Module.finrank_eq_card_basis ((Pi.basisFun R (Fin n)).baseChange k)
  simpa only [Fintype.card_fin] using h

theorem rank_add (P Q : Object R) : rank R k (of R (P × Q))=rank R k P+rank R k Q := by
  unfold rank
  change Module.finrank k (k ⊗[R] (P × Q)) = _
  rw [(TensorProduct.prodRight R k k P Q).finrank_eq, Module.finrank_prod]

def rankMap : Completion R →+ ℤ :=
  descend R (fun P => (rank R k P : ℤ))
    (fun P Q h => congrArg (fun n : ℕ => (n : ℤ)) (rank_iso R k P Q h))
    (by simp only [rank_free, Nat.cast_zero])
    (fun P Q => by simp only [rank_add, Nat.cast_add])

theorem rankMap_class (P : Object R) : rankMap R k (completionClass R P)=(rank R k P : ℤ) :=
  descend_class R _ _ _ _ P

theorem rankMap_free (n : ℕ) : rankMap R k (completionClass R (of R (Fin n → R)))=n := by
  rw [rankMap_class, rank_free]

#print axioms rank
#print axioms rank_iso
#print axioms rank_free
#print axioms rank_add
#print axioms rankMap
#print axioms rankMap_class
#print axioms rankMap_free
end Verification.ProjectiveFieldRank
