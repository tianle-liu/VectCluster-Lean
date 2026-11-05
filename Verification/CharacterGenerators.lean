/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SplitTorusFiber
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Character Generators

Reducing the full character-relation ideal to the chosen generating
characters. This connects a primitive column basis to the group-algebra
fiber equivalence, without silently replacing finitely many equations by
an infinite family of equations.
-/
namespace Verification.CharacterGenerators
open MonoidAlgebra Verification.SplitTorusFiber
variable {R H K ι : Type*} [CommRing R] [CommGroup H] [CommGroup K]

noncomputable def generatorRelations (c : H →* Rˣ) (w : ι → H) :
    Ideal (MonoidAlgebra R (H × K)) :=
  Ideal.span (Set.range (fun i => relation c (w i)))

theorem generated_relation_mem (c : H →* Rˣ) (w : ι → H)
    (hw : Subgroup.closure (Set.range w) = ⊤) (h : H) :
    relation (K := K) c h ∈ generatorRelations c w := by
  let J := generatorRelations (K := K) c w
  let q := Ideal.Quotient.mk J
  let f : H →* (MonoidAlgebra R (H × K) ⧸ J) :=
    q.toMonoidHom.comp ((of R (H × K)).comp (MonoidHom.inl H K))
  let g : H →* (MonoidAlgebra R (H × K) ⧸ J) :=
    (algebraMap R _).toMonoidHom.comp ((Units.coeHom R).comp c)
  have hfg : f = g := by
    apply MonoidHom.eq_of_eqOn_dense hw
    rintro _ ⟨i,rfl⟩
    have hi : q (relation c (w i)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
    rw [relation, map_sub] at hi
    exact sub_eq_zero.mp (show f (w i) - g (w i) = 0 from hi)
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q (relation c h) = 0
  rw [relation, map_sub]
  change f h - g h = 0
  rw [hfg, sub_self]

/-- The relation ideal is unchanged by passing from a generating basis to
all its integral products and inverses. -/
theorem generatorRelations_eq (c : H →* Rˣ) (w : ι → H)
    (hw : Subgroup.closure (Set.range w) = ⊤) :
    generatorRelations (K := K) c w = relations c := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact Ideal.subset_span (Set.mem_range_self (w i))
  · apply Ideal.span_le.mpr
    rintro _ ⟨h,rfl⟩
    exact generated_relation_mem c w hw h

/-- The original finite equations already define the translated split fiber. -/
noncomputable def generatedFiberEquiv (c : H →* Rˣ) (w : ι → H)
    (hw : Subgroup.closure (Set.range w) = ⊤) :
    (MonoidAlgebra R (H × K) ⧸ generatorRelations (K := K) c w) ≃ₐ[R]
      MonoidAlgebra R K :=
  (Ideal.quotientEquivAlgOfEq R (generatorRelations_eq c w hw)).trans (fiberEquiv c)

#print axioms generated_relation_mem
#print axioms generatorRelations_eq
#print axioms generatedFiberEquiv
end Verification.CharacterGenerators

-- Explicit dependency audit of the early module constructions.
#print axioms Verification.CharacterGenerators.generatorRelations
