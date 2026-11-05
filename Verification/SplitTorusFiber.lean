/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Split Torus Fiber

The split character-fiber calculation for (AS), at manuscript.tex:507–513.
We work with actual group algebras, so for free abelian H and K these are
the coordinate rings of split tori. Prescribing a unit-valued character on
H in H×K leaves exactly the group algebra of K, over any commutative ring.
The fiber is a quotient algebra, not merely an identification of points.
-/
namespace Verification.SplitTorusFiber
open MonoidAlgebra
variable {R H K : Type*} [CommRing R] [CommGroup H] [CommGroup K]

noncomputable def specializationCharacter (c : H →* Rˣ) :
    (H × K) →* MonoidAlgebra R K where
  toFun a := algebraMap R _ (c a.1 : R) * of R K a.2
  map_one' := by simp; rfl
  map_mul' a b := by simp [mul_mul_mul_comm]

noncomputable def specialize (c : H →* Rˣ) :
    MonoidAlgebra R (H × K) →ₐ[R] MonoidAlgebra R K :=
  lift R (H × K) (MonoidAlgebra R K) (specializationCharacter c)

noncomputable def relation (c : H →* Rˣ) (h : H) : MonoidAlgebra R (H × K) :=
  of R (H × K) (h,1) - algebraMap R _ (c h : R)

noncomputable def relations (c : H →* Rˣ) : Ideal (MonoidAlgebra R (H × K)) :=
  Ideal.span (Set.range (relation c))

theorem specialize_monomial (c : H →* Rˣ) (h : H) (k : K) :
    specialize c (of R (H × K) (h,k)) =
      algebraMap R _ (c h : R) * of R K k := by
  simp [specialize, specializationCharacter]

theorem specialize_relation (c : H →* Rˣ) (h : H) :
    specialize (K := K) c (relation c h) = 0 := by
  rw [relation, map_sub, specialize_monomial, AlgHom.commutes]
  rw [map_one, mul_one, sub_self]

noncomputable def descend (c : H →* Rˣ) :
    (MonoidAlgebra R (H × K) ⧸ relations (K := K) c) →ₐ[R] MonoidAlgebra R K :=
  Ideal.Quotient.liftₐ (relations (K := K) c) (specialize c) (by
    change relations (K := K) c ≤ RingHom.ker (specialize c).toRingHom
    apply Ideal.span_le.mpr
    rintro p ⟨h, rfl⟩
    exact specialize_relation c h)

noncomputable def freeCharacter : K →* MonoidAlgebra R (H × K) where
  toFun k := of R (H × K) (1,k)
  map_one' := by simp; rfl
  map_mul' a b := by simp [← map_mul]

noncomputable def includeFree (c : H →* Rˣ) :
    MonoidAlgebra R K →ₐ[R] (MonoidAlgebra R (H × K) ⧸ relations (K := K) c) :=
  (Ideal.Quotient.mkₐ R (relations (K := K) c)).comp
    (lift R K (MonoidAlgebra R (H × K)) freeCharacter)

theorem quotient_relation (c : H →* Rˣ) (h : H) :
    Ideal.Quotient.mk (relations (K := K) c) (of R (H × K) (h,1)) =
      algebraMap R _ (c h : R) := by
  have hr : Ideal.Quotient.mk (relations (K := K) c) (relation c h) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self h))
  simpa only [relation, map_sub, Ideal.Quotient.mk_algebraMap, sub_eq_zero] using hr

theorem quotient_monomial (c : H →* Rˣ) (h : H) (k : K) :
    Ideal.Quotient.mk (relations (K := K) c) (of R (H × K) (h,k)) =
      algebraMap R _ (c h : R) *
        Ideal.Quotient.mk (relations (K := K) c) (of R (H × K) (1,k)) := by
  rw [show (h,k) = (h,1) * (1,k) by simp, map_mul, map_mul, quotient_relation]

theorem descend_includeFree (c : H →* Rˣ) :
    (descend (K := K) c).comp (includeFree c) = AlgHom.id R _ := by
  apply MonoidAlgebra.algHom_ext
  intro k
  change descend c (includeFree c (of R K k)) = of R K k
  simp only [descend, includeFree, AlgHom.comp_apply, lift_of, freeCharacter]
  change specialize c (of R (H × K) (1,k)) = of R K k
  rw [specialize_monomial]
  simp

theorem includeFree_descend (c : H →* Rˣ) :
    (includeFree (K := K) c).comp (descend c) = AlgHom.id R _ := by
  apply Ideal.Quotient.algHom_ext
  apply MonoidAlgebra.algHom_ext
  rintro ⟨h,k⟩
  change includeFree c (specialize c (of R (H × K) (h,k))) =
    Ideal.Quotient.mk (relations (K := K) c) (of R (H × K) (h,k))
  rw [specialize_monomial, map_mul, AlgHom.commutes]
  simp only [includeFree, AlgHom.comp_apply, lift_of, freeCharacter]
  exact (quotient_monomial c h k).symm

noncomputable def fiberEquiv (c : H →* Rˣ) :
    (MonoidAlgebra R (H × K) ⧸ relations (K := K) c) ≃ₐ[R] MonoidAlgebra R K :=
  AlgEquiv.ofAlgHom (descend c) (includeFree c)
    (descend_includeFree c) (includeFree_descend c)

variable {G : Type*} [CommGroup G]

/-- The character equations in the original coordinates of a split lattice. -/
noncomputable def transportedRelation (e : G ≃* (H × K)) (c : H →* Rˣ) (h : H) :
    MonoidAlgebra R G :=
  of R G (e.symm (h,1)) - algebraMap R _ (c h : R)

noncomputable def transportedRelations (e : G ≃* (H × K)) (c : H →* Rˣ) :
    Ideal (MonoidAlgebra R G) := Ideal.span (Set.range (transportedRelation e c))

theorem transport_relations (e : G ≃* (H × K)) (c : H →* Rˣ) :
    (transportedRelations e c).map (domCongr R R e).toRingHom = relations (K := K) c := by
  rw [transportedRelations, Ideal.map_span, ← Set.range_comp]
  unfold relations
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext h
  simp [transportedRelation, relation]

/-- A split character lattice gives the actual translated torus fiber in
any original lattice coordinates, by an explicit quotient algebra map. -/
noncomputable def splitCharacterFiberEquiv (e : G ≃* (H × K)) (c : H →* Rˣ) :
    (MonoidAlgebra R G ⧸ transportedRelations e c) ≃ₐ[R] MonoidAlgebra R K :=
  (Ideal.quotientEquivAlg (transportedRelations e c) (relations (K := K) c)
    (domCongr R R e) (transport_relations e c).symm).trans (fiberEquiv c)

#print axioms transport_relations
#print axioms splitCharacterFiberEquiv
#print axioms specialize_monomial
#print axioms specialize_relation
#print axioms quotient_relation
#print axioms quotient_monomial
#print axioms descend_includeFree
#print axioms includeFree_descend
#print axioms fiberEquiv
end Verification.SplitTorusFiber

-- Explicit dependency audit of the early module constructions.
#print axioms Verification.SplitTorusFiber.descend
#print axioms Verification.SplitTorusFiber.freeCharacter
#print axioms Verification.SplitTorusFiber.includeFree
#print axioms Verification.SplitTorusFiber.relation
#print axioms Verification.SplitTorusFiber.relations
#print axioms Verification.SplitTorusFiber.specializationCharacter
#print axioms Verification.SplitTorusFiber.specialize
#print axioms Verification.SplitTorusFiber.transportedRelation
#print axioms Verification.SplitTorusFiber.transportedRelations
