/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimitiveLattice
import Verification.CharacterGenerators
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Int.Cast.Lemmas

/-!
# Primitive Characters

The original AS character-fiber argument with a primitive family as
input, not a pre-assumed torus splitting. Finite basis equations generate
the full character ideal, and the splitting sends each original column
to its specified first coordinate.
-/
namespace Verification.PrimitiveCharacters
open MonoidAlgebra Verification.SplitTorusFiber Verification.CharacterGenerators
variable {R M P ι : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup P]

/-- Arbitrary unit values on a lattice basis extend to a character by
integer powers. No extraction of roots is used. -/
noncomputable def basisCharacter (b : Basis ι ℤ P) (u : ι → Rˣ) :
    Multiplicative P →* Rˣ :=
  AddMonoidHom.toMultiplicative''
    ((Finsupp.liftAddHom (fun i => zmultiplesHom (Additive Rˣ) (Additive.ofMul (u i)))).comp
      b.repr.toAddMonoidHom)

@[simp] theorem basisCharacter_apply (b : Basis ι ℤ P) (u : ι → Rˣ) (i : ι) :
    basisCharacter b u (Multiplicative.ofAdd (b i)) = u i := by
  classical
  change Additive.toMul
    ((Finsupp.liftAddHom (fun i => zmultiplesHom (Additive Rˣ) (Additive.ofMul (u i))))
      (b.repr (b i))) = _
  rw [b.repr_self, Finsupp.liftAddHom_apply_single]
  simp [zmultiplesHom_apply]

/-- A Z-basis generates the corresponding multiplicative character group. -/
theorem basis_generates (b : Basis ι ℤ P) :
    Subgroup.closure (Set.range (fun i => Multiplicative.ofAdd (b i))) = ⊤ := by
  have hb : AddSubgroup.closure (Set.range b) = ⊤ := by
    rw [← Submodule.span_int_eq_addSubgroup_closure, b.span_eq]
    rfl
  have h := congrArg AddSubgroup.toSubgroup hb
  rw [AddSubgroup.toSubgroup_closure] at h
  exact h

noncomputable def columnIdeal (f : P →ₗ[ℤ] M) (b : Basis ι ℤ P)
    (c : Multiplicative P →* Rˣ) : Ideal (MonoidAlgebra R (Multiplicative M)) :=
  Ideal.span (Set.range (fun i =>
    of R (Multiplicative M) (Multiplicative.ofAdd (f (b i))) -
      algebraMap R _ (c (Multiplicative.ofAdd (b i)) : R)))

def groupSplitting {Q : Type*} [AddCommGroup Q] (e : M ≃ₗ[ℤ] (P × Q)) :
    Multiplicative M ≃* (Multiplicative P × Multiplicative Q) :=
  e.toAddEquiv.toMultiplicative.trans (MulEquiv.prodMultiplicative P Q)

theorem groupSplitting_column {Q : Type*} [AddCommGroup Q]
    (e : M ≃ₗ[ℤ] (P × Q)) (f : P →ₗ[ℤ] M)
    (he : ∀ p, e (f p) = (p,0)) (p : P) :
    groupSplitting e (Multiplicative.ofAdd (f p)) = (Multiplicative.ofAdd p,1) := by
  change (Multiplicative.ofAdd (e (f p)).1, Multiplicative.ofAdd (e (f p)).2) = _
  rw [he]
  rfl

theorem columnIdeal_map {Q : Type*} [AddCommGroup Q]
    (e : M ≃ₗ[ℤ] (P × Q)) (f : P →ₗ[ℤ] M)
    (he : ∀ p, e (f p) = (p,0)) (b : Basis ι ℤ P)
    (c : Multiplicative P →* Rˣ) :
    (columnIdeal f b c).map (domCongr R R (groupSplitting e)).toRingHom =
      generatorRelations (K := Multiplicative Q) c (fun i => Multiplicative.ofAdd (b i)) := by
  rw [columnIdeal, Ideal.map_span, ← Set.range_comp]
  unfold generatorRelations
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  change (domCongr R R (groupSplitting e))
    (of R (Multiplicative M) (Multiplicative.ofAdd (f (b i))) -
      algebraMap R _ (c (Multiplicative.ofAdd (b i)) : R)) = _
  rw [map_sub, AlgEquiv.commutes]
  have hmono : (domCongr R R (groupSplitting e))
      (of R (Multiplicative M) (Multiplicative.ofAdd (f (b i)))) =
      of R (Multiplicative P × Multiplicative Q) (Multiplicative.ofAdd (b i),1) := by
    change (domCongr R R (groupSplitting e)) (Finsupp.single _ 1) = Finsupp.single _ 1
    rw [domCongr_single, groupSplitting_column e f he]
  rw [hmono]
  rfl

noncomputable def fiberEquivOfSplitting {Q : Type*} [AddCommGroup Q]
    (e : M ≃ₗ[ℤ] (P × Q)) (f : P →ₗ[ℤ] M)
    (he : ∀ p, e (f p) = (p,0)) (b : Basis ι ℤ P)
    (c : Multiplicative P →* Rˣ) :
    (MonoidAlgebra R (Multiplicative M) ⧸ columnIdeal f b c) ≃ₐ[R]
      MonoidAlgebra R (Multiplicative Q) :=
  (Ideal.quotientEquivAlg (columnIdeal f b c)
    (generatorRelations (K := Multiplicative Q) c (fun i => Multiplicative.ofAdd (b i)))
    (domCongr R R (groupSplitting e)) (columnIdeal_map e f he b c).symm).trans
      (generatedFiberEquiv c _ (basis_generates b))

/-- The finite equations of a primitive independent column family define a
translated split fiber. The splitting conclusion is derived, not assumed. -/
theorem primitive_fiber_equiv [Module.Finite ℤ M]
    (f : P →ₗ[ℤ] M) (hf : Function.Injective f)
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range f))
    (b : Basis ι ℤ P) (c : Multiplicative P →* Rˣ) :
    Nonempty ((MonoidAlgebra R (Multiplicative M) ⧸ columnIdeal f b c) ≃ₐ[R]
      MonoidAlgebra R (Multiplicative (M ⧸ LinearMap.range f))) := by
  obtain ⟨e,he⟩ := Verification.PrimitiveLattice.primitive_columns_split_compatible f hf hs
  exact ⟨fiberEquivOfSplitting e f he b c⟩

/-- The original finite equations with arbitrary prescribed unit constants. -/
noncomputable def prescribedIdeal (f : P →ₗ[ℤ] M) (b : Basis ι ℤ P)
    (u : ι → Rˣ) : Ideal (MonoidAlgebra R (Multiplicative M)) :=
  Ideal.span (Set.range (fun i =>
    of R (Multiplicative M) (Multiplicative.ofAdd (f (b i))) - algebraMap R _ (u i : R)))

theorem prescribedIdeal_eq (f : P →ₗ[ℤ] M) (b : Basis ι ℤ P) (u : ι → Rˣ) :
    prescribedIdeal f b u = columnIdeal f b (basisCharacter b u) := by
  simp only [prescribedIdeal, columnIdeal, basisCharacter_apply]

theorem primitive_prescribed_fiber [Module.Finite ℤ M]
    (f : P →ₗ[ℤ] M) (hf : Function.Injective f)
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range f))
    (b : Basis ι ℤ P) (u : ι → Rˣ) :
    Nonempty ((MonoidAlgebra R (Multiplicative M) ⧸ prescribedIdeal f b u) ≃ₐ[R]
      MonoidAlgebra R (Multiplicative (M ⧸ LinearMap.range f))) := by
  rw [prescribedIdeal_eq]
  exact primitive_fiber_equiv f hf hs b (basisCharacter b u)

#print axioms basisCharacter
#print axioms columnIdeal
#print axioms basisCharacter_apply
#print axioms prescribedIdeal
#print axioms prescribedIdeal_eq
#print axioms primitive_prescribed_fiber
#print axioms basis_generates
#print axioms groupSplitting
#print axioms groupSplitting_column
#print axioms columnIdeal_map
#print axioms fiberEquivOfSplitting
#print axioms primitive_fiber_equiv
end Verification.PrimitiveCharacters
