/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimitiveCharacters
import Verification.PrimitiveTorusRank

/-!
# Explicit Primitive Fiber

A coordinate-compatible primitive character-fiber isomorphism.
Unlike choosing an arbitrary member of a Nonempty AlgEquiv type, the
chosen compatible lattice splitting and its character formula are retained.
-/
noncomputable section
namespace Verification.ExplicitPrimitiveFiber
open MonoidAlgebra Verification.PrimitiveCharacters Verification.SplitTorusFiber
variable {R M P ι : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup P]
variable [Module.Finite ℤ M]
variable (f : P →ₗ[ℤ] M) (hf : Function.Injective f)
variable (hs : FreezingLattice.Saturated (LinearMap.range f))

def splitting : M ≃ₗ[ℤ] (P × (M ⧸ LinearMap.range f)) :=
  (PrimitiveLattice.primitive_columns_split_compatible f hf hs).choose

theorem splitting_column (p : P) : splitting f hf hs (f p) = (p,0) :=
  (PrimitiveLattice.primitive_columns_split_compatible f hf hs).choose_spec p

omit [Module.Finite ℤ M] in
theorem split_monomial {Q : Type*} [AddCommGroup Q]
    (e : M ≃ₗ[ℤ] (P × Q)) (g : P →ₗ[ℤ] M)
    (he : ∀ p, e (g p) = (p,0)) (b : Basis ι ℤ P)
    (c : Multiplicative P →* Rˣ) (m : M) :
    fiberEquivOfSplitting e g he b c
      (Ideal.Quotient.mk (columnIdeal g b c) (of R (Multiplicative M) (Multiplicative.ofAdd m))) =
    algebraMap R _ (c (Multiplicative.ofAdd (e m).1) : R) *
      of R (Multiplicative Q) (Multiplicative.ofAdd (e m).2) := by
  change specialize c (domCongr R R (groupSplitting e)
    (of R (Multiplicative M) (Multiplicative.ofAdd m))) = _
  have hh : domCongr R R (groupSplitting e)
      (of R (Multiplicative M) (Multiplicative.ofAdd m)) =
      of R (Multiplicative P × Multiplicative Q)
        (Multiplicative.ofAdd (e m).1, Multiplicative.ofAdd (e m).2) := by
    change domCongr R R (groupSplitting e) (Finsupp.single _ 1) = Finsupp.single _ 1
    rw [domCongr_single]
    rfl
  rw [hh, specialize_monomial]

def prescribedEquiv (b : Basis ι ℤ P) (u : ι → Rˣ) :
    (MonoidAlgebra R (Multiplicative M) ⧸ prescribedIdeal f b u) ≃ₐ[R]
      MonoidAlgebra R (Multiplicative (M ⧸ LinearMap.range f)) :=
  (Ideal.quotientEquivAlgOfEq R (prescribedIdeal_eq f b u)).trans
    (fiberEquivOfSplitting (splitting f hf hs) f (splitting_column f hf hs) b (basisCharacter b u))

theorem prescribedEquiv_monomial (b : Basis ι ℤ P) (u : ι → Rˣ) (m : M) :
    prescribedEquiv f hf hs b u
      (Ideal.Quotient.mk (prescribedIdeal f b u) (of R (Multiplicative M) (Multiplicative.ofAdd m))) =
    algebraMap R _ (basisCharacter b u (Multiplicative.ofAdd (splitting f hf hs m).1) : R) *
      of R (Multiplicative (M ⧸ LinearMap.range f))
        (Multiplicative.ofAdd (splitting f hf hs m).2) := by
  dsimp only [prescribedEquiv, AlgEquiv.trans_apply]
  rw [Ideal.quotientEquivAlgOfEq_mk]
  exact split_monomial _ _ _ _ _ _

variable {κ : Type*} [Fintype κ]

def torusSplitting (g : P →ₗ[ℤ] (κ →₀ ℤ)) (hg : Function.Injective g)
    (hsg : FreezingLattice.Saturated (LinearMap.range g)) :
    (κ →₀ ℤ) ≃ₗ[ℤ] (P × (Fin (Module.finrank ℤ ((κ →₀ ℤ) ⧸ LinearMap.range g)) →₀ ℤ)) :=
  (splitting g hg hsg).trans
    ((LinearEquiv.refl ℤ P).prodCongr (PrimitiveTorusRank.quotientCoordinates g hsg))

theorem torusSplitting_column (g : P →ₗ[ℤ] (κ →₀ ℤ)) (hg : Function.Injective g)
    (hsg : FreezingLattice.Saturated (LinearMap.range g)) (p : P) :
    torusSplitting g hg hsg (g p) = (p,0) := by
  simp only [torusSplitting, LinearEquiv.trans_apply, splitting_column,
    LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply, map_zero]

def torusEquiv (g : P →ₗ[ℤ] (κ →₀ ℤ)) (hg : Function.Injective g)
    (hsg : FreezingLattice.Saturated (LinearMap.range g)) (b : Basis ι ℤ P) (u : ι → Rˣ) :
    (MonoidAlgebra R (Multiplicative (κ →₀ ℤ)) ⧸ prescribedIdeal g b u) ≃ₐ[R]
      MonoidAlgebra R (Multiplicative (Fin (Module.finrank ℤ ((κ →₀ ℤ) ⧸ LinearMap.range g)) →₀ ℤ)) :=
  (prescribedEquiv g hg hsg b u).trans (PrimitiveTorusRank.quotientTorusEquiv R g hsg)

theorem torusEquiv_monomial (g : P →ₗ[ℤ] (κ →₀ ℤ)) (hg : Function.Injective g)
    (hsg : FreezingLattice.Saturated (LinearMap.range g)) (b : Basis ι ℤ P) (u : ι → Rˣ)
    (m : κ →₀ ℤ) :
    torusEquiv g hg hsg b u (Ideal.Quotient.mk (prescribedIdeal g b u)
      (of R (Multiplicative (κ →₀ ℤ)) (Multiplicative.ofAdd m))) =
    algebraMap R _ (basisCharacter b u (Multiplicative.ofAdd (torusSplitting g hg hsg m).1) : R) *
      of R _ (Multiplicative.ofAdd (torusSplitting g hg hsg m).2) := by
  rw [torusEquiv, AlgEquiv.trans_apply, prescribedEquiv_monomial, map_mul, AlgEquiv.commutes]
  congr 1
  change MonoidAlgebra.domCongr R R _ (Finsupp.single _ 1) = Finsupp.single _ 1
  rw [MonoidAlgebra.domCongr_single]
  rfl

#print axioms splitting
#print axioms splitting_column
#print axioms split_monomial
#print axioms prescribedEquiv
#print axioms prescribedEquiv_monomial
#print axioms torusSplitting
#print axioms torusSplitting_column
#print axioms torusEquiv
#print axioms torusEquiv_monomial
end Verification.ExplicitPrimitiveFiber
