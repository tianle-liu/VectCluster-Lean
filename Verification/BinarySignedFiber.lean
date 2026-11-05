/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CharacterGenerators
import Mathlib.Data.ZMod.IntUnitsPower
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Binary Signed Fiber

Signed elementary-abelian group-algebra fibers. The finite generator
relations, including their signs, produce the actual complementary group
algebra. All splittings below are ordinary linear-algebra constructions.
-/
noncomputable section
open scoped Classical
namespace Verification.BinarySignedFiber
open MonoidAlgebra Verification.SplitTorusFiber Verification.CharacterGenerators
variable {ι M Q : Type*} [Fintype ι] [AddCommGroup M] [Module (ZMod 2) M]
  [AddCommGroup Q] [Module (ZMod 2) Q]

def character (u : ι → ℤˣ) : Multiplicative (ι → ZMod 2) →* ℤˣ :=
  AddMonoidHom.toMultiplicative''
    (((Pi.basisFun (ZMod 2) ι).constr (ZMod 2) (fun i => Additive.ofMul (u i))).toAddMonoidHom)

theorem character_single (u : ι → ℤˣ) (i : ι) :
    character u (Multiplicative.ofAdd (Pi.single i 1)) = u i := by
  change Additive.toMul (((Pi.basisFun (ZMod 2) ι).constr (ZMod 2)
    (fun i => Additive.ofMul (u i))) ((Pi.basisFun (ZMod 2) ι) i)) = _
  rw [Basis.constr_basis]
  rfl

theorem single_generates :
    Subgroup.closure (Set.range (fun i : ι =>
      Multiplicative.ofAdd (Pi.single i (1:ZMod 2)))) = ⊤ := by
  apply top_unique
  intro x _
  have hx : x = ∏ i, (Multiplicative.ofAdd (Pi.single i (1:ZMod 2))) ^
      (Multiplicative.toAdd x i).val := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_prod,toAdd_pow,toAdd_ofAdd]
    funext j
    simp only [Finset.sum_apply,Pi.smul_apply]
    simp [Pi.single_apply,nsmul_eq_mul]
  rw [hx]
  apply Subgroup.prod_mem
  intro i _
  exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self i)) _

def groupSplitting (e : M ≃ₗ[ZMod 2] ((ι → ZMod 2) × Q)) :
    Multiplicative M ≃* (Multiplicative (ι → ZMod 2) × Multiplicative Q) :=
  e.toAddEquiv.toMultiplicative.trans (MulEquiv.prodMultiplicative _ _)

def prescribedIdeal (f : (ι → ZMod 2) →ₗ[ZMod 2] M) (u : ι → ℤˣ) :
    Ideal (MonoidAlgebra ℤ (Multiplicative M)) :=
  Ideal.span (Set.range fun i => of ℤ _ (Multiplicative.ofAdd (f (Pi.single i 1))) -
    algebraMap ℤ _ (u i : ℤ))

theorem prescribedIdeal_map (f : (ι → ZMod 2) →ₗ[ZMod 2] M) (u : ι → ℤˣ)
    (e : M ≃ₗ[ZMod 2] ((ι → ZMod 2) × Q)) (he : ∀ x, e (f x) = (x,0)) :
    (prescribedIdeal f u).map (domCongr ℤ ℤ (groupSplitting e)).toRingHom =
      generatorRelations (K := Multiplicative Q) (character u)
        (fun i => Multiplicative.ofAdd (Pi.single i (1:ZMod 2))) := by
  rw [prescribedIdeal,Ideal.map_span,← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  simp only [Function.comp_apply,map_sub,AlgEquiv.commutes]
  change (domCongr ℤ ℤ (groupSplitting e)) (Finsupp.single _ 1) - _ = _
  rw [domCongr_single]
  have h : groupSplitting e (Multiplicative.ofAdd (f (Pi.single i 1))) =
      (Multiplicative.ofAdd (Pi.single i 1),1) := by
    change (Multiplicative.ofAdd (e (f (Pi.single i 1))).1,
      Multiplicative.ofAdd (e (f (Pi.single i 1))).2) = _
    rw [he]
    rfl
  rw [h]
  simp [relation,character_single,of_apply]

def fiberEquiv (f : (ι → ZMod 2) →ₗ[ZMod 2] M) (u : ι → ℤˣ)
    (e : M ≃ₗ[ZMod 2] ((ι → ZMod 2) × Q)) (he : ∀ x, e (f x) = (x,0)) :
    (MonoidAlgebra ℤ (Multiplicative M) ⧸ prescribedIdeal f u) ≃ₐ[ℤ]
      MonoidAlgebra ℤ (Multiplicative Q) :=
  (Ideal.quotientEquivAlg (prescribedIdeal f u)
    (generatorRelations (K := Multiplicative Q) (character u)
      (fun i => Multiplicative.ofAdd (Pi.single i (1:ZMod 2))))
    (domCongr ℤ ℤ (groupSplitting e)) (prescribedIdeal_map f u e he).symm).trans
      (generatedFiberEquiv _ _ single_generates)

omit [Fintype ι] in
theorem split_injection (f : (ι → ZMod 2) →ₗ[ZMod 2] M) (hf : Function.Injective f) :
    ∃ e : M ≃ₗ[ZMod 2] ((ι → ZMod 2) × (M ⧸ LinearMap.range f)),
      ∀ x, e (f x) = (x,0) := by
  obtain ⟨q,hq⟩ := Submodule.exists_isCompl (K := ZMod 2) (V := M) (LinearMap.range f)
  let e := (Submodule.prodEquivOfIsCompl (LinearMap.range f) q hq).symm.trans
    (((LinearEquiv.ofInjective f hf).symm).prodCongr
      (Submodule.quotientEquivOfIsCompl (LinearMap.range f) q hq).symm)
  refine ⟨e,?_⟩
  intro x
  change ((LinearEquiv.ofInjective f hf).symm
      ((Submodule.prodEquivOfIsCompl (LinearMap.range f) q hq).symm (f x)).1,
    (Submodule.quotientEquivOfIsCompl (LinearMap.range f) q hq).symm
      ((Submodule.prodEquivOfIsCompl (LinearMap.range f) q hq).symm (f x)).2) = _
  rw [Submodule.prodEquivOfIsCompl_symm_apply_left (LinearMap.range f) q hq
    (⟨f x,⟨x,rfl⟩⟩ : LinearMap.range f)]
  simp only [map_zero,Prod.mk.injEq,and_true]
  exact (LinearEquiv.ofInjective f hf).symm_apply_apply x

def primitiveFiberEquiv (f : (ι → ZMod 2) →ₗ[ZMod 2] M) (hf : Function.Injective f)
    (u : ι → ℤˣ) :
    (MonoidAlgebra ℤ (Multiplicative M) ⧸ prescribedIdeal f u) ≃ₐ[ℤ]
      MonoidAlgebra ℤ (Multiplicative (M ⧸ LinearMap.range f)) :=
  fiberEquiv f u (split_injection f hf).choose (split_injection f hf).choose_spec

#print axioms split_injection
#print axioms primitiveFiberEquiv
#print axioms character
#print axioms character_single
#print axioms single_generates
#print axioms groupSplitting
#print axioms prescribedIdeal
#print axioms prescribedIdeal_map
#print axioms fiberEquiv
end Verification.BinarySignedFiber
