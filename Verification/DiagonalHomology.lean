/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Logic.Equiv.Set

/-!
# Diagonal Homology

Kernel and cokernel of an actual rectangular diagonal operator, including
its unmatched target coordinates. The coefficient maps may have torsion.
-/

noncomputable section
namespace Verification.DiagonalHomology
open Function
open scoped Classical

variable {R M ι κ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (e : ι ↪ κ) (a : ι → Module.End R M)

abbrev Unmatched := {j : κ // j ∉ Set.range e}

def indexEquiv : ι ⊕ Unmatched e ≃ κ :=
  (Equiv.sumCongr (Equiv.ofInjective e e.injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range e))

def coordinates : (κ → M) ≃ₗ[R] (ι → M) × (Unmatched e → M) :=
  (LinearEquiv.piCongrLeft R (fun _ : κ => M) (indexEquiv e)).symm.trans
    (LinearEquiv.sumArrowLequivProdArrow ι (Unmatched e) R M)

theorem coordinates_fst (x : κ → M) (i : ι) : (coordinates (R := R) e x).1 i = x (e i) := rfl

theorem coordinates_snd (x : κ → M) (j : Unmatched e) :
    (coordinates (R := R) e x).2 j = x j.val := rfl

def diagonal : (ι → M) →ₗ[R] (κ → M) :=
  (coordinates (R := R) e).symm.toLinearMap.comp
    ((LinearMap.pi (fun i => (a i).comp (LinearMap.proj i))).prod 0)

theorem diagonal_coordinates (x : ι → M) :
    coordinates (R := R) e (diagonal e a x) = (fun i => a i (x i), 0) :=
  (coordinates (R := R) e).apply_symm_apply _

theorem diagonal_at (x : ι → M) (i : ι) : diagonal e a x (e i) = a i (x i) :=
  congrArg (fun z => z.1 i) (diagonal_coordinates (R := R) e a x)

theorem diagonal_unmatched (x : ι → M) (j : Unmatched e) : diagonal e a x j.val = 0 :=
  congrArg (fun z => z.2 j) (diagonal_coordinates (R := R) e a x)

def kernelEquiv : LinearMap.ker (diagonal e a) ≃ₗ[R] (∀ i, LinearMap.ker (a i)) where
  toFun x i := ⟨x.val i, by
    have h := congrFun x.property (e i)
    simpa only [diagonal_at, Pi.zero_apply] using h⟩
  invFun x := ⟨fun i => (x i).val, by
    apply (coordinates (R := R) e).injective
    rw [diagonal_coordinates, map_zero]
    exact Prod.ext (funext fun i => (x i).property) rfl⟩
  left_inv x := by rfl
  right_inv x := by rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def cokernelProjection : (κ → M) →ₗ[R]
    (Unmatched e → M) × (∀ i, M ⧸ LinearMap.range (a i)) where
  toFun x := (fun j => x j.val, fun i => (LinearMap.range (a i)).mkQ (x (e i)))
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

theorem cokernelProjection_surjective : Function.Surjective (cokernelProjection e a) := by
  rintro ⟨u,v⟩
  choose w hw using fun i => (LinearMap.range (a i)).mkQ_surjective (v i)
  refine ⟨(coordinates (R := R) e).symm (w,u), ?_⟩
  have h := (coordinates (R := R) e).apply_symm_apply (w,u)
  apply Prod.ext
  · exact congrArg Prod.snd h
  · funext i
    change (LinearMap.range (a i)).mkQ ((coordinates (R := R) e).symm (w,u) (e i)) = v i
    change (LinearMap.range (a i)).mkQ ((coordinates (R := R) e ((coordinates (R := R) e).symm (w,u))).1 i) = v i
    rw [h, hw]

theorem cokernelProjection_kernel :
    LinearMap.ker (cokernelProjection e a) = LinearMap.range (diagonal e a) := by
  ext x
  constructor
  · intro hx
    have hu : ∀j : Unmatched e, x j.val=0 := fun j => congrArg (fun z => z.1 j) hx
    have hv : ∀i, x (e i) ∈ LinearMap.range (a i) := by
      intro i
      exact (Submodule.Quotient.mk_eq_zero _).mp (congrArg (fun z => z.2 i) hx)
    choose w hw using hv
    refine ⟨w, ?_⟩
    apply (coordinates (R := R) e).injective
    rw [diagonal_coordinates]
    exact Prod.ext (funext hw) (funext fun j => (hu j).symm)
  · rintro ⟨w,rfl⟩
    apply Prod.ext
    · funext j
      exact diagonal_unmatched e a w j
    · funext i
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨w i, (diagonal_at e a w i).symm⟩

/-- The unpaired target terms and the scalar cokernels split independently. -/
def cokernelEquiv : ((κ → M) ⧸ LinearMap.range (diagonal e a)) ≃ₗ[R]
    (Unmatched e → M) × (∀ i, M ⧸ LinearMap.range (a i)) :=
  (Submodule.quotEquivOfEq _ _ (cokernelProjection_kernel e a).symm).trans
    ((cokernelProjection e a).quotKerEquivOfSurjective (cokernelProjection_surjective e a))

#print axioms Unmatched
#print axioms indexEquiv
#print axioms coordinates
#print axioms coordinates_fst
#print axioms coordinates_snd
#print axioms diagonal
#print axioms diagonal_coordinates
#print axioms diagonal_at
#print axioms diagonal_unmatched
#print axioms kernelEquiv
#print axioms cokernelProjection
#print axioms cokernelProjection_surjective
#print axioms cokernelProjection_kernel
#print axioms cokernelEquiv

end Verification.DiagonalHomology
