/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalGlobalGenerators
import Verification.PathEndpointMonomials

/-!
# Path Original Y Presentation

The unfrozen original exchange matrix is the literal nearest-neighbor
path algebra with both endpoints one. The equivalence fixes both original
and mutated variables; even length specializes this to the article's Y.
-/
noncomputable section
namespace Verification.PathOriginalYPresentation
open Verification.FrozenAcyclicCover Verification.PathPresentation
open Verification.PathAdjacencyMonomials Verification.PathEndpointMonomials
open scoped BigOperators

def matrix (n : ℕ) : (Fin n ⊕ Empty) → (Fin n ⊕ Empty) → ℤ :=
  fun a => Sum.elim (fun i => Sum.elim (fun k => PathLattice.pathMatrix n k i) Empty.elim a) Empty.elim

variable {T : Type} [CommRing T] {n : ℕ}

theorem exchange_sum (xx : Fin n → T) (i : Fin n) :
    (∏ a : Fin n ⊕ Empty, Sum.elim xx Empty.elim a ^ (matrix n a (Sum.inl i)).toNat)+
      (∏ a : Fin n ⊕ Empty, Sum.elim xx Empty.elim a ^ (-matrix n a (Sum.inl i)).toNat)=
        boundary 1 1 xx i.castSucc.castSucc+boundary 1 1 xx i.succ.succ := by
  simp only [Fintype.prod_sum_type,matrix,Sum.elim_inl,Fintype.prod_empty,mul_one,
    positive_product,negative_product]
  have h₁ := previous_boundary (1:T) 1 xx i
  have h₂ := next_boundary (1:T) 1 xx i
  simp only [ite_self,one_mul] at h₁ h₂
  rw [h₁,h₂]

variable (R : Type) [CommRing R] (n : ℕ)
abbrev Original := Global R Empty n (matrix n)

def originalX (i : Fin n) : Original R n := initial R Empty n (matrix n) (Sum.inl i)
def originalY (i : Fin n) : Original R n := mutated R Empty n (matrix n) i

theorem original_equations : Equations (1:Original R n) 1 (originalX R n) (originalY R n) := by
  intro i
  have hh := literal_equation R Empty n (matrix n) i
  have he : initial R Empty n (matrix n)=Sum.elim (originalX R n) Empty.elim := by
    funext a
    cases a with
    | inl a => rfl
    | inr a => exact a.elim
  change originalX R n i*originalY R n i=_ at hh
  rw [he,exchange_sum] at hh
  exact hh

def toOriginal : PathAlgebra n (1:R) 1 →ₐ[R] Original R n :=
  PathPresentation.lift 1 1 (originalX R n) (originalY R n) (by
    simpa only [map_one] using original_equations R n)

def toPath : Original R n →ₐ[R] PathAlgebra n (1:R) 1 where
  __ := OriginalGlobalGenerators.lift R Empty n (matrix n)
    (algebraMap R _) (Sum.elim (x (1:R) 1) Empty.elim) (y (1:R) 1)
    (fun i => by rw [exchange_sum]; simpa only [map_one] using equations n (1:R) 1 i)
    (fun e => e.elim)
  commutes' := OriginalGlobalGenerators.lift_scalar R Empty n (matrix n) _ _ _ _ _

theorem toOriginal_x (i : Fin n) : toOriginal R n (x (1:R) 1 i)=originalX R n i :=
  PathPresentation.lift_x _ _ _ _ _ i

theorem toOriginal_y (i : Fin n) : toOriginal R n (y (1:R) 1 i)=originalY R n i :=
  PathPresentation.lift_y _ _ _ _ _ i

theorem toPath_x (i : Fin n) : toPath R n (originalX R n i)=x (1:R) 1 i :=
  OriginalGlobalGenerators.lift_initial R Empty n (matrix n) _ _ _ _ (fun e => e.elim) (Sum.inl i)

theorem toPath_y (i : Fin n) : toPath R n (originalY R n i)=y (1:R) 1 i :=
  OriginalGlobalGenerators.lift_mutated R Empty n (matrix n) _ _ _ _ (fun e => e.elim) i

theorem toPath_toOriginal : (toPath R n).comp (toOriginal R n)=AlgHom.id R _ := by
  apply PathPresentation.hom_ext
  · intro i
    change toPath R n (toOriginal R n (x (1:R) 1 i))=x (1:R) 1 i
    rw [toOriginal_x,toPath_x]
  · intro i
    change toPath R n (toOriginal R n (y (1:R) 1 i))=y (1:R) 1 i
    rw [toOriginal_y,toPath_y]

theorem toOriginal_toPath : (toOriginal R n).comp (toPath R n)=AlgHom.id R _ := by
  apply AlgHom.coe_ringHom_injective
  apply OriginalGlobalGenerators.hom_ext R Empty n (matrix n)
  · intro r
    change toOriginal R n (toPath R n (algebraMap R _ r))=algebraMap R _ r
    rw [AlgHom.commutes,AlgHom.commutes]
  · intro i
    cases i with
    | inl i =>
      change toOriginal R n (toPath R n (originalX R n i))=originalX R n i
      rw [toPath_x,toOriginal_x]
    | inr e => exact e.elim
  · intro i
    change toOriginal R n (toPath R n (originalY R n i))=originalY R n i
    rw [toPath_y,toOriginal_y]

def presentationEquiv : PathAlgebra n (1:R) 1 ≃ₐ[R] Original R n :=
  AlgEquiv.ofAlgHom (toOriginal R n) (toPath R n) (toOriginal_toPath R n) (toPath_toOriginal R n)

theorem presentation_x (i : Fin n) : presentationEquiv R n (x (1:R) 1 i)=initial R Empty n (matrix n) (Sum.inl i) :=
  toOriginal_x R n i

theorem presentation_y (i : Fin n) : presentationEquiv R n (y (1:R) 1 i)=mutated R Empty n (matrix n) i :=
  toOriginal_y R n i

#print axioms matrix
#print axioms exchange_sum
#print axioms Original
#print axioms originalX
#print axioms originalY
#print axioms original_equations
#print axioms toOriginal
#print axioms toPath
#print axioms toOriginal_x
#print axioms toOriginal_y
#print axioms toPath_x
#print axioms toPath_y
#print axioms toPath_toOriginal
#print axioms toOriginal_toPath
#print axioms presentationEquiv
#print axioms presentation_x
#print axioms presentation_y
end Verification.PathOriginalYPresentation
