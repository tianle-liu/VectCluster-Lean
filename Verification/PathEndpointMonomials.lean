/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathAdjacencyMonomials
import Verification.ScalarExchangeRelabel

/-!
# Path Endpoint Monomials

The distinguished endpoint coefficients in the standard path exchange
matrix give the literal two-endpoint nearest-neighbour polynomial.
-/
noncomputable section
namespace Verification.PathEndpointMonomials
open Verification.PathAdjacencyMonomials
open scoped BigOperators
variable {R : Type*} [CommRing R] {n : ℕ}

theorem previous_boundary (a b : R) (x : Fin n → R) (i : Fin n) :
    (if i.val=0 then a else 1)*previous x i=PathPresentation.boundary a b x i.castSucc.castSucc := by
  by_cases h : i.val=0
  · have hi : i.castSucc.castSucc=0 := Fin.ext h
    rw [if_pos h,previous,dif_neg (by omega),mul_one,hi,PathPresentation.boundary_zero]
  · let j : Fin n := ⟨i.val-1,by omega⟩
    have hi : i.castSucc.castSucc=j.castSucc.succ := by apply Fin.ext;dsimp [j];omega
    rw [if_neg h,one_mul,previous,dif_pos (by omega),hi,PathPresentation.boundary_middle]

theorem next_boundary (a b : R) (x : Fin n → R) (i : Fin n) :
    (if i.val+1=n then b else 1)*next x i=PathPresentation.boundary a b x i.succ.succ := by
  by_cases h : i.val+1=n
  · have hi : i.succ.succ=Fin.last (n+1) := by apply Fin.ext;dsimp;omega
    rw [if_pos h,next,dif_neg (by omega),mul_one,hi,PathPresentation.boundary_last]
  · let j : Fin n := ⟨i.val+1,by omega⟩
    have hi : i.succ.succ=j.castSucc.succ := by apply Fin.ext;rfl
    rw [if_neg h,one_mul,next,dif_pos (by omega),hi,PathPresentation.boundary_middle]

theorem exchange_equations (a b : R) (x y : Fin n → R) :
    (∀ i,x i*y i=(if i.val=0 then a else 1)*(∏ r,x r^(PathLattice.pathMatrix n r i).toNat)+
      (if i.val+1=n then b else 1)*∏ r,x r^(-PathLattice.pathMatrix n r i).toNat) ↔
        PathPresentation.Equations a b x y := by
  simp only [positive_product,negative_product,previous_boundary a b x,next_boundary a b x,PathPresentation.Equations]

theorem powerSum (a b : Rˣ) (i : Fin n) :
    ScalarExchangeRelabel.powerSum R (fun r=>PathLattice.pathMatrix n r i)
      (if i.val=0 then a else 1) (if i.val+1=n then b else 1)=
    PathPresentation.boundary (MvPolynomial.C (a : R)) (MvPolynomial.C (b : R)) MvPolynomial.X i.castSucc.castSucc+
      PathPresentation.boundary (MvPolynomial.C (a : R)) (MvPolynomial.C (b : R)) MvPolynomial.X i.succ.succ := by
  have ha : MvPolynomial.C ((if i.val=0 then a else 1 : Rˣ) : R)=
      (if i.val=0 then (MvPolynomial.C (a : R) : MvPolynomial (Fin n) R) else 1) := by split_ifs <;> simp
  have hb : MvPolynomial.C ((if i.val+1=n then b else 1 : Rˣ) : R)=
      (if i.val+1=n then (MvPolynomial.C (b : R) : MvPolynomial (Fin n) R) else 1) := by split_ifs <;> simp
  rw [ScalarExchangeRelabel.powerSum,ha,hb,positive_product,negative_product,previous_boundary,next_boundary]

#print axioms previous_boundary
#print axioms next_boundary
#print axioms exchange_equations
#print axioms powerSum
end Verification.PathEndpointMonomials
