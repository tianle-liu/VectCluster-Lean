/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LaurentExchangeUniversal
import Verification.NestedExchangeComponents
import Mathlib.Data.Matrix.Block

/-!
# Laurent Exchange Components

A literal block-diagonal Laurent exchange matrix separates into its
component quotient rings over the common Laurent coefficient algebra.
-/
noncomputable section
namespace Verification.LaurentExchangeComponents
open Classical MvPolynomial Verification.LaurentScalarModel
open scoped BigOperators TensorProduct
variable (R : Type*) [CommRing R]
variable {I : Type*} [Fintype I] (V : I → Type*) [∀ i,Fintype (V i)]
variable (P : ∀ i,Matrix (V i) (V i) ℤ)

variable {T : Type*} [CommMonoid T]
theorem product_block (x : ((i : I) × V i) → T) (e : ℤ → ℕ) (he : e 0=0)
    (k : I) (j : V k) :
    (∏ v,x v^e (Matrix.blockDiagonal' P v ⟨k,j⟩))=
      ∏ v,x ⟨k,v⟩^e (P k v j) := by
  rw [Fintype.prod_sigma]
  rw [Finset.prod_eq_single k]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro t _ htk
    apply Finset.prod_eq_one
    intro v _
    rw [Matrix.blockDiagonal'_apply_ne P v j htk,he,pow_zero]
  · simp

variable {M : Type*} [AddCommGroup M]
variable (f : ∀ i,V i → M) (c : ∀ i,V i → Rˣ)

theorem exchange_block (v : (i : I) × V i) :
    exchange R (Matrix.blockDiagonal' P) (fun v=>f v.1 v.2) (fun v=>c v.1 v.2) v=
      rename (Sigma.mk v.1) (exchange R (P v.1) (f v.1) (c v.1) v.2) := by
  simp only [exchange,map_add,map_mul,rename_C,map_prod,map_pow,rename_X]
  rw [product_block V P _ Int.toNat (by rfl) v.1 v.2]
  rw [product_block V P _ (fun a=>(-a).toNat) (by rfl) v.1 v.2]

attribute [local instance] MvPolynomial.algebraMvPolynomial
local instance ambientCommRing (α : Type*) :
    CommRing (MvPolynomial α (MvPolynomial α (Coefficients R M))) := inferInstance
local instance componentCommRing (i : I) : CommRing (Presentation R (P i) (f i) (c i)) :=
  inferInstanceAs (CommRing (MvPolynomial (V i) (MvPolynomial (V i) (Coefficients R M)) ⧸ relations R (P i) (f i) (c i)))

abbrev Component (i : I) := Presentation R (P i) (f i) (c i)
abbrev Product := ⨂[Coefficients R M] i,Component R V P f c i

def separatedEquiv :
    Presentation R (Matrix.blockDiagonal' P) (fun v=>f v.1 v.2) (fun v=>c v.1 v.2) ≃ₐ[Coefficients R M]
      Product R V P f c :=
  (Ideal.quotientEquivAlgOfEq (Coefficients R M) (congrArg
    (fun q=>PartnerScaling.relations (fun v=>X v) q)
    (funext (exchange_block R V P f c)))).trans
      (NestedExchangeComponents.equivalence (Coefficients R M) V (fun i=>exchange R (P i) (f i) (c i)))

#print axioms product_block
#print axioms exchange_block
#print axioms ambientCommRing
#print axioms componentCommRing
#print axioms Component
#print axioms Product
#print axioms separatedEquiv
end Verification.LaurentExchangeComponents
