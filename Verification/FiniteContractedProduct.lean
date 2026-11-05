/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ContractedModelTransport
import Verification.FiniteAlgebraSmooth

/-!
# Finite Contracted Product

Actual finite products of smooth affine schemes whose genuine strict
cellular models have already been contracted. The proof recursively uses the
ordinary binary cellular product input; it never assumes a path contraction.
-/
noncomputable section
set_option maxHeartbeats 1000000
namespace Verification.FiniteContractedProduct
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped TensorProduct
open Verification.ContractedStrictProductInput
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [MonoidalCategory A] [MonoidalPreadditive A]
variable [Category C] [Abelian C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) (G : Scheme ⥤ CochainComplex C ℤ)
variable (k : Type) [Field k]

omit [Abelian A] [HasDerivedCategory.{w₁} A] [MonoidalPreadditive A] in
def survivors (base : A) : (n : ℕ)→(Fin n→A)→A
  | 0,_=>base
  | n+1,U=>U 0⊗survivors base n (fun i=>U i.succ)

variable (MS : Standard J L G k)
variable {base : A}
variable (P₀ : ContractedModel J (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of k))))) base)

def model : ∀ (n : ℕ) (S : Fin n→Type) [∀ i,CommRing (S i)] [∀ i,Algebra k (S i)]
    [∀ i,Algebra.Smooth k (S i)] (U : Fin n→A)
    (_P : ∀ i,ContractedModel J (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of (S i)))))) (U i)),
    ContractedModel J (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of (⨂[k] i,S i))))))
      (survivors base n U) := by
  intro n
  induction n with
  | zero =>
    intro S _ _ _ U _
    exact ContractedModelTransport.ring J L G (FiniteAlgebraSplit.empty k S).toRingEquiv P₀
  | succ n ih =>
    intro S _ _ _ U P
    letI : Algebra.Smooth k (⨂[k] i : Fin n,S i.succ) := FiniteAlgebraSmooth.finite k n _
    exact ContractedModelTransport.ring J L G (FiniteAlgebraSplit.equiv k S).toRingEquiv
      (combine J L G k MS (S 0) (⨂[k] i : Fin n,S i.succ) (P 0)
        (ih (fun i=>S i.succ) (fun i=>U i.succ) (fun i=>P i.succ)))

variable (Nis : StrictNisnevichInput.Theory A)
variable (NR : StrictNisnevichRepresentability.Standard J L G Nis k)
variable (HC : StrictCoefficientComparison.StandardHomology (A:=A))

include MS P₀ NR HC in
omit [MonoidalPreadditive A] in
theorem vanishes (n : ℕ) (S : Fin n→Type) [∀ i,CommRing (S i)] [∀ i,Algebra k (S i)]
    [∀ i,Algebra.Smooth k (S i)] (U : Fin n→A)
    (P : ∀ i,ContractedModel J (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of (S i)))))) (U i))
    (F : A) (p : ℕ) (hp : 0<p) : IsZero (Nis.cohomology (Spec (CommRingCat.of (⨂[k] i,S i))) F p) := by
  letI : Algebra.Smooth k (⨂[k] i,S i) := FiniteAlgebraSmooth.finite k n S
  exact ContractedStrictProductInput.vanishes J L G k (⨂[k] i,S i) Nis NR HC
    (model J L G k MS P₀ n S U P) F p hp

#print axioms survivors
#print axioms model
#print axioms vanishes
end Verification.FiniteContractedProduct
