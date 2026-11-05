/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphTensorTFFromChain
import Verification.GraphTensorMultiplicity

/-!
# Graph Tensor TF Free Family

With integral graph TF, the actual compressed coefficient family is
a finite power. Its exponent is the exact weighted sum of ranks of the
actual integral independence cohomology groups.
-/
noncomputable section
open scoped Classical
namespace Verification.GraphTensorTFFreeFamily
variable {V C : Type} [Fintype V] [Fintype C] [LinearOrder V] [LinearOrder C]
variable (G : SimpleGraph V) (c : V → C) (p : ℕ)

def Index := Σ T : Finset V,
  Fin (GraphBlockMultiplicity.multiplicity c T) × Fin (GraphTensorTF.betti G c T p)

def indexFintype : Fintype (Index G c p) := inferInstanceAs (Fintype (Σ T : Finset V,
  Fin (GraphBlockMultiplicity.multiplicity c T) × Fin (GraphTensorTF.betti G c T p)))
attribute [instance] indexFintype

def rank : ℕ := ∑ T : Finset V,
  GraphBlockMultiplicity.multiplicity c T * GraphTensorTF.betti G c T p

theorem index_card : Fintype.card (Index G c p) = rank G c p := by
  simp only [Index,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin,rank]

def indexFinEquiv : Index G c p ≃ Fin (rank G c p) :=
  (Fintype.equivFin _).trans (finCongr (index_card G c p))

variable (A : Type) [AddCommGroup A]

def curryEquiv :
    ((T : Finset V) → Fin (GraphBlockMultiplicity.multiplicity c T) →
      Fin (GraphTensorTF.betti G c T p) → A) ≃+ (Index G c p → A) where
  toFun f i := f i.1 i.2.1 i.2.2
  invFun f T a b := f ⟨T,a,b⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

def coefficientEquiv (h : GraphChainTF.ChainGraphFree G) (hp : 0 < p) :
    ((T : Finset V) → Fin (GraphBlockMultiplicity.multiplicity c T) →
      (GraphTensorCohomology.simplex G c A (T,∅)).homology p) ≃+ (Fin (rank G c p) → A) :=
  (AddEquiv.piCongrRight (fun T => AddEquiv.piCongrRight (fun _ =>
    GraphTensorTFFromChain.coefficientEquiv G c h T A p hp))).trans
      ((curryEquiv G c p A).trans
        (LinearEquiv.piCongrLeft' ℤ (fun _ => A) (indexFinEquiv G c p)).toAddEquiv)

#print axioms Index
#print axioms indexFintype
#print axioms rank
#print axioms index_card
#print axioms indexFinEquiv
#print axioms curryEquiv
#print axioms coefficientEquiv
end Verification.GraphTensorTFFreeFamily
