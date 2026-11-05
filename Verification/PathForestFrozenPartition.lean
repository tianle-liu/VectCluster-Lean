/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathForestStandardEndpointColumns
import Verification.FiniteGroupAlgebraTensor

/-!
# Path Forest Frozen Partition

The actual normalized frozen lattice splits into one coefficient lattice
for each path and the unused lattice. Every exchange column lands in its own
component, so its Laurent coefficient has no cross-component dependency.
-/
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 600000
namespace Verification.PathForestFrozenPartition
open Classical Verification.PathForestQuotient Verification.PathForestFrozenBasis
variable {S F : Type} [Fintype S] [Fintype F] (o : S → Bool)
abbrev Unused := Fin (Fintype.card F-Fintype.card (Odd o))
def Lattice : Option S → Type
  | none => Unused (F:=F) o → ℤ
  | some s => PLift (o s=true) → ℤ
instance latticeGroup (i : Option S) : AddCommGroup (Lattice (F:=F) o i) := by
  cases i <;> dsimp [Lattice] <;> infer_instance
instance latticeModule (i : Option S) : Module ℤ (Lattice (F:=F) o i) := by
  cases i <;> dsimp [Lattice] <;> infer_instance

def split : (NewFrozen (F:=F) o → ℤ) ≃ₗ[ℤ] (∀ i,Lattice (F:=F) o i) where
  toFun x i := match i with
    | none => fun u=>x (Sum.inr u)
    | some s => fun h=>x (Sum.inl ⟨s,h.down⟩)
  invFun y i := match i with
    | Sum.inl s => y (some s.val) ⟨s.property⟩
    | Sum.inr u => y none u
  left_inv x := by funext i;cases i <;> rfl
  right_inv y := by funext i;cases i <;> rfl
  map_add' x y := by funext i;cases i <;> rfl
  map_smul' a x := by funext i;cases i <;> rfl

variable (m : S → ℕ)
def endpointColumn (s : S) (i : Fin (PathOrientationBlocks.length (m s) (o s))) :
    Lattice (F:=F) o (some s) := fun _=>if i.val=0 then 1 else 0

theorem column (s : S) (i : Fin (PathOrientationBlocks.length (m s) (o s))) :
    split (F:=F) o (fun a=>standardFrozen (F:=F) m o a
      ((PathForestOrientation.reindex m o).symm ⟨s,i⟩))=
    Pi.single (some s) (endpointColumn (F:=F) o m s i) := by
  funext j
  cases j with
  | none =>
    apply funext
    intro u
    rw [Pi.single_eq_of_ne (by simp : (none : Option S)≠some s)]
    exact PathForestStandardEndpointColumns.unused_row m o u ⟨s,i⟩
  | some t =>
    by_cases h:t=s
    · subst t
      rw [Pi.single_eq_same]
      apply funext
      intro ht
      change standardFrozen (F:=F) m o (Sum.inl ⟨s,ht.down⟩) _=_
      rw [PathForestStandardEndpointColumns.odd_row]
      simp [endpointColumn]
    · rw [Pi.single_eq_of_ne (by simpa using h : some t≠some s)]
      apply funext
      intro ht
      change standardFrozen (F:=F) m o (Sum.inl ⟨t,ht.down⟩) _=0
      rw [PathForestStandardEndpointColumns.odd_row]
      simp [h]

variable (R : Type*) [CommRing R]
def coefficientEquiv : LaurentScalarModel.Coefficients R (NewFrozen (F:=F) o → ℤ) ≃ₐ[R]
    FiniteGroupAlgebraTensor.Product R (Lattice (F:=F) o) :=
  (LaurentScalarModel.coefficientEquiv R (split (F:=F) o)).trans
    (FiniteGroupAlgebraTensor.equiv R (Lattice (F:=F) o))

theorem coefficient_column (s : S) (i : Fin (PathOrientationBlocks.length (m s) (o s))) :
    coefficientEquiv (F:=F) o R
      (ExchangeCharacters.monomial (fun a=>standardFrozen (F:=F) m o a
        ((PathForestOrientation.reindex m o).symm ⟨s,i⟩)))=
    PiTensorProduct.singleAlgHom (some s)
      (ExchangeCharacters.monomial (endpointColumn (F:=F) o m s i)) := by
  change FiniteGroupAlgebraTensor.toProduct R (Lattice (F:=F) o)
    (LaurentScalarModel.coefficientEquiv R (split (F:=F) o) _)=_
  rw [LaurentScalarModel.coefficientEquiv_monomial,column]
  rw [FiniteGroupAlgebraTensor.toProduct_monomial]
  rw [Finset.prod_eq_single (some s)]
  · rw [Pi.single_eq_same]
    congr 1
    exact congrArg (fun d : DecidableEq (Option S)=>
      @PiTensorProduct.singleAlgHom (Option S) R
        (FiniteGroupAlgebraTensor.Factor R (Lattice (F:=F) o)) _ _ _ d (some s))
      (Subsingleton.elim _ _)
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj,ExchangeCharacters.monomial_zero,map_one]
  · simp

#print axioms Unused
#print axioms Lattice
#print axioms latticeGroup
#print axioms latticeModule
#print axioms split
#print axioms endpointColumn
#print axioms column
#print axioms coefficientEquiv
#print axioms coefficient_column
end Verification.PathForestFrozenPartition
