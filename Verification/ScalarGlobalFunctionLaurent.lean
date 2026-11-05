/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarLaurentNormalForm
import Verification.LaurentRowCorrection

/-!
# Scalar Global Function Laurent

The original scalar Global algebra in arbitrary mutable labels and the
finite function lattice of frozen exponents. This connects the actual global
presentation to the matrices used by frozen-row normalization.
-/
noncomputable section
namespace Verification.ScalarGlobalFunctionLaurent
open Classical
variable (R F V : Type) [CommRing R] [Fintype F] [Fintype V] (n : ℕ) (e : V ≃ Fin n)
variable (B : Matrix (Fin n ⊕ F) (Fin n ⊕ Empty) ℤ) (a b : Fin n → Rˣ)

def principal : Matrix V V ℤ := fun r i=>B (Sum.inl (e r)) (Sum.inl (e i))
def frozen : Matrix F V ℤ := fun k i=>B (Sum.inr k) (Sum.inl (e i))
def scalar (i : V) : Rˣ := a (e i)*(b (e i))⁻¹

omit [Fintype V] in
theorem exponent_column (i : Fin n) :
    Finsupp.linearEquivFunOnFinite ℤ ℤ F (ScalarLaurentNormalForm.frozenColumn F n B i)=
      fun k=>B (Sum.inr k) (Sum.inl i) := by
  funext k
  simp [ScalarLaurentNormalForm.frozenColumn,ExchangeCharacters.column,Finsupp.single_apply]

def globalEquiv : ScalarFrozenGlobal.Global R F n B a b ≃ₐ[R]
    LaurentScalarModel.Presentation R (principal F V n e B) (LaurentRowCorrection.column (frozen F V n e B))
      (scalar R V n e a b) :=
  (ScalarLaurentNormalForm.globalEquiv R F n B a b).trans
    ((LaurentScalarModel.presentationEquiv R e.symm (Finsupp.linearEquivFunOnFinite ℤ ℤ F)
      (ScalarLaurentNormalForm.principal F n B) (ScalarLaurentNormalForm.frozenColumn F n B)
      (ScalarLaurentNormalForm.ratio R n a b)).trans
      (Ideal.quotientEquivAlgOfEq R (congrArg
        (fun f=>LaurentScalarModel.relations R (principal F V n e B) f (scalar R V n e a b))
          (funext (fun i=>exponent_column F n B (e i))))))

#print axioms principal
#print axioms frozen
#print axioms scalar
#print axioms exponent_column
#print axioms globalEquiv
end Verification.ScalarGlobalFunctionLaurent
