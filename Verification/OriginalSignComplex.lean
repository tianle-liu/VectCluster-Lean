/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.AcyclicOrderedFamily
import Verification.FrozenSignCoefficients
import Verification.IndependentFamilyBound
import Mathlib.Data.Sum.Order

/-!
# Original Sign Complex

The original finite mutable/frozen labels and literal sign differential,
with a row order that extends the given mutable order by construction.
-/
noncomputable section
namespace Verification.OriginalSignComplex
open CategoryTheory ExchangeReindex
variable {V C : Type} [Fintype V] [Fintype C] [LinearOrder V] [LinearOrder C]

def rowOrder : LinearOrder (V ⊕ C) := inferInstanceAs (LinearOrder (V ⊕ₗ C))
local instance : LinearOrder (V ⊕ C) := rowOrder

omit [Fintype V] [Fintype C] in
theorem order_compatible (i j : V) :
    @LT.lt (V ⊕ C) (rowOrder (V := V) (C := C)).toLT (Sum.inl i) (Sum.inl j) ↔ i<j :=
  Sum.Lex.inl_lt_inl_iff

variable (B : (V ⊕ C) → V → ℤ)

omit [Fintype V] [Fintype C] [LinearOrder V] [LinearOrder C] in
theorem indep (I : Finset V) (hI : PrincipalIndependent B I)
    (i : V) (hi : i∈I) (j : V) (hj : j∈I) (hne : i≠j) : B (Sum.inl j) i=0 :=
  hI j hj i hi hne.symm

def complex (A : Type) [AddCommGroup A] : CochainComplex (ModuleCat ℤ) ℕ :=
  FrozenSignCoefficients.complex (A := A) B (PrincipalIndependent B)
    (AcyclicOrderedFamily.down B) (indep B)

def alpha : ℕ := IndependentFamilyBound.maximum (PrincipalIndependent B)

omit [Fintype C] [LinearOrder V] [LinearOrder C] in
theorem card_le_alpha (I : Finset V) (hI : PrincipalIndependent B I) : I.card≤alpha B :=
  IndependentFamilyBound.card_le (PrincipalIndependent B) I hI

#print axioms rowOrder
#print axioms order_compatible
#print axioms indep
#print axioms complex
#print axioms alpha
#print axioms card_le_alpha
end Verification.OriginalSignComplex
