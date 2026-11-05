/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarOpenFreezing
import Verification.ScalarLaurentNormalForm
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

/-!
# Scalar Initial Torus

Inverting all mutable originals in the actual frozen scalar ring
gives a literal Laurent ring. All mutated partners are eliminated by
unit-coefficient exchange equations.
-/
noncomputable section
namespace Verification.ScalarInitialTorus
open Verification.IndependentChartIndex Verification.ScalarFrozenGlobal
open Verification.ScalarOpenFreezing Verification.ScalarIndependentBasicOpen
variable (R κ : Type) [CommRing R] [Fintype κ]

omit [Fintype κ] in
theorem empty_relations (P : Fin 0 → Fin 0 → ℤ) (f : Fin 0 → (κ →₀ ℤ)) (c : Fin 0 → Rˣ) :
    LaurentScalarModel.relations R P f c = ⊥ := by
  simp [LaurentScalarModel.relations,PartnerScaling.relations,Set.range_eq_empty]

def emptyModelEquiv (P : Fin 0 → Fin 0 → ℤ) (f : Fin 0 → (κ →₀ ℤ)) (c : Fin 0 → Rˣ) :
    LaurentScalarModel.Presentation R P f c ≃ₐ[R] OriginalTorus.Torus R κ :=
  (Ideal.quotientEquivAlgOfEq R (empty_relations R κ P f c)).trans
    ((AlgEquiv.quotientBot R _).trans
      (((MvPolynomial.isEmptyAlgEquiv (MvPolynomial (Fin 0) (OriginalTorus.Torus R κ)) (Fin 0)).restrictScalars R).trans
        ((MvPolynomial.isEmptyAlgEquiv (OriginalTorus.Torus R κ) (Fin 0)).restrictScalars R)))

def emptyGlobalEquiv (B : (Fin 0 ⊕ κ) → (Fin 0 ⊕ Empty) → ℤ) (a b : Fin 0 → Rˣ) :
    Global R κ 0 B a b ≃ₐ[R] OriginalTorus.Torus R κ :=
  (ScalarLaurentNormalForm.globalEquiv R κ 0 B a b).trans
    (emptyModelEquiv R κ (ScalarLaurentNormalForm.principal κ 0 B)
      (ScalarLaurentNormalForm.frozenColumn κ 0 B) (ScalarLaurentNormalForm.ratio R 0 a b))

variable (n : ℕ) (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (a b : Fin n → Rˣ)

def emptySelectedEquiv : Selected n ∅ ≃ Fin 0 := by
  letI : IsEmpty (Selected n ∅) := ⟨fun i => Finset.not_mem_empty i.val i.property⟩
  exact Equiv.equivOfIsEmpty _ _

def initialTorusEquiv : BasicOpen R κ n ∅ B a b ≃ₐ[R]
    OriginalTorus.Torus R (Other n ∅ ⊕ κ) :=
  (chartFreezingEquiv R κ n ∅ B a b 0 (emptySelectedEquiv n)).trans
    (emptyGlobalEquiv R (Other n ∅ ⊕ κ) (frozenMatrix κ n ∅ B 0 (emptySelectedEquiv n))
      (frozenScalar R n ∅ 0 (emptySelectedEquiv n) a)
      (frozenScalar R n ∅ 0 (emptySelectedEquiv n) b))

theorem initialTorus_domain [IsDomain R] : IsDomain (BasicOpen R κ n ∅ B a b) :=
  Function.Injective.isDomain (initialTorusEquiv R κ n B a b).toRingHom
    (initialTorusEquiv R κ n B a b).injective

#print axioms empty_relations
#print axioms emptyModelEquiv
#print axioms emptyGlobalEquiv
#print axioms emptySelectedEquiv
#print axioms initialTorusEquiv
#print axioms initialTorus_domain
end Verification.ScalarInitialTorus
