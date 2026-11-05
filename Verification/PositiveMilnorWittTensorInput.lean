/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Positive Milnor Witt Tensor Input

The ordinary positive Milnor--Witt sheaf tensor formula
K_p^MW tensor_A1 K_q^MW = K_(p+q)^MW, as used in the cited
Morel--Sawant Remark 2.45. It is uniform in both positive degrees and
contains no variety or cellular differential.
-/
noncomputable section
namespace Verification.PositiveMilnorWittTensorInput
open CategoryTheory CategoryTheory.MonoidalCategory
variable {A : Type*} [Category A] [MonoidalCategory A]
variable (M : ℤ → A)

structure Standard where
  positive : ∀ (p q : ℕ),0<p → 0<q → ((M p ⊗ M q) ≅ M ((p+q : ℕ) : ℤ))

variable (H : Standard M)
def squareTwo : (M 2 ⊗ M 2) ≅ M 4 := H.positive 2 2 (by decide) (by decide)

#print axioms Standard
#print axioms squareTwo
end Verification.PositiveMilnorWittTensorInput
