/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.TorusThomInput
import Verification.RealSheafSignature

/-!
# Contracted Section Theory

Standard Thom representability and contraction on actual sheaf
sections. C is the chosen strict coefficient category, distinct from the
category of all Nisnevich sheaves. The left side uses the literal normal-
pair derived cone; the right side is an actual sheaf evaluation. No exchange
filtration, global comparison, lattice or differential is an input.
-/
noncomputable section
namespace Verification.ContractedSectionTheory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (J : GrothendieckTopology Scheme.{0})
variable (M : ℤ → C) (N : ℤ → Sheaf J (ModuleCat.{0} ℤ))

structure Standard where
  evaluate : ∀ (ι τ α : Type) [Fintype ι] [Fintype τ] [Fintype α] (j : ℤ),
    ((DerivedCategory.homologyFunctor C (-(Fintype.card ι:ℤ))).obj
      (TorusThomInput.thom ℝ ι τ α G) ⟶ M j) ≃ₗ[ℤ]
        (N (j-Fintype.card ι)).val.obj (Opposite.op (RealTorusScheme.torus α))

#print axioms Standard
end Verification.ContractedSectionTheory
