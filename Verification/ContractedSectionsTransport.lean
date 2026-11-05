/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ContractedSectionTheory
import Verification.HomIntegerIso

/-!
# Contracted Sections Transport

Standard contracted sections are transported through an actual
derived object isomorphism by its literal precomposition map.
-/
noncomputable section
namespace Verification.ContractedSectionsTransport
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (J : GrothendieckTopology Scheme.{0})
variable (M : ℤ → C) (N : ℤ → Sheaf J (ModuleCat.{0} ℤ))
variable (T : ContractedSectionTheory.Standard G J M N)
variable (ι τ α : Type) [Fintype ι] [Fintype τ] [Fintype α] (j : ℤ)
variable (D : DerivedCategory C) (e : D ≅ TorusThomInput.thom ℝ ι τ α G)

def evaluateOn :
    ((DerivedCategory.homologyFunctor C (-(Fintype.card ι:ℤ))).obj D ⟶ M j) ≃ₗ[ℤ]
      (N (j-Fintype.card ι)).val.obj (Opposite.op (RealTorusScheme.torus α)) :=
  (HomIntegerIso.precompose ((DerivedCategory.homologyFunctor C (-(Fintype.card ι:ℤ))).mapIso e) (M j)).trans
    (T.evaluate ι τ α j)

#print axioms evaluateOn
end Verification.ContractedSectionsTransport
