/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GradedScalarDegreeTransport
import Verification.GradedRealizationComponents

/-!
# Path Strict Realization Entry

The positive formal path action is literally the actual MW scalar
morphism after all successor-weight casts have been removed.
-/
noncomputable section
namespace Verification.PathStrictRealizationEntry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.PathGradedCoefficientAction
open Verification.GradedMilnorWittDegreeSpaces
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) [L.Additive]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (R : Type) [CommRing R]
variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (W : GradedMilnorWittSheaf.Standard site N)
variable (P : GradedMilnorWittHomogeneity.Standard site N W)
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (H : GradedMilnorWittStrictScalars.Standard J L G R site M N W P V)

attribute [local instance] Abelian.hasFiniteBiproducts
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {w : ι → ℕ} {v : κ → ℕ} {d : ι → ℤ}
variable (T : PositiveGradedContraction.Data w v d)

omit [J.Additive] [L.Additive] in
theorem entry (i j : {i // 0<w i}) :
    GradedRealizationComponents.entry (fun n:ℕ=>M (n:ℤ))
      (PathStrictCoefficientAction.action J L G R site M N W P V H 1) T i j=
    H.scalar (w i.val:ℤ) (w j.val:ℤ)
      ⟨PathMilnorWittCoefficients.realize (W.symbols (CommRingCat.of R)).toCoefficients (T.D j.val i.val),
        PathMilnorWittGradedRealization.homogeneous P (CommRingCat.of R) (T.coefficientD j.val i.val)⟩ := by
  unfold GradedRealizationComponents.entry
  rw [PathStrictCoefficientAction.action_apply]
  exact GradedScalarDegreeTransport.scalar J L G R site M N W P V H _ _ _ _
    (by have h:=i.property;omega) (by have h:=j.property;omega) _ _ rfl
#print axioms entry
end Verification.PathStrictRealizationEntry
