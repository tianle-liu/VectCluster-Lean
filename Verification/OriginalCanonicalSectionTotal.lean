/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.AffineCoefficientSectionTotal
import Verification.OriginalCanonicalFiberProjection

/-!
# Original Canonical Section Total

Canonical affine-partner-zero projection on every actual stratum,
including the empty zero set, is invertible on total sections. Smoothness
is needed only for its explicitly presented coefficient algebra.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.OriginalCanonicalSectionTotal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.ExchangeOpenCover Verification.IndependentOpenCoordinates
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n,¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n,¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j,earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0)
variable (hI : Independent (laterWeights κ n B) I)
variable (ht : Algebra.Smooth R (ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R (Selected n I) (Other n I ⊕ κ) (Other n I) (matrix κ n I B))))

include hpos hneg hsupport hI ht in
theorem source_smooth : Algebra.Smooth R (GlobalNormalFrame.ZeroLayer R κ n I B) := by
  letI : Algebra.Smooth R (ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R (Selected n I) (Other n I ⊕ κ) (Other n I) (matrix κ n I B))) := ht
  letI : Algebra.Smooth (ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R (Selected n I) (Other n I ⊕ κ) (Other n I) (matrix κ n I B))) (MvPolynomial (Selected n I) (ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R (Selected n I) (Other n I ⊕ κ) (Other n I) (matrix κ n I B)))) := {}
  letI := Algebra.Smooth.comp R (ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R (Selected n I) (Other n I ⊕ κ) (Other n I) (matrix κ n I B))) (MvPolynomial (Selected n I) (ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R (Selected n I) (Other n I ⊕ κ) (Other n I) (matrix κ n I B))))
  exact Algebra.Smooth.of_equiv ((IndependentStratumCoordinates.affineEquiv R κ n I B hpos hneg hsupport hI)).symm

universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
variable [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive]
variable (J : DerivedCategory A ⥤ D) [J.Additive] [J.CommShift ℤ]
variable (L : DerivedCategory C ⥤ D) [L.Additive] [L.CommShift ℤ]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (H : LocalizedAffineThomInvariance.Standard L R G)
variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (hV : LocalizedThomSections.Naturality J L G R site M N V)
variable (W : GradedMilnorWittSheaf.Standard site N)

def equiv : W.Total (CommRingCat.of (GlobalNormalFrame.ZeroLayer R κ n I B)) ≃+* W.Total (CommRingCat.of (ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R (Selected n I) (Other n I ⊕ κ) (Other n I) (matrix κ n I B)))) :=
  AffineCoefficientSectionTotal.totalEquiv J L G R (GlobalNormalFrame.ZeroLayer R κ n I B) (ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R (Selected n I) (Other n I ⊕ κ) (Other n I) (matrix κ n I B))) (Selected n I) (IndependentStratumCoordinates.affineEquiv R κ n I B hpos hneg hsupport hI)
    (source_smooth R κ n I B hpos hneg hsupport hI ht) ht H site M N V hV W

omit [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive] [J.Additive] [J.CommShift ℤ] [L.Additive] [L.CommShift ℤ] [HasShift D ℤ] in
theorem equiv_apply (a : W.Total (CommRingCat.of (GlobalNormalFrame.ZeroLayer R κ n I B))) :
    equiv R κ n I B hpos hneg hsupport hI ht J L G H site M N V hV W a=
      GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of (GlobalNormalFrame.ZeroLayer R κ n I B)) (T:=CommRingCat.of (ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R (Selected n I) (Other n I ⊕ κ) (Other n I) (matrix κ n I B))))
        (OriginalCanonicalFiberProjection.projection R κ n I B hpos hneg hsupport hI).toRingHom a := rfl

omit [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive] [J.Additive] [J.CommShift ℤ] [L.Additive] [L.CommShift ℤ] [HasShift D ℤ] in
theorem inverse_section (s : (ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R (Selected n I) (Other n I ⊕ κ) (Other n I) (matrix κ n I B))) →ₐ[R] (GlobalNormalFrame.ZeroLayer R κ n I B))
    (hp : (OriginalCanonicalFiberProjection.projection R κ n I B hpos hneg hsupport hI).comp s=AlgHom.id R (ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R (Selected n I) (Other n I ⊕ κ) (Other n I) (matrix κ n I B))))
    (a : W.Total (CommRingCat.of (ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R (Selected n I) (Other n I ⊕ κ) (Other n I) (matrix κ n I B))))) :
    (equiv R κ n I B hpos hneg hsupport hI ht J L G H site M N V hV W).symm a=
      GradedMilnorWittSheaf.pullback site N W (S:=CommRingCat.of (ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R (Selected n I) (Other n I ⊕ κ) (Other n I) (matrix κ n I B)))) (T:=CommRingCat.of (GlobalNormalFrame.ZeroLayer R κ n I B)) s.toRingHom a :=
  AffineCoefficientSectionTotal.inverse_section J L G R (GlobalNormalFrame.ZeroLayer R κ n I B) (ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R (Selected n I) (Other n I ⊕ κ) (Other n I) (matrix κ n I B))) (Selected n I) (IndependentStratumCoordinates.affineEquiv R κ n I B hpos hneg hsupport hI)
    (source_smooth R κ n I B hpos hneg hsupport hI ht) ht H site M N V hV W s hp a

#print axioms source_smooth
#print axioms equiv
#print axioms equiv_apply
#print axioms inverse_section
end Verification.OriginalCanonicalSectionTotal
