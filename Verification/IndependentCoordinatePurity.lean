/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CoordinatePurityInput
import Verification.IndependentStratumTorus
import Verification.TorusSmooth

/-!
# Independent Coordinate Purity

The actual original coordinate pairs satisfy every hypothesis of the
uniform purity input. Smoothness, regularity, and the conormal basis are
constructed from the independent selected columns and AS.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
namespace Verification.IndependentCoordinatePurity
open CategoryTheory AlgebraicGeometry CochainComplex
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.ExchangeOpenCover Verification.IndependentBasicOpen
open Verification.IndependentOpenCoordinates Verification.GlobalExchangeSmooth
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable (R κ : Type) [CommRing R] [Nontrivial R] [Fintype κ] (n : ℕ)
variable (I : Finset (Fin n)) (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hI : Independent (laterWeights κ n B) I)
variable (hf : Function.Injective (selectedMap κ n B I))
variable (hs : FreezingLattice.Saturated (LinearMap.range (selectedMap κ n B I)))

include hpos hneg hsupport hI hf hs in
omit [Nontrivial R] in
theorem closed_smooth : Algebra.Smooth R (GlobalNormalFrame.ZeroLayer R κ n I B) := by
  letI := TorusSmooth.torus_smooth R (Fin (IndependentStratumTorus.torusRank κ n I B))
  letI : Algebra.Smooth (MonoidAlgebra R (Multiplicative (Fin (IndependentStratumTorus.torusRank κ n I B) →₀ ℤ)))
      (MvPolynomial (Selected n I)
        (MonoidAlgebra R (Multiplicative (Fin (IndependentStratumTorus.torusRank κ n I B) →₀ ℤ)))) := {}
  letI : Algebra.Smooth R (MvPolynomial (Selected n I)
      (MonoidAlgebra R (Multiplicative (Fin (IndependentStratumTorus.torusRank κ n I B) →₀ ℤ)))) :=
    Algebra.Smooth.comp R (MonoidAlgebra R (Multiplicative (Fin (IndependentStratumTorus.torusRank κ n I B) →₀ ℤ))) _
  exact Algebra.Smooth.of_equiv
    (IndependentStratumTorus.affineTorusEquiv R κ n I B hf hs hpos hneg hsupport hI).symm

def frame : CoordinatePurityInput.Frame R (BasicOpen R κ n I B) (Selected n I)
    (selectedCoordinate R κ n I B) := by
  obtain ⟨m,s⟩ := (LinearMap.range (selectedMap κ n B I)).smithNormalForm Finsupp.basisSingleOne
  have he : ∀ i, IsUnit ((s.a i).natAbs : R) := by
    intro i
    simp only [SaturatedSmith.coefficient_natAbs s hs,Nat.cast_one,isUnit_one]
  exact {
    smooth := basicOpen_smooth R κ n B hpos hneg hsupport I hI hf s he
    closedSmooth := closed_smooth R κ n I B hpos hneg hsupport hI hf hs
    regular := GlobalRegularParameters.selected_coordinates_regular R κ n B hpos hneg hsupport I hI hf
    basis := GlobalNormalFrame.conormalBasis R κ n I B hpos hneg hsupport hI hf s he
    basis_generator := GlobalNormalFrame.conormalBasis_apply R κ n I B hpos hneg hsupport hI hf s he }

universe w
variable {C : Type*} [Category C] [Abelian C] [CategoryTheory.Limits.HasBinaryBiproducts C]
  [HasDerivedCategory.{w} C]
variable (G : Scheme ⥤ CochainComplex C ℤ) (P : CoordinatePurityInput.StandardPurity R G)

def comparison : CoordinatePurityInput.relative (BasicOpen R κ n I B) (Selected n I)
    (selectedCoordinate R κ n I B) G ≅
      CoordinatePurityInput.normalThom (BasicOpen R κ n I B) (Selected n I)
        (selectedCoordinate R κ n I B) G :=
  P.comparison _ _ _ (frame R κ n I B hpos hneg hsupport hI hf hs)

#print axioms closed_smooth
#print axioms frame
#print axioms comparison
end Verification.IndependentCoordinatePurity
