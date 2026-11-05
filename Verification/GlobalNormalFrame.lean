/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GlobalRegularParameters
import Verification.SaturatedSmith
import Verification.SmoothConormal

/-!
# Global Normal Frame

Smooth parameter maps and normal frames on the principal opens of the
fixed global exchange algebra, with their literal original coordinates.
-/
noncomputable section
namespace Verification.GlobalNormalFrame
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.ExchangeOpenCover Verification.IndependentBasicOpen
open Verification.IndependentOpenCoordinates MvPolynomial
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
attribute [local instance] MvPolynomial.algebraMvPolynomial

def parameterMap : MvPolynomial (Selected n I) R →ₐ[R] BasicOpen R κ n I B :=
  aeval (selectedCoordinate R κ n I B)

instance parameterAlgebra : Algebra (MvPolynomial (Selected n I) R) (BasicOpen R κ n I B) :=
  (parameterMap R κ n I B).toRingHom.toAlgebra

instance parameterTower : IsScalarTower R (MvPolynomial (Selected n I) R) (BasicOpen R κ n I B) :=
  IsScalarTower.of_algHom (parameterMap R κ n I B)

theorem parameter_X (i : Selected n I) :
    algebraMap (MvPolynomial (Selected n I) R) (BasicOpen R κ n I B) (X i) =
      selectedCoordinate R κ n I B i := aeval_X _ _

def chartParameterEquiv : BasicOpen R κ n I B ≃ₐ[MvPolynomial (Selected n I) R]
    ActualOpenChart.GlobalOpen R (Selected n I) (Other n I ⊕ κ) (Other n I)
      Sum.inl (matrix κ n I B) :=
  AlgEquiv.ofRingEquiv (f := (chartEquiv R κ n I B).toRingEquiv) (fun p => by
    have h : (chartEquiv R κ n I B).toAlgHom.comp (parameterMap R κ n I B) =
        ActualOpenGeometry.globalParameterMap R (Selected n I) (Other n I ⊕ κ)
          (Other n I) Sum.inl (matrix κ n I B) := by
      apply MvPolynomial.algHom_ext
      intro i
      change chartEquiv R κ n I B (aeval (selectedCoordinate R κ n I B) (X i)) = _
      rw [aeval_X]
      rw [ActualOpenGeometry.globalParameterMap, aeval_X]
      exact chartEquiv_selectedCoordinate R κ n I B i
    exact AlgHom.congr_fun h p)

variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hI : Independent (laterWeights κ n B) I)
variable (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable {m : ℕ} (s : Basis.SmithNormalForm
  (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)) (Other n I ⊕ κ) m)
variable (he : ∀ i, IsUnit ((s.a i).natAbs : R))

include hpos hneg hsupport hI hf s he in
theorem parameters_smooth : Algebra.Smooth (MvPolynomial (Selected n I) R) (BasicOpen R κ n I B) := by
  letI := ActualOpenGeometry.globalOpen_parameters_smooth R (Selected n I) (Other n I ⊕ κ)
    (Other n I) Sum.inl (matrix κ n I B)
    (matrix_zero_block κ n I B hpos hneg hsupport hI) hf s he
  exact Algebra.Smooth.of_equiv (chartParameterEquiv R κ n I B).symm

def zeroIdeal : Ideal (BasicOpen R κ n I B) := ConormalFrame.ideal (selectedCoordinate R κ n I B)
def ZeroLayer := BasicOpen R κ n I B ⧸ zeroIdeal R κ n I B

instance zeroLayerCommRing : CommRing (ZeroLayer R κ n I B) :=
  inferInstanceAs (CommRing (BasicOpen R κ n I B ⧸ zeroIdeal R κ n I B))

instance conormalModule : Module (ZeroLayer R κ n I B) (zeroIdeal R κ n I B).Cotangent :=
  Ideal.cotangentModule _

include hpos hneg hsupport hI hf s he in
theorem exists_directions :
    ∃ f : BasicOpen R κ n I B →+*
        TrivSqZeroExt (ZeroLayer R κ n I B) (Selected n I →₀ ZeroLayer R κ n I B),
      (∀ a, (f a).fst = Ideal.Quotient.mk (zeroIdeal R κ n I B) a) ∧
      ∀ i, f (selectedCoordinate R κ n I B i) = TrivSqZeroExt.inr (Finsupp.single i 1) := by
  letI := parameters_smooth R κ n I B hpos hneg hsupport hI hf s he
  exact SmoothConormal.exists_directions_for R (BasicOpen R κ n I B) (Selected n I)
    (selectedCoordinate R κ n I B) (parameter_X R κ n I B)

def conormalBasis : Basis (Selected n I) (ZeroLayer R κ n I B) (zeroIdeal R κ n I B).Cotangent :=
  ConormalFrame.basis (selectedCoordinate R κ n I B)
    (exists_directions R κ n I B hpos hneg hsupport hI hf s he).choose
    (exists_directions R κ n I B hpos hneg hsupport hI hf s he).choose_spec.1
    (exists_directions R κ n I B hpos hneg hsupport hI hf s he).choose_spec.2

theorem conormalBasis_apply (i : Selected n I) :
    conormalBasis R κ n I B hpos hneg hsupport hI hf s he i =
      ConormalFrame.frame (selectedCoordinate R κ n I B) i := ConormalFrame.basis_apply _ _ _ _ i

def normalBasis : Basis (Selected n I) (ZeroLayer R κ n I B)
    (Module.Dual (ZeroLayer R κ n I B) (zeroIdeal R κ n I B).Cotangent) :=
  (conormalBasis R κ n I B hpos hneg hsupport hI hf s he).dualBasis

theorem normalBasis_coordinateClass (i l : Selected n I) :
    normalBasis R κ n I B hpos hneg hsupport hI hf s he i
      (ConormalFrame.frame (selectedCoordinate R κ n I B) l) = if i = l then 1 else 0 := by
  rw [← conormalBasis_apply R κ n I B hpos hneg hsupport hI hf s he l]
  dsimp only [normalBasis]
  rw [Basis.dualBasis_apply_self]
  simp only [eq_comm]

theorem coordinates_generate (l : List (Selected n I)) (hl : ∀ i, i ∈ l) :
    Ideal.ofList (l.map (selectedCoordinate R κ n I B)) = zeroIdeal R κ n I B := by
  apply congrArg Ideal.span
  ext a
  change (a ∈ l.map (selectedCoordinate R κ n I B)) ↔
    ∃ i, selectedCoordinate R κ n I B i = a
  constructor
  · intro ha
    obtain ⟨i, _, hi⟩ := List.mem_map.mp ha
    exact ⟨i, hi⟩
  · rintro ⟨i, rfl⟩
    exact List.mem_map.mpr ⟨i, hl i, rfl⟩

#print axioms parameterMap
#print axioms parameterAlgebra
#print axioms parameterTower
#print axioms parameter_X
#print axioms chartParameterEquiv
#print axioms parameters_smooth
#print axioms zeroIdeal
#print axioms ZeroLayer
#print axioms zeroLayerCommRing
#print axioms conormalModule
#print axioms exists_directions
#print axioms conormalBasis
#print axioms conormalBasis_apply
#print axioms normalBasis
#print axioms normalBasis_coordinateClass
#print axioms coordinates_generate
end Verification.GlobalNormalFrame
