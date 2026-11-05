/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOpenNaturality
import Verification.PathTower
import Verification.SplitExchangeChart

/-!
# Path Open Layer

The actual first-coordinate principal open of a path is a smaller
path over a freely invertible new left endpoint. The old left endpoint
is retained only in the eliminated exchange partner.
-/
noncomputable section
namespace Verification.PathOpenLayer
open Verification.PathPresentation Verification.PathRecursion
open Verification.PathOpenInsertion
variable {R : Type*} [CommRing R]
attribute [local instance] MvPolynomial.algebraMvPolynomial

abbrev Laurent (R : Type*) [CommRing R] := Verification.SplitExchangeChart.Laurent R PUnit

def parameter (R : Type*) [CommRing R] : Laurent R :=
  Verification.SplitExchangeChart.laurentVariable R PUnit PUnit.unit

def parameterUnit (R : Type*) [CommRing R] : (Laurent R)ˣ :=
  (Verification.SplitExchangeChart.laurentVariable_unit R PUnit PUnit.unit).unit

theorem parameterUnit_val : (parameterUnit R : Laurent R) = parameter R :=
  (Verification.SplitExchangeChart.laurentVariable_unit R PUnit PUnit.unit).unit_spec

variable (n : ℕ) (a b : R)
abbrev Open := Localization.Away (x (n:=n+1) a b 0)
abbrev Target := PathAlgebra n (parameter R) (algebraMap R (Laurent R) b)

def openX (i : Fin (n+1)) : Open n a b := algebraMap _ _ (x a b i)
def openY (i : Fin (n+1)) : Open n a b := algebraMap _ _ (y a b i)

theorem open_equations : Equations (algebraMap R (Open n a b) a)
    (algebraMap R (Open n a b) b) (openX n a b) (openY n a b) :=
  equations_map (algebraMap _ _) _ _ _ _ (equations (n+1) a b)

theorem open_first_unit : IsUnit (openX n a b 0) :=
  IsLocalization.Away.algebraMap_isUnit (x (n:=n+1) a b 0)

def openUnit : (Open n a b)ˣ := (open_first_unit n a b).unit

def targetUnit : (Target n b)ˣ :=
  Units.map (algebraMap (Laurent R) (Target n b)).toMonoidHom (parameterUnit R)

def targetX (i : Fin n) : Target n b := x (parameter R) (algebraMap R (Laurent R) b) i

def targetY (i : Fin n) : Target n b := y (parameter R) (algebraMap R (Laurent R) b) i

theorem target_equations : Equations (targetUnit n b : Target n b)
    (algebraMap R (Target n b) b) (targetX n b) (targetY n b) := by
  have hu : (targetUnit n b : Target n b) = algebraMap (Laurent R) (Target n b) (parameter R) := by
    change algebraMap (Laurent R) (Target n b) (parameterUnit R : Laurent R) = _
    rw [parameterUnit_val]
  rw [hu]
  exact equations n (parameter R) (algebraMap R (Laurent R) b)

def forwardPath : PathAlgebra (n+1) a b →ₐ[R] Target n b :=
  lift a b (insertX (targetUnit n b) (targetX n b))
    (insertY (algebraMap R (Target n b) a) (algebraMap R (Target n b) b)
      (targetUnit n b) (targetX n b) (targetY n b))
    (inserted_equations _ _ _ _ _ (target_equations n b))

theorem forwardPath_units (m : Submonoid.powers (x (n:=n+1) a b 0)) :
    IsUnit (forwardPath n a b m) := by
  rcases m with ⟨m,⟨k,rfl⟩⟩
  rw [map_pow]
  have h : forwardPath n a b (x a b 0) = (targetUnit n b : Target n b) :=
    lift_x _ _ _ _ _ 0
  rw [h]
  exact (targetUnit n b).isUnit.pow k

def forward : Open n a b →ₐ[R] Target n b := IsLocalization.liftAlgHom (forwardPath_units n a b)

@[simp] theorem forward_x (i : Fin (n+1)) :
    forward n a b (openX n a b i) = insertX (targetUnit n b) (targetX n b) i := by
  change IsLocalization.lift (forwardPath_units n a b) (algebraMap _ _ (x a b i)) = _
  rw [IsLocalization.lift_eq]
  exact lift_x _ _ _ _ _ i

@[simp] theorem forward_y (i : Fin (n+1)) :
    forward n a b (openY n a b i) =
      insertY (algebraMap R (Target n b) a) (algebraMap R (Target n b) b)
        (targetUnit n b) (targetX n b) (targetY n b) i := by
  change IsLocalization.lift (forwardPath_units n a b) (algebraMap _ _ (y a b i)) = _
  rw [IsLocalization.lift_eq]
  exact lift_y _ _ _ _ _ i

def coefficientPolynomial : MvPolynomial PUnit R →ₐ[R] Open n a b :=
  MvPolynomial.aeval (fun _ => openX n a b 0)

theorem coefficientPolynomial_units (m : Verification.SplitExchangeChart.variableMonoid R PUnit) :
    IsUnit (coefficientPolynomial n a b m) := by
  apply Verification.SplitExchangeChart.units_on_closure (coefficientPolynomial n a b).toRingHom
    MvPolynomial.X _ m
  intro i
  change IsUnit (MvPolynomial.aeval (fun _ : PUnit => openX n a b 0) (MvPolynomial.X i))
  rw [MvPolynomial.aeval_X]
  exact open_first_unit n a b

def backCoefficient : Laurent R →ₐ[R] Open n a b :=
  IsLocalization.liftAlgHom (coefficientPolynomial_units n a b)

@[simp] theorem backCoefficient_parameter : backCoefficient n a b (parameter R) = openX n a b 0 := by
  change IsLocalization.lift (coefficientPolynomial_units n a b)
    (algebraMap (MvPolynomial PUnit R) _ (MvPolynomial.X PUnit.unit)) = _
  rw [IsLocalization.lift_eq]
  exact MvPolynomial.aeval_X _ _

def back : Target n b →ₐ[R] Open n a b :=
  Verification.PathTower.liftTower (backCoefficient n a b) (parameter R) (algebraMap R (Laurent R) b)
    (Fin.tail (openX n a b)) (Fin.tail (openY n a b)) (by
      rw [backCoefficient_parameter, AlgHom.commutes]
      exact equations_tail _ _ _ _ (open_equations n a b))

@[simp] theorem back_x (i : Fin n) : back n a b (targetX n b i) = openX n a b i.succ :=
  Verification.PathTower.liftTower_x _ _ _ _ _ _ i

@[simp] theorem back_y (i : Fin n) : back n a b (targetY n b i) = openY n a b i.succ :=
  Verification.PathTower.liftTower_y _ _ _ _ _ _ i

@[simp] theorem back_coefficient (c : Laurent R) :
    back n a b (algebraMap (Laurent R) (Target n b) c) = backCoefficient n a b c :=
  Verification.PathTower.liftTower_coefficient _ _ _ _ _ _ c

theorem back_targetUnit : back n a b (targetUnit n b : Target n b) = openX n a b 0 := by
  change back n a b (algebraMap (Laurent R) (Target n b) (parameterUnit R : Laurent R)) = _
  rw [parameterUnit_val, back_coefficient, backCoefficient_parameter]

theorem back_inverse_targetUnit :
    back n a b (((targetUnit n b)⁻¹ : (Target n b)ˣ) : Target n b) =
      (((openUnit n a b)⁻¹ : (Open n a b)ˣ) : Open n a b) := by
  have hu : Units.map (back n a b).toRingHom.toMonoidHom (targetUnit n b) = openUnit n a b := by
    apply Units.ext
    change back n a b (targetUnit n b : Target n b) = (openUnit n a b : Open n a b)
    rw [back_targetUnit]
    exact (open_first_unit n a b).unit_spec.symm
  have hh := congrArg (fun u : (Open n a b)ˣ => ((u⁻¹ : (Open n a b)ˣ) : Open n a b)) hu
  exact hh

theorem forward_backCoefficient :
    (forward n a b).comp (backCoefficient n a b) =
      IsScalarTower.toAlgHom R (Laurent R) (Target n b) := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Verification.SplitExchangeChart.variableMonoid R PUnit)
  apply MvPolynomial.ringHom_ext
  · intro r
    change forward n a b (backCoefficient n a b (algebraMap R (Laurent R) r)) =
      algebraMap R (Target n b) r
    rw [AlgHom.commutes, AlgHom.commutes]
  · intro i
    cases i
    change forward n a b (backCoefficient n a b (parameter R)) =
      algebraMap (Laurent R) (Target n b) (parameter R)
    rw [backCoefficient_parameter, forward_x]
    change algebraMap (Laurent R) (Target n b) (parameterUnit R : Laurent R) = _
    rw [parameterUnit_val]

theorem forward_back : (forward n a b).comp (back n a b) = AlgHom.id R _ := by
  apply Verification.PathTower.hom_ext
  · intro c
    change forward n a b (back n a b (algebraMap (Laurent R) (Target n b) c)) = _
    rw [back_coefficient]
    exact AlgHom.congr_fun (forward_backCoefficient n a b) c
  · intro i
    change forward n a b (back n a b (targetX n b i)) = targetX n b i
    rw [back_x, forward_x]
    rfl
  · intro i
    change forward n a b (back n a b (targetY n b i)) = targetY n b i
    rw [back_y, forward_y]
    rfl

theorem back_forward_y_first :
    back n a b (insertY (algebraMap R (Target n b) a) (algebraMap R (Target n b) b)
      (targetUnit n b) (targetX n b) (targetY n b) 0) = openY n a b 0 := by
  have hu : Units.map (back n a b).toRingHom.toMonoidHom (targetUnit n b) = openUnit n a b := by
    apply Units.ext
    change back n a b (targetUnit n b : Target n b) = (openUnit n a b : Open n a b)
    rw [back_targetUnit]
    exact (open_first_unit n a b).unit_spec.symm
  have hx : (fun i => back n a b (targetX n b i)) = Fin.tail (openX n a b) := by
    funext i
    exact back_x n a b i
  have hy : (fun i => back n a b (targetY n b i)) = Fin.tail (openY n a b) := by
    funext i
    exact back_y n a b i
  have hm := Verification.PathOpenNaturality.map_insertY (back n a b).toRingHom
    (algebraMap R (Target n b) a) (algebraMap R (Target n b) b)
    (targetUnit n b) (targetX n b) (targetY n b) 0
  change back n a b (insertY _ _ _ _ _ 0) =
    insertY (back n a b (algebraMap R (Target n b) a))
      (back n a b (algebraMap R (Target n b) b))
      (Units.map (back n a b).toRingHom.toMonoidHom (targetUnit n b))
      (fun i => back n a b (targetX n b i)) (fun i => back n a b (targetY n b i)) 0 at hm
  rw [(back n a b).commutes, (back n a b).commutes, hu, hx, hy] at hm
  refine hm.trans ?_
  change ((openUnit n a b)⁻¹ : (Open n a b)ˣ) *
    (algebraMap R (Open n a b) a + boundary (openUnit n a b : Open n a b)
      (algebraMap R (Open n a b) b) (Fin.tail (openX n a b)) 1) = _
  exact (removed_partner (algebraMap R (Open n a b) a) (algebraMap R (Open n a b) b)
    (openUnit n a b) _ _ (open_equations n a b) (open_first_unit n a b).unit_spec.symm).symm

theorem back_forward : (back n a b).comp (forward n a b) = AlgHom.id R _ := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (x (n:=n+1) a b 0))
  have hh : ((back n a b).comp (forward n a b)).comp
      (IsScalarTower.toAlgHom R (PathAlgebra (n+1) a b) (Open n a b)) =
      IsScalarTower.toAlgHom R (PathAlgebra (n+1) a b) (Open n a b) := by
    apply Verification.PathPresentation.hom_ext
    · intro i
      change back n a b (forward n a b (openX n a b i)) = openX n a b i
      rw [forward_x]
      induction i using Fin.cases with
      | zero => exact back_targetUnit n a b
      | succ i => exact back_x n a b i
    · intro i
      change back n a b (forward n a b (openY n a b i)) = openY n a b i
      rw [forward_y]
      induction i using Fin.cases with
      | zero => exact back_forward_y_first n a b
      | succ i => exact back_y n a b i
  exact congrArg AlgHom.toRingHom hh

def openEquiv : Open n a b ≃ₐ[R] Target n b :=
  AlgEquiv.ofAlgHom (forward n a b) (back n a b) (forward_back n a b) (back_forward n a b)

@[simp] theorem openEquiv_first :
    openEquiv n a b (openX n a b 0) = algebraMap (Laurent R) (Target n b) (parameter R) := by
  change forward n a b (openX n a b 0) = _
  rw [forward_x]
  change algebraMap (Laurent R) (Target n b) (parameterUnit R : Laurent R) = _
  rw [parameterUnit_val]

@[simp] theorem openEquiv_x (i : Fin n) : openEquiv n a b (openX n a b i.succ) = targetX n b i :=
  forward_x n a b i.succ

@[simp] theorem openEquiv_y (i : Fin n) : openEquiv n a b (openY n a b i.succ) = targetY n b i :=
  forward_y n a b i.succ

#print axioms Laurent
#print axioms parameter
#print axioms parameterUnit
#print axioms parameterUnit_val
#print axioms Open
#print axioms Target
#print axioms openX
#print axioms openY
#print axioms open_equations
#print axioms open_first_unit
#print axioms openUnit
#print axioms targetUnit
#print axioms targetX
#print axioms targetY
#print axioms target_equations
#print axioms forwardPath
#print axioms forwardPath_units
#print axioms forward
#print axioms forward_x
#print axioms forward_y
#print axioms coefficientPolynomial
#print axioms coefficientPolynomial_units
#print axioms backCoefficient
#print axioms backCoefficient_parameter
#print axioms back
#print axioms back_x
#print axioms back_y
#print axioms back_coefficient
#print axioms back_targetUnit
#print axioms back_inverse_targetUnit
#print axioms forward_backCoefficient
#print axioms forward_back
#print axioms back_forward_y_first
#print axioms back_forward
#print axioms openEquiv
#print axioms openEquiv_first
#print axioms openEquiv_x
#print axioms openEquiv_y
end Verification.PathOpenLayer
