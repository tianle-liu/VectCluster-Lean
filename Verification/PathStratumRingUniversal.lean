/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathLiteralStratumUniversal

/-!
# Path Stratum Ring Universal

Ring-level universal property of the actual path layer, allowing a
change of coefficient algebra such as the frozen parameter of Z.
-/
noncomputable section
namespace Verification.PathStratumRingUniversal
open Verification.PathLiteralStratum Verification.PathPresentation
open Verification.PathCompression Verification.PathClassRepresentatives
variable (R : Type) [CommRing R] {n : ℕ} {I : Finset ℕ} (hI : Admissible n I) (a b : R)

def pathPosition (p : Fin (n+2)) : PathAlgebra n a b :=
  boundary (algebraMap R _ a) (algebraMap R _ b) (x a b) p

def baseMap : PathAlgebra n a b →+* Layer R hI a b :=
  (algebraMap (Closed R hI a b) _).comp (Ideal.Quotient.mk (zeroIdeal R hI a b))

theorem closedPosition_mk (p : Fin (n+2)) : closedPosition R hI a b p =
    Ideal.Quotient.mk (zeroIdeal R hI a b) (pathPosition R a b p) :=
  (boundary_map (Ideal.Quotient.mk (zeroIdeal R hI a b)) _ _ _ p).symm

theorem base_position (p : Fin (n+2)) : baseMap R hI a b (pathPosition R a b p)=position R hI a b p := by
  change algebraMap (Closed R hI a b) _ (Ideal.Quotient.mk _ _) = _
  rw [← closedPosition_mk]
  rfl

variable {T : Type} [CommRing T] (f : PathAlgebra n a b →+* T)
variable (hz : ∀ i : I,f (x a b (mutableIndex hI i))=0)
variable (hu : ∀ p : Vertices n I,IsUnit (f (pathPosition R a b (vertexPosition p))))

def closedLift : Closed R hI a b →+* T := Ideal.Quotient.lift _ f (by
  have hh : zeroIdeal R hI a b ≤ RingHom.ker f := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact hz i
  exact fun z hz=>hh hz)

include hu in
theorem closedLift_units (m : openMonoid R hI a b) : IsUnit (closedLift R hI a b f hz m) := by
  apply SplitExchangeChart.units_on_closure (closedLift R hI a b f hz)
    (fun p : Vertices n I => closedPosition R hI a b (vertexPosition p)) _ m
  intro p
  change IsUnit (closedLift R hI a b f hz (closedPosition R hI a b (vertexPosition p)))
  rw [closedPosition_mk]
  exact hu p

def lift : Layer R hI a b →+* T := IsLocalization.lift (closedLift_units R hI a b f hz hu)

theorem lift_base (z : PathAlgebra n a b) : lift R hI a b f hz hu (baseMap R hI a b z)=f z :=
  IsLocalization.lift_eq (closedLift_units R hI a b f hz hu) _

theorem hom_ext (f g : Layer R hI a b →+* T)
    (heq : f.comp (baseMap R hI a b)=g.comp (baseMap R hI a b)) : f=g := by
  apply IsLocalization.ringHom_ext (openMonoid R hI a b)
  apply Ideal.Quotient.ringHom_ext
  exact heq

#print axioms pathPosition
#print axioms baseMap
#print axioms closedPosition_mk
#print axioms base_position
#print axioms closedLift
#print axioms closedLift_units
#print axioms lift
#print axioms lift_base
#print axioms hom_ext
end Verification.PathStratumRingUniversal
