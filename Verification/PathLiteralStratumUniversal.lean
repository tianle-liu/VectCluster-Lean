/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathLiteralStratum

/-!
# Path Literal Stratum Universal

The universal property and generator extensionality of the actual
localized zero stratum of the nearest-neighbor path algebra.
-/
noncomputable section
namespace Verification.PathLiteralStratumUniversal
open Verification.PathLiteralStratum Verification.PathPresentation
open Verification.PathCompression Verification.PathClassRepresentatives
variable (R : Type) [CommRing R] {n : ℕ} {I : Finset ℕ} (hI : Admissible n I) (a b : R)
variable {T : Type} [CommRing T] [Algebra R T]
variable (xx yy : Fin n → T)
variable (he : Equations (algebraMap R T a) (algebraMap R T b) xx yy)
variable (hz : ∀ i : I, xx (mutableIndex hI i)=0)

def liftClosed : Closed R hI a b →ₐ[R] T :=
  Ideal.Quotient.liftₐ (zeroIdeal R hI a b) (PathPresentation.lift a b xx yy he) (by
    change zeroIdeal R hI a b ≤ RingHom.ker (PathPresentation.lift a b xx yy he).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change PathPresentation.lift a b xx yy he (x a b (mutableIndex hI i))=0
    rw [lift_x,hz])

theorem liftClosed_x (i : Fin n) : liftClosed R hI a b xx yy he hz (closedX R hI a b i)=xx i :=
  lift_x a b xx yy he i

theorem liftClosed_y (i : Fin n) : liftClosed R hI a b xx yy he hz (closedY R hI a b i)=yy i :=
  lift_y a b xx yy he i

theorem liftClosed_position (p : Fin (n+2)) : liftClosed R hI a b xx yy he hz (closedPosition R hI a b p)=
    boundary (algebraMap R T a) (algebraMap R T b) xx p := by
  rw [closedPosition,boundary_map (liftClosed R hI a b xx yy he hz),AlgHom.commutes,AlgHom.commutes]
  simp only [liftClosed_x]

variable (hu : ∀ p : Vertices n I, IsUnit (boundary (algebraMap R T a) (algebraMap R T b) xx (vertexPosition p)))

include hu in
theorem liftClosed_units (m : openMonoid R hI a b) : IsUnit (liftClosed R hI a b xx yy he hz m) := by
  apply SplitExchangeChart.units_on_closure (liftClosed R hI a b xx yy he hz).toRingHom
    (fun p : Vertices n I => closedPosition R hI a b (vertexPosition p)) _ m
  intro p
  change IsUnit (liftClosed R hI a b xx yy he hz (closedPosition R hI a b (vertexPosition p)))
  rw [liftClosed_position]
  exact hu p

def lift : Layer R hI a b →ₐ[R] T := IsLocalization.liftAlgHom (liftClosed_units R hI a b xx yy he hz hu)

theorem lift_x (i : Fin n) : lift R hI a b xx yy he hz hu (layerX R hI a b i)=xx i := by
  change IsLocalization.lift (liftClosed_units R hI a b xx yy he hz hu)
    (algebraMap (Closed R hI a b) _ (closedX R hI a b i))=_
  rw [IsLocalization.lift_eq]
  exact liftClosed_x R hI a b xx yy he hz i

theorem lift_y (i : Fin n) : lift R hI a b xx yy he hz hu (layerY R hI a b i)=yy i := by
  change IsLocalization.lift (liftClosed_units R hI a b xx yy he hz hu)
    (algebraMap (Closed R hI a b) _ (closedY R hI a b i))=_
  rw [IsLocalization.lift_eq]
  exact liftClosed_y R hI a b xx yy he hz i

theorem lift_position (p : Fin (n+2)) : lift R hI a b xx yy he hz hu (position R hI a b p)=
    boundary (algebraMap R T a) (algebraMap R T b) xx p := by
  change IsLocalization.lift (liftClosed_units R hI a b xx yy he hz hu)
    (algebraMap (Closed R hI a b) _ (closedPosition R hI a b p))=_
  rw [IsLocalization.lift_eq]
  exact liftClosed_position R hI a b xx yy he hz p

theorem hom_ext (f g : Layer R hI a b →ₐ[R] T)
    (hx : ∀ i, f (layerX R hI a b i)=g (layerX R hI a b i))
    (hy : ∀ i, f (layerY R hI a b i)=g (layerY R hI a b i)) : f=g := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (openMonoid R hI a b)
  have heq : f.comp (IsScalarTower.toAlgHom R (Closed R hI a b) (Layer R hI a b))=
      g.comp (IsScalarTower.toAlgHom R (Closed R hI a b) (Layer R hI a b)) := by
    apply Ideal.Quotient.algHom_ext
    apply PathPresentation.hom_ext
    · exact hx
    · exact hy
  exact congrArg AlgHom.toRingHom heq

#print axioms liftClosed
#print axioms liftClosed_x
#print axioms liftClosed_y
#print axioms liftClosed_position
#print axioms liftClosed_units
#print axioms lift
#print axioms lift_x
#print axioms lift_y
#print axioms lift_position
#print axioms hom_ext
end Verification.PathLiteralStratumUniversal
