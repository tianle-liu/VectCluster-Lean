/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathSignedStratumCoordinates

/-!
# Path Signed Stratum Equivalence

Both directions of the canonical signed coordinate chart on every
literal independent path stratum, retaining the original x and y generators.
-/
noncomputable section
namespace Verification.PathSignedStratumEquivalence
open Verification.PathCompression Verification.PathClassRepresentatives
open Verification.PathLiteralStratum Verification.PathSignedStratumCoefficients
open Verification.PathSignedStratumCoordinates Verification.PathPresentation
open Verification.OriginalTorus Verification.FinsuppTorusUniversal MvPolynomial Finset
variable (R : Type) [CommRing R] {n : ℕ} {I : Finset ℕ} (hI : Admissible n I) (a b : R)

def forward : Layer R hI a b →ₐ[R] Target R hI a b :=
  PathLiteralStratumUniversal.lift R hI a b (targetX R hI a b) (targetY R hI a b)
    (target_equations R hI a b) (target_zero R hI a b) (target_units R hI a b)

theorem forward_x (i : Fin n) : forward R hI a b (layerX R hI a b i)=targetX R hI a b i :=
  PathLiteralStratumUniversal.lift_x R hI a b _ _ _ _ _ i

theorem forward_y (i : Fin n) : forward R hI a b (layerY R hI a b i)=targetY R hI a b i :=
  PathLiteralStratumUniversal.lift_y R hI a b _ _ _ _ _ i

theorem forward_position (p : Fin (n+2)) : forward R hI a b (position R hI a b p)=
    C (PathSignedStratumCoordinates.coordinate R hI a b p) :=
  (PathLiteralStratumUniversal.lift_position R hI a b _ _ _ _ _ p).trans (target_boundary R hI a b p)

def backward : Target R hI a b →ₐ[R] Layer R hI a b :=
  MvPolynomial.aevalTower (toLayer R hI a b) (fun i : I => layerY R hI a b (mutableIndex hI i))

theorem backward_C (c : Coefficients R hI a b) : backward R hI a b (C c)=toLayer R hI a b c :=
  MvPolynomial.aevalTower_C _ _ c

theorem backward_X (i : I) : backward R hI a b (X i)=layerY R hI a b (mutableIndex hI i) :=
  MvPolynomial.aevalTower_X _ _ i

theorem position_zero (p : Fin (n+2)) (hp : p.val ∈ I) : position R hI a b p=0 := by
  let i : I := ⟨p.val,hp⟩
  have he : p=(mutableIndex hI i).castSucc.succ := by
    apply Fin.ext
    exact (mutable_position hI i).symm
  rw [he,position_middle,layer_zero]

theorem backward_coordinate (p : Fin (n+2)) :
    backward R hI a b (C (PathSignedStratumCoordinates.coordinate R hI a b p))=position R hI a b p := by
  rw [backward_C,PathSignedStratumCoordinates.coordinate]
  split_ifs with hp
  · rw [map_zero,position_zero R hI a b p hp]
  · rw [toLayer_unsigned]
    rfl

theorem backward_x (i : Fin n) : backward R hI a b (targetX R hI a b i)=layerX R hI a b i := by
  rw [targetX,backward_coordinate,position_middle]

theorem backward_y (i : Fin n) : backward R hI a b (targetY R hI a b i)=layerY R hI a b i := by
  by_cases hi : i.val+1 ∈ I
  · let j : I := ⟨i.val+1,hi⟩
    have hj : mutableIndex hI j=i := by apply Fin.ext;dsimp [mutableIndex,j]
    rw [← hj,target_selected_partner,backward_X]
  · have hu : IsUnit (layerX R hI a b i) := by
      have hh := coordinate_isUnit R hI a b (nonzeroVertex i hi)
      change IsUnit (position R hI a b i.castSucc.succ) at hh
      rw [position_middle] at hh
      exact hh
    apply hu.mul_left_cancel
    have he := congrArg (backward R hI a b) (target_equations R hI a b i)
    change backward R hI a b (_*_)=backward R hI a b (_+_) at he
    rw [map_mul,map_add,backward_x,target_boundary,target_boundary,
      backward_coordinate,backward_coordinate,position_boundary,position_boundary] at he
    exact he.trans (layer_equations R hI a b i).symm

theorem backward_forward : (backward R hI a b).comp (forward R hI a b)=AlgHom.id R _ := by
  apply PathLiteralStratumUniversal.hom_ext R hI a b
  · intro i
    change backward R hI a b (forward R hI a b (layerX R hI a b i))=_
    rw [forward_x,backward_x,AlgHom.id_apply]
  · intro i
    change backward R hI a b (forward R hI a b (layerY R hI a b i))=_
    rw [forward_y,backward_y,AlgHom.id_apply]

theorem forward_signed (p : Vertices n I) :
    forward R hI a b (signedUnit R hI a b p : Layer R hI a b)=
      C (signedCoordinate R hI a b p : Coefficients R hI a b) := by
  rw [signedUnit_val,map_mul,map_pow,map_neg,map_one,forward_position,coordinate_vertex]
  change (-1:Target R hI a b)^(p.val/2)*
    C ((-1:Coefficients R hI a b)^(p.val/2)*(signedCoordinate R hI a b p : Coefficients R hI a b))=_
  rw [map_mul,map_pow,map_neg,map_one,← mul_assoc,sign_square,one_mul]

theorem forward_coefficients : (forward R hI a b).comp (toLayer R hI a b)=
    IsScalarTower.toAlgHom R (Coefficients R hI a b) (Target R hI a b) := by
  apply Ideal.Quotient.algHom_ext
  apply FinsuppTorusUniversal.hom_ext
  intro p
  change forward R hI a b (toLayerTorus R hI a b (torusCoordinate R _ p))=
    C (Ideal.Quotient.mk (endpointIdeal R hI a b) (torusCoordinate R _ p))
  rw [toLayerTorus,lift_coordinate,forward_signed]
  change C (Ideal.Quotient.mk (endpointIdeal R hI a b) (torusCoordinate R _ (compress hI (includeRepresentative p))))=_
  rw [compress_include]

theorem forward_backward : (forward R hI a b).comp (backward R hI a b)=AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext'
  · apply AlgHom.ext
    intro c
    change forward R hI a b (backward R hI a b (C c))=C c
    rw [backward_C]
    exact AlgHom.congr_fun (forward_coefficients R hI a b) c
  · intro i
    change forward R hI a b (backward R hI a b (X i))=X i
    rw [backward_X,forward_y,target_selected_partner]

def stratumEquiv : Layer R hI a b ≃ₐ[R] Target R hI a b :=
  AlgEquiv.ofAlgHom (forward R hI a b) (backward R hI a b)
    (forward_backward R hI a b) (backward_forward R hI a b)

theorem stratumEquiv_position (p : Fin (n+2)) :
    stratumEquiv R hI a b (position R hI a b p)=C (PathSignedStratumCoordinates.coordinate R hI a b p) :=
  forward_position R hI a b p

theorem stratumEquiv_partner (i : I) :
    stratumEquiv R hI a b (layerY R hI a b (mutableIndex hI i))=X i :=
  (forward_y R hI a b _).trans (target_selected_partner R hI a b i)

theorem stratumEquiv_signed (p : Vertices n I) :
    stratumEquiv R hI a b (signedUnit R hI a b p : Layer R hI a b)=
      C (signedCoordinate R hI a b p : Coefficients R hI a b) := forward_signed R hI a b p

#print axioms forward
#print axioms forward_x
#print axioms forward_y
#print axioms forward_position
#print axioms backward
#print axioms backward_C
#print axioms backward_X
#print axioms position_zero
#print axioms backward_coordinate
#print axioms backward_x
#print axioms backward_y
#print axioms backward_forward
#print axioms forward_signed
#print axioms forward_coefficients
#print axioms forward_backward
#print axioms stratumEquiv
#print axioms stratumEquiv_position
#print axioms stratumEquiv_partner
#print axioms stratumEquiv_signed
end Verification.PathSignedStratumEquivalence
