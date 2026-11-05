/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOrderedCoordinateList
import Verification.PathWordEndpointEvaluation
import Verification.MilnorWittSignedConstants
import Verification.PathEndpointComplex

/-!
# Path Ordered Endpoint Evaluation

The actual compressed coefficient symbols factor through the literal
endpoint quotient, including the parity-dependent right rho constant.
-/
noncomputable section
namespace Verification.PathOrderedEndpointEvaluation
open Finset Verification.PathCompression Verification.PathClassRepresentatives
open Verification.PathSignedStratumCoefficients Verification.PathOrderedFaceUnits
open Verification.PathOrderedCoordinateList Verification.PathEndpointOrdering
open Verification.PathClassOrdering Verification.PathMilnorWittWordFace
open Verification.PathMilnorWittCoefficients Verification.MilnorWittSymbolRelations
variable (S : Type) [CommRing S] {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)

theorem left_unit (b : S) : signedCoordinate S hI 1 b (firstVertex hI)=1 := by
  apply Units.ext
  have hh:=signed_endpoint S hI 1 b false
  simpa only [endpoint,endpointValue,Bool.false_eq_true,↓reduceIte,map_one,Units.val_one] using hh

theorem right_unit (a : S) : signedCoordinate S hI a 1 (lastVertex hI)=(-1)^((n+1)/2) := by
  apply Units.ext
  have hh:=signed_endpoint S hI a 1 true
  simpa only [endpoint,endpointValue,↓reduceIte,mul_one,map_pow,map_neg,map_one,
    Units.val_pow_eq_pow_val,Units.val_neg,Units.val_one] using hh

theorem nonempty (a b : S) : units S hI a b≠[] := by
  have hp : 0<(available I (n+2)).card := Finset.card_pos.mpr ⟨0,zero_available hI (by omega)⟩
  intro he
  have hh:=length_units S hI a b
  rw [he,List.length_nil] at hh
  omega

theorem right_list (a b : S) :
    (units S hI a b).take ((units S hI a b).length-1) ++
      [signedCoordinate S hI a b (lastVertex hI)]=units S hI a b := by
  have hi:=at_index S hI a b (compress hI (lastVertex hI))
  have hl:=last_index hI
  have he : (index (compress hI (lastVertex hI))).val=(units S hI a b).length-1 := by
    rw [length_units]
    omega
  have hc : signedCoordinate S hI a b (includeRepresentative (compress hI (lastVertex hI)))=
      signedCoordinate S hI a b (lastVertex hI) := by
    unfold signedCoordinate
    rw [compress_include]
  simp only [he,hc] at hi
  have ht := List.take_append_getLast (units S hI a b) (nonempty S hI a b)
  rw [List.getLast_eq_getElem,hi] at ht
  exact ht

theorem left_list (a b : S) :
    units S hI a b=signedCoordinate S hI a b (firstVertex hI)::(units S hI a b).drop 1 := by
  have hi:=at_index S hI a b (compress hI (firstVertex hI))
  have hc : signedCoordinate S hI a b (includeRepresentative (compress hI (firstVertex hI)))=
      signedCoordinate S hI a b (firstVertex hI) := by
    unfold signedCoordinate
    rw [compress_include]
  simp only [first_index,hc] at hi
  have hp : 0<(units S hI a b).length := List.length_pos_iff.mpr (nonempty S hI a b)
  have ht := List.drop_eq_getElem_cons hp
  simpa only [List.drop_zero,Nat.zero_add,hi] using ht

variable {B : Type*} [Ring B]
local notation "C" => Verification.PathCoefficientRing.Coeff

theorem right_symbol (a : S) (D : Symbols (Coefficients S hI a 1) B) :
    D.symbol (signedCoordinate S hI a 1 (lastVertex hI))=
      realize D.toCoefficients (Verification.PathEndpointComplex.endpointConstant Verification.PathCoefficientRing.rho n) := by
  rw [right_unit,Verification.MilnorWittSignedConstants.signed_power]
  unfold Verification.PathEndpointComplex.endpointConstant
  split_ifs <;> simp only [map_zero,realize_rho]

theorem right_projection (a : S) (D : Symbols (Coefficients S hI a 1) B)
    (f : List Bool →₀ C) (hf : f ∈ Verification.PathRhoFinite.layer (R:=C) (available I (n+2)).card) :
    evaluate D (units S hI a 1)
      (Verification.PathRightEndpoint.projection
        (Verification.PathEndpointComplex.endpointConstant Verification.PathCoefficientRing.rho n) f)=
      evaluate D (units S hI a 1) f := by
  have hh := PathWordEndpointEvaluation.right_layer D
    (Verification.PathEndpointComplex.endpointConstant Verification.PathCoefficientRing.rho n)
    (signedCoordinate S hI a 1 (lastVertex hI)) (right_symbol S hI a D)
    ((units S hI a 1).take ((units S hI a 1).length-1)) f
  have hp : 0<(units S hI a 1).length := List.length_pos_iff.mpr (nonempty S hI a 1)
  have he : ((units S hI a 1).take ((units S hI a 1).length-1)).length+1=(available I (n+2)).card := by
    rw [List.length_take_of_le (by omega)]
    have hl := length_units S hI a 1
    omega
  rw [he] at hh
  rw [right_list] at hh
  exact hh hf

theorem left_projection (b : S) (D : Symbols (Coefficients S hI 1 b) B) (f : List Bool →₀ C) :
    evaluate D (units S hI 1 b) (Verification.PathLeftEndpoint.projection (0:C) f)=
      evaluate D (units S hI 1 b) f := by
  have hs : D.symbol (signedCoordinate S hI 1 b (firstVertex hI))=realize D.toCoefficients (0:C) := by
    rw [left_unit,D.one,map_zero]
  have hh := PathWordEndpointEvaluation.left_all D (0:C) (signedCoordinate S hI 1 b (firstVertex hI)) hs
    ((units S hI 1 b).drop 1) f
  rw [←left_list] at hh
  exact hh

theorem both_projection (D : Symbols (Coefficients S hI 1 1) B) (f : List Bool →₀ C)
    (hf : f ∈ Verification.PathRhoFinite.layer (R:=C) (available I (n+2)).card) :
    evaluate D (units S hI 1 1)
      (Verification.PathLeftEndpoint.projection (0:C)
        (Verification.PathRightEndpoint.projection
          (Verification.PathEndpointComplex.endpointConstant Verification.PathCoefficientRing.rho n) f))=
      evaluate D (units S hI 1 1) f := by
  rw [left_projection,right_projection S hI 1 D f hf]

#print axioms left_unit
#print axioms right_unit
#print axioms nonempty
#print axioms right_list
#print axioms left_list
#print axioms right_symbol
#print axioms right_projection
#print axioms left_projection
#print axioms both_projection
end Verification.PathOrderedEndpointEvaluation
