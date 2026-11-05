/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LaurentPolynomialUniversal
import Verification.FinsuppTorusUniversal
import Verification.ExchangeTransverseSlice

/-!
# Laurent Torus Character Quotient

The literal Laurent line over an actual character fiber is the full torus
with the same coefficient character relations. Both directions and every unit
coordinate are constructed, before applying any cohomological theory.
-/
noncomputable section
namespace Verification.LaurentTorusCharacterQuotient
open Verification.OriginalTorus Verification.ExchangeTransverseSlice
variable (R κ ι : Type) [CommRing R] (χ : ι → (Torus R κ)ˣ)

abbrev New := LaurentPolynomialUniversal.Laurent (Fiber χ)

def coefficient : Torus R κ →ₐ[R] Torus R (Option κ) :=
  FinsuppTorusUniversal.lift R κ (fun i => FinsuppTorusUniversal.unit R (Option κ) (some i))

theorem coefficient_coordinate (i : κ) : coefficient R κ (torusCoordinate R κ i)=
    torusCoordinate R (Option κ) (some i) := FinsuppTorusUniversal.lift_coordinate _ _ _ _

def fullIdeal : Ideal (Torus R (Option κ)) :=
  Ideal.span (Set.range (fun i => 1+coefficient R κ (χ i : Torus R κ)))

abbrev FullFiber := Torus R (Option κ) ⧸ fullIdeal R κ ι χ

def quotient : Torus R (Option κ) →ₐ[R] FullFiber R κ ι χ := Ideal.Quotient.mkₐ R _

def targetUnits : Option κ → (New R κ ι χ)ˣ
  | none => LaurentPolynomialUniversal.parameterUnit (Fiber χ)
  | some i => Units.map (algebraMap (Torus R κ) (New R κ ι χ)).toMonoidHom
      (FinsuppTorusUniversal.unit R κ i)

def toNewRaw : Torus R (Option κ) →ₐ[R] New R κ ι χ :=
  FinsuppTorusUniversal.lift R (Option κ) (targetUnits R κ ι χ)

theorem toNewRaw_coefficient :
    (toNewRaw R κ ι χ).comp (coefficient R κ)=IsScalarTower.toAlgHom R (Torus R κ) (New R κ ι χ) := by
  apply FinsuppTorusUniversal.hom_ext
  intro i
  change toNewRaw R κ ι χ (coefficient R κ (torusCoordinate R κ i))=_
  rw [coefficient_coordinate]
  change FinsuppTorusUniversal.lift R (Option κ) _ (torusCoordinate R (Option κ) (some i))=_
  rw [FinsuppTorusUniversal.lift_coordinate]
  rfl

theorem toNewRaw_relation (i : ι) :
    toNewRaw R κ ι χ (1+coefficient R κ (χ i : Torus R κ))=0 := by
  rw [map_add,map_one]
  rw [show toNewRaw R κ ι χ (coefficient R κ (χ i : Torus R κ))=
    algebraMap (Torus R κ) (New R κ ι χ) (χ i : Torus R κ) from
      AlgHom.congr_fun (toNewRaw_coefficient R κ ι χ) _]
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_range_self i) : (1+(χ i : Torus R κ))∈fiberIdeal χ)
  have hh := congrArg (algebraMap (Fiber χ) (New R κ ι χ)) h
  simpa only [map_add,map_one,map_zero] using hh

def toNew : FullFiber R κ ι χ →ₐ[R] New R κ ι χ :=
  Ideal.Quotient.liftₐ _ (toNewRaw R κ ι χ) (by
    change fullIdeal R κ ι χ ≤ RingHom.ker (toNewRaw R κ ι χ).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact toNewRaw_relation R κ ι χ i)

def coefficientLift : Fiber χ →ₐ[R] FullFiber R κ ι χ :=
  Ideal.Quotient.liftₐ _ ((quotient R κ ι χ).comp (coefficient R κ)) (by
    change fiberIdeal χ ≤ RingHom.ker ((quotient R κ ι χ).comp (coefficient R κ)).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change quotient R κ ι χ (coefficient R κ (1+(χ i : Torus R κ)))=0
    rw [map_add,map_one]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i)))

def normalUnit : (FullFiber R κ ι χ)ˣ :=
  Units.map (quotient R κ ι χ).toMonoidHom (FinsuppTorusUniversal.unit R (Option κ) none)

def fromNew : New R κ ι χ →ₐ[R] FullFiber R κ ι χ :=
  LaurentPolynomialUniversal.lift (coefficientLift R κ ι χ) (normalUnit R κ ι χ)

theorem fromNew_coefficient (a : Torus R κ) :
    fromNew R κ ι χ (algebraMap (Torus R κ) (New R κ ι χ) a)=
      quotient R κ ι χ (coefficient R κ a) := by
  rw [IsScalarTower.algebraMap_apply (Torus R κ) (Fiber χ) (New R κ ι χ)]
  exact LaurentPolynomialUniversal.lift_coefficient _ _ _

theorem fromNew_parameter :
    fromNew R κ ι χ (LaurentPolynomialUniversal.parameter (Fiber χ))=
      quotient R κ ι χ (torusCoordinate R (Option κ) none) :=
  LaurentPolynomialUniversal.lift_parameter _ _

theorem toNew_coordinate (i : Option κ) :
    toNew R κ ι χ (quotient R κ ι χ (torusCoordinate R (Option κ) i))=
      (targetUnits R κ ι χ i : New R κ ι χ) :=
  FinsuppTorusUniversal.lift_coordinate _ _ _ _

theorem toNew_fromNew : (toNew R κ ι χ).comp (fromNew R κ ι χ)=AlgHom.id R _ := by
  apply LaurentPolynomialUniversal.hom_ext
  · intro x
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
    change toNew R κ ι χ (fromNew R κ ι χ (algebraMap (Torus R κ) (New R κ ι χ) a))=_
    rw [fromNew_coefficient]
    exact AlgHom.congr_fun (toNewRaw_coefficient R κ ι χ) a
  · change toNew R κ ι χ (fromNew R κ ι χ (LaurentPolynomialUniversal.parameter (Fiber χ)))=_
    rw [fromNew_parameter,toNew_coordinate]
    exact LaurentPolynomialUniversal.parameterUnit_val

theorem fromNew_toNew : (fromNew R κ ι χ).comp (toNew R κ ι χ)=AlgHom.id R _ := by
  apply Ideal.Quotient.algHom_ext
  apply FinsuppTorusUniversal.hom_ext
  intro i
  change fromNew R κ ι χ (toNew R κ ι χ
    (quotient R κ ι χ (torusCoordinate R (Option κ) i)))=_
  rw [toNew_coordinate]
  cases i with
  | none =>
    change fromNew R κ ι χ (LaurentPolynomialUniversal.parameterUnit (Fiber χ) : New R κ ι χ)=_
    rw [LaurentPolynomialUniversal.parameterUnit_val,fromNew_parameter]
    rfl
  | some i =>
    change fromNew R κ ι χ (algebraMap (Torus R κ) (New R κ ι χ) (torusCoordinate R κ i))=_
    rw [fromNew_coefficient,coefficient_coordinate]
    rfl

def equiv : FullFiber R κ ι χ ≃ₐ[R] New R κ ι χ :=
  AlgEquiv.ofAlgHom (toNew R κ ι χ) (fromNew R κ ι χ)
    (toNew_fromNew R κ ι χ) (fromNew_toNew R κ ι χ)

theorem equiv_coordinate (i : Option κ) :
    equiv R κ ι χ (quotient R κ ι χ (torusCoordinate R (Option κ) i))=
      (targetUnits R κ ι χ i : New R κ ι χ) := toNew_coordinate R κ ι χ i

#print axioms New
#print axioms coefficient
#print axioms coefficient_coordinate
#print axioms fullIdeal
#print axioms FullFiber
#print axioms quotient
#print axioms targetUnits
#print axioms toNewRaw
#print axioms toNewRaw_coefficient
#print axioms toNewRaw_relation
#print axioms toNew
#print axioms coefficientLift
#print axioms normalUnit
#print axioms fromNew
#print axioms fromNew_coefficient
#print axioms fromNew_parameter
#print axioms toNew_coordinate
#print axioms toNew_fromNew
#print axioms fromNew_toNew
#print axioms equiv
#print axioms equiv_coordinate
end Verification.LaurentTorusCharacterQuotient
