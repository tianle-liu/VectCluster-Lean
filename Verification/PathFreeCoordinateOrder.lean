/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathEndpointOrdering
import Verification.TorusModelWordBasis

/-!
# Path Free Coordinate Order

Removing constant endpoint classes shifts the increasing Laurent
coordinate index by exactly zero (Z) or one (Y).
-/
noncomputable section
namespace Verification.PathFreeCoordinateOrder
open Classical Verification.PathCompression Verification.PathClassRepresentatives
open Verification.PathClassOrdering Verification.PathEndpointOrdering
variable {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)
local notation "Z" => PathVariableEndpointMaps.FreeCoordinates hI

theorem z_card : Fintype.card Z+1=(available I (n+2)).card := by
  have h := PathVariableEndpointTorus.rank_formula hI
  have ha:=Verification.PathCompression.available_card hI
  simp only [Fintype.card_eq_nat_card] at h ⊢
  omega

def zIndex (p : Z) : Fin (Fintype.card Z) :=
  ⟨(index p.val).val,by have h:=right_free_index hI p;have hc:=z_card hI;omega⟩

theorem zIndex_strictMono : StrictMono (zIndex hI) := by
  intro p q hp
  exact index_strictMono hp

def zOrderIso : Z ≃o Fin (Fintype.card Z) :=
  StrictMono.orderIsoOfSurjective (zIndex hI) (zIndex_strictMono hI)
    ((Fintype.bijective_iff_injective_and_card (zIndex hI)).mpr
      ⟨(zIndex_strictMono hI).injective,by rw [Fintype.card_fin]⟩).2

theorem z_ordering (i : Fin (Fintype.card Z)) :
    (index (TorusModelWordBasis.ordering Z i).val).val=i.val := by
  have he : zOrderIso hI=(TorusModelWordBasis.ordering Z).symm := Subsingleton.elim _ _
  have h:=congrArg (fun e : Z≃oFin (Fintype.card Z) => e (TorusModelWordBasis.ordering Z i)) he
  change zIndex hI (TorusModelWordBasis.ordering Z i)=_ at h
  dsimp only at h
  rw [OrderIso.symm_apply_apply] at h
  exact congrArg Fin.val h

variable {a : ℕ} (hY : Admissible (2*a) I)
local notation "Y" => PathEvenEndpointTorus.FreeCoordinates hY

theorem y_card : Fintype.card Y+2=(available I (2*a+2)).card := by
  have h := PathEvenEndpointTorus.rank_formula hY
  have ha:=Verification.PathCompression.available_card hY
  simp only [Fintype.card_eq_nat_card] at h ⊢
  omega

def yIndex (p : Y) : Fin (Fintype.card Y) :=
  ⟨(index p.val).val-1,by have h:=both_free_indices hY p;have hc:=y_card hY;omega⟩

theorem yIndex_strictMono : StrictMono (yIndex hY) := by
  intro p q hp
  have h:=index_strictMono hp
  have hp₀:=(both_free_indices hY p).1
  change (index p.val).val<(index q.val).val at h
  change (index p.val).val-1<(index q.val).val-1
  omega

def yOrderIso : Y ≃o Fin (Fintype.card Y) :=
  StrictMono.orderIsoOfSurjective (yIndex hY) (yIndex_strictMono hY)
    ((Fintype.bijective_iff_injective_and_card (yIndex hY)).mpr
      ⟨(yIndex_strictMono hY).injective,by rw [Fintype.card_fin]⟩).2

theorem y_ordering (i : Fin (Fintype.card Y)) :
    (index (TorusModelWordBasis.ordering Y i).val).val=i.val+1 := by
  have he : yOrderIso hY=(TorusModelWordBasis.ordering Y).symm := Subsingleton.elim _ _
  have h:=congrArg (fun e : Y≃oFin (Fintype.card Y) => e (TorusModelWordBasis.ordering Y i)) he
  change yIndex hY (TorusModelWordBasis.ordering Y i)=_ at h
  dsimp only at h
  rw [OrderIso.symm_apply_apply] at h
  have hv:=congrArg Fin.val h
  have hp₀:=(both_free_indices hY (TorusModelWordBasis.ordering Y i)).1
  change (index (TorusModelWordBasis.ordering Y i).val).val-1=i.val at hv
  omega

#print axioms z_card
#print axioms zIndex
#print axioms zIndex_strictMono
#print axioms zOrderIso
#print axioms z_ordering
#print axioms y_card
#print axioms yIndex
#print axioms yIndex_strictMono
#print axioms yOrderIso
#print axioms y_ordering
end Verification.PathFreeCoordinateOrder
