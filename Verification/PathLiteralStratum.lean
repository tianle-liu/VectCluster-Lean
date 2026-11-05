/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathClassRepresentatives
import Verification.PathRecursion
import Verification.SplitExchangeChart

/-!
# Path Literal Stratum

The literal path stratum: quotient the actual exchange algebra by the
selected original coordinates, then invert all remaining coordinates.
Endpoint coordinates are included among the inverted units; for unit endpoints
this is precisely the same open stratum.
-/
noncomputable section
namespace Verification.PathLiteralStratum
open Verification.PathPresentation Verification.PathClassRepresentatives Verification.PathCompression
open Finset
variable (R : Type) [CommRing R] {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)
variable (a b : R)

def mutableIndex (i : I) : Fin n :=
  ⟨i.val-1,by have hh:=mem_Icc.mp (hI.1 i.property);omega⟩

def zeroIdeal : Ideal (PathAlgebra n a b) :=
  Ideal.span (Set.range (fun i : I => x a b (mutableIndex hI i)))
abbrev Closed := PathAlgebra n a b ⧸ zeroIdeal R hI a b

def closedX (i : Fin n) : Closed R hI a b :=
  Ideal.Quotient.mk (zeroIdeal R hI a b) (x a b i)
def closedY (i : Fin n) : Closed R hI a b :=
  Ideal.Quotient.mk (zeroIdeal R hI a b) (y a b i)

def closedPosition (p : Fin (n+2)) : Closed R hI a b :=
  boundary (algebraMap R _ a) (algebraMap R _ b) (closedX R hI a b) p

def vertexPosition (p : Vertices n I) : Fin (n+2) :=
  ⟨p.val,mem_range.mp (mem_sdiff.mp p.property).1⟩

def openMonoid : Submonoid (Closed R hI a b) :=
  Submonoid.closure (Set.range (fun p : Vertices n I => closedPosition R hI a b (vertexPosition p)))
abbrev Layer := Localization (openMonoid R hI a b)

def layerX (i : Fin n) : Layer R hI a b := algebraMap _ _ (closedX R hI a b i)
def layerY (i : Fin n) : Layer R hI a b := algebraMap _ _ (closedY R hI a b i)
def position (p : Fin (n+2)) : Layer R hI a b := algebraMap _ _ (closedPosition R hI a b p)

theorem closed_equations : Equations (algebraMap R (Closed R hI a b) a)
    (algebraMap R _ b) (closedX R hI a b) (closedY R hI a b) :=
  PathRecursion.equations_map (Ideal.Quotient.mk (zeroIdeal R hI a b)) _ _ _ _ (equations n a b)

theorem layer_equations : Equations (algebraMap R (Layer R hI a b) a)
    (algebraMap R _ b) (layerX R hI a b) (layerY R hI a b) :=
  PathRecursion.equations_map (algebraMap (Closed R hI a b) _) _ _ _ _ (closed_equations R hI a b)

theorem position_boundary (p : Fin (n+2)) : position R hI a b p=
    boundary (algebraMap R _ a) (algebraMap R _ b) (layerX R hI a b) p :=
  boundary_map (algebraMap (Closed R hI a b) _) _ _ _ p

theorem closed_zero (i : I) : closedX R hI a b (mutableIndex hI i)=0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))

theorem layer_zero (i : I) : layerX R hI a b (mutableIndex hI i)=0 := by
  rw [layerX,closed_zero,map_zero]

theorem position_middle (i : Fin n) : position R hI a b i.castSucc.succ=layerX R hI a b i := by
  rw [position_boundary,boundary_middle]

theorem position_left (i : I) :
    vertexPosition (leftVertex hI i)=(mutableIndex hI i).castSucc.castSucc := by
  apply Fin.ext
  rfl

theorem position_right (i : I) :
    vertexPosition (rightVertex hI i)=(mutableIndex hI i).succ.succ := by
  apply Fin.ext
  dsimp [vertexPosition,rightVertex,mutableIndex]
  have hh:=mem_Icc.mp (hI.1 i.property)
  omega

theorem neighbor_relation (i : I) :
    position R hI a b (vertexPosition (rightVertex hI i))=
      -position R hI a b (vertexPosition (leftVertex hI i)) := by
  have hh := layer_equations R hI a b (mutableIndex hI i)
  rw [layer_zero,zero_mul] at hh
  rw [position_right,position_left,position_boundary,position_boundary]
  exact eq_neg_of_add_eq_zero_right hh.symm

theorem coordinate_isUnit (p : Vertices n I) :
    IsUnit (position R hI a b (vertexPosition p)) :=
  IsLocalization.map_units (M := openMonoid R hI a b) (Layer R hI a b)
    ⟨closedPosition R hI a b (vertexPosition p),Submonoid.subset_closure (Set.mem_range_self p)⟩

def coordinateUnit (p : Vertices n I) : (Layer R hI a b)ˣ := (coordinate_isUnit R hI a b p).unit

theorem coordinateUnit_val (p : Vertices n I) :
    (coordinateUnit R hI a b p : Layer R hI a b)=position R hI a b (vertexPosition p) :=
  (coordinate_isUnit R hI a b p).unit_spec

def signedUnit (p : Vertices n I) : (Layer R hI a b)ˣ :=
  (-1)^(p.val/2)*coordinateUnit R hI a b p

theorem signedUnit_val (p : Vertices n I) :
    (signedUnit R hI a b p : Layer R hI a b)=
      (-1)^(p.val/2)*position R hI a b (vertexPosition p) := by
  simp only [signedUnit,Units.val_mul,Units.val_pow_eq_pow_val,Units.val_neg,Units.val_one,coordinateUnit_val]

theorem signed_neighbor (i : I) :
    signedUnit R hI a b (rightVertex hI i)=signedUnit R hI a b (leftVertex hI i) := by
  apply Units.ext
  rw [signedUnit_val,signedUnit_val,neighbor_relation]
  have hp := (mem_Icc.mp (hI.1 i.property)).1
  have he : (i.val+1)/2=(i.val-1)/2+1 := by omega
  change (-1:Layer R hI a b)^((i.val+1)/2)*(-position R hI a b _) =
    (-1:Layer R hI a b)^((i.val-1)/2)*position R hI a b _
  rw [he,pow_succ]
  ring

#print axioms mutableIndex
#print axioms zeroIdeal
#print axioms Closed
#print axioms closedX
#print axioms closedY
#print axioms closedPosition
#print axioms vertexPosition
#print axioms openMonoid
#print axioms Layer
#print axioms layerX
#print axioms layerY
#print axioms position
#print axioms closed_equations
#print axioms layer_equations
#print axioms position_boundary
#print axioms closed_zero
#print axioms layer_zero
#print axioms position_middle
#print axioms position_left
#print axioms position_right
#print axioms neighbor_relation
#print axioms coordinate_isUnit
#print axioms coordinateUnit
#print axioms coordinateUnit_val
#print axioms signedUnit
#print axioms signedUnit_val
#print axioms signed_neighbor
end Verification.PathLiteralStratum
