/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOrderedFaceUnits
import Verification.PathFreeCoordinateOrder

/-!
# Path Ordered Coordinate List

The sorted geometric units have exactly the indices of the genuine
Laurent basis; removal of the fixed left endpoint shifts Y indices by one.
-/
noncomputable section
namespace Verification.PathOrderedCoordinateList
open Classical Verification.PathCompression Verification.PathClassRepresentatives
open Verification.PathSignedStratumCoefficients Verification.PathOrderedFaceUnits
open Verification.PathRepresentativeFaceList Verification.PathClassOrdering
open Verification.PathFreeCoordinateOrder
variable (S : Type) [CommRing S] {n : ℕ} {I : Finset ℕ}
variable (hI : Admissible n I) (a b : S)

theorem length_units : (units S hI a b).length=(available I (n+2)).card := by
  rw [units,List.length_map,length_representatives]

theorem at_index (p : Representatives n I) :
    (units S hI a b)[(index p).val]'(by rw [length_units];exact (index p).isLt)=
      signedCoordinate S hI a b (includeRepresentative p) := by
  simp only [units,List.getElem_map,get_index]
  exact unitAt_vertex S hI a b (includeRepresentative p)

theorem z_at (i : Fin (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI))) :
    (units S hI a b)[i.val]'(by rw [length_units];have hh:=z_card hI;have hi:=i.isLt;omega)=
      signedCoordinate S hI a b
        (includeRepresentative (TorusModelWordBasis.ordering (PathVariableEndpointMaps.FreeCoordinates hI) i).val) := by
  simpa only [z_ordering] using
    at_index S hI a b (TorusModelWordBasis.ordering (PathVariableEndpointMaps.FreeCoordinates hI) i).val

variable {m : ℕ} (hY : Admissible (2*m) I)

theorem y_at (i : Fin (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hY))) :
    (units S hY a b)[i.val+1]'(by rw [length_units];have hh:=y_card hY;have hi:=i.isLt;omega)=
      signedCoordinate S hY a b
        (includeRepresentative (TorusModelWordBasis.ordering (PathEvenEndpointTorus.FreeCoordinates hY) i).val) := by
  simpa only [y_ordering] using
    at_index S hY a b (TorusModelWordBasis.ordering (PathEvenEndpointTorus.FreeCoordinates hY) i).val

#print axioms length_units
#print axioms at_index
#print axioms z_at
#print axioms y_at
end Verification.PathOrderedCoordinateList
