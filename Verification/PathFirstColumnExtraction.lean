/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathFirstBoundaryCutout
import Verification.PathFirstCofaceRelations

/-!
# Path First Column Extraction

The actual endpoint-normal first columns are obtained from the literal
transpose cofaces by coefficient extraction at padded original word bases.
-/

namespace Verification.PathFirstColumnExtraction

open Classical Verification.PathWords Verification.PathFirstBasis Verification.PathFirstBoundaryCutout
  Verification.PathEndpointWords Verification.PathFirstCofaces

variable {R : Type*} [CommRing R]

noncomputable def zExtract (n : ℕ) : (List Bool →₀ R) →ₗ[R] (Word (n+1) →₀ R) :=
  (Finsupp.linearEquivFunOnFinite R R (Word (n+1))).symm.toLinearMap.comp
    (LinearMap.pi (fun w => Finsupp.lapply (w.val++[false])))

noncomputable def yExtract (a : ℕ) : (List Bool →₀ R) →ₗ[R] (Word (2*a) →₀ R) :=
  (Finsupp.linearEquivFunOnFinite R R (Word (2*a))).symm.toLinearMap.comp
    (LinearMap.pi (fun w => Finsupp.lapply (false::(w.val++[false]))))

theorem zExtract_apply (n : ℕ) (x : List Bool →₀ R) (w : Word (n+1)) :
    zExtract n x w=x (w.val++[false]) := rfl

theorem yExtract_apply (a : ℕ) (x : List Bool →₀ R) (w : Word (2*a)) :
    yExtract a x w=x (false::(w.val++[false])) := rfl

theorem zExtract_single (n : ℕ) (w : Word (n+1)) (r : R) :
    zExtract n (Finsupp.single (w.val++[false]) r)=Finsupp.single w r := by
  apply Finsupp.ext
  intro v
  rw [zExtract_apply]
  simp only [Finsupp.single_apply,List.append_cancel_right_eq,Subtype.ext_iff]

theorem yExtract_single (a : ℕ) (w : Word (2*a)) (r : R) :
    yExtract a (Finsupp.single (false::(w.val++[false])) r)=Finsupp.single w r := by
  apply Finsupp.ext
  intro v
  rw [yExtract_apply]
  simp only [Finsupp.single_apply,List.cons.injEq,true_and,List.append_cancel_right_eq,Subtype.ext_iff]

theorem zColumn_extract (g : R) (n : ℕ) (v : OneSource RightNormal n) :
    zColumn g n v=zExtract n (cofaceColumn (-g) 0 (v.1.val-1) v.2.val) := by
  ext w
  exact zColumn_apply g n v w

theorem yColumn_extract (g : R) (a : ℕ) (v : OneSource BothNormal (2*a)) :
    yColumn g a v=yExtract a (cofaceColumn (-g) 0 (v.1.val-1) v.2.val) := by
  ext w
  exact yColumn_apply g a v w

#print axioms zExtract
#print axioms yExtract
#print axioms zExtract_apply
#print axioms yExtract_apply
#print axioms zExtract_single
#print axioms yExtract_single
#print axioms zColumn_extract
#print axioms yColumn_extract

end Verification.PathFirstColumnExtraction
