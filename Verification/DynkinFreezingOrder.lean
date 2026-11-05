/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.DynkinMatrixNormalForm
import Verification.DynkinShapeDeletion
import Verification.FreezingOrderEquiv

/-!
# Dynkin Freezing Order

Every actual irreducible finite Dynkin matrix normal form has the
required ordering. All deletion cases are checked here; classification
supplies only the usual matrix list, never the ordering conclusion.
-/
noncomputable section
namespace Verification.DynkinFreezingOrder
open Verification.PathForestMatrixPredicate Verification.DynkinMatrixNormalForm

theorem path_good (n : ℕ) (a : ℕ→ℤˣ) (E : Fin n→Fin n→Prop) :
    FreezingOrder.Good IsPathForest (PathOrientationSigns.matrix a n) E Fin.val := by
  intro _ m g _
  exact PathForestRestriction.hereditary _ (PathForestArbitraryLengths.single n a) g

theorem exists_order (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (N : NormalForm n A) (E : Fin n→Fin n→Prop) :
    ∃rank : Fin n→ℕ,Function.Injective rank ∧ FreezingOrder.Good IsPathForest A E rank := by
  rcases N with ⟨kind,a,b,u,e,h⟩
  cases kind with
  | A r =>
    exact FreezingOrderEquiv.transport IsPathForest _ Fin.val e A E h
      Fin.val_injective (path_good (r+1) a (fun i j=>E (e i) (e j)))
  | B r =>
    exact FreezingOrderEquiv.transport IsPathForest _
      (OneVertexFreezingOrder.rank (⟨0,by omega⟩ : Fin (r+2))) e A E h
      (OneVertexFreezingOrder.rank_injective _)
      (DynkinShapeDeletion.modified_good (r+2) a ⟨0,by omega⟩ (2*(a 0:ℤ)) (-(a 0:ℤ)) (fun i j=>E (e i) (e j)))
  | C r =>
    exact FreezingOrderEquiv.transport IsPathForest _
      (OneVertexFreezingOrder.rank (⟨0,by omega⟩ : Fin (r+2))) e A E h
      (OneVertexFreezingOrder.rank_injective _)
      (DynkinShapeDeletion.modified_good (r+2) a ⟨0,by omega⟩ (a 0:ℤ) (-2*(a 0:ℤ)) (fun i j=>E (e i) (e j)))
  | D r =>
    exact ⟨OneVertexFreezingOrder.rank (e none),OneVertexFreezingOrder.rank_injective _,
      DynkinShapeDeletion.branched_good (dArms r) b (fun i=>(u i:ℤ)) (fun i=>-(u i:ℤ)) n e A h E⟩
  | E6 =>
    exact ⟨OneVertexFreezingOrder.rank (e none),OneVertexFreezingOrder.rank_injective _,
      DynkinShapeDeletion.branched_good (eArms 0) b (fun i=>(u i:ℤ)) (fun i=>-(u i:ℤ)) n e A h E⟩
  | E7 =>
    exact ⟨OneVertexFreezingOrder.rank (e none),OneVertexFreezingOrder.rank_injective _,
      DynkinShapeDeletion.branched_good (eArms 1) b (fun i=>(u i:ℤ)) (fun i=>-(u i:ℤ)) n e A h E⟩
  | E8 =>
    exact ⟨OneVertexFreezingOrder.rank (e none),OneVertexFreezingOrder.rank_injective _,
      DynkinShapeDeletion.branched_good (eArms 2) b (fun i=>(u i:ℤ)) (fun i=>-(u i:ℤ)) n e A h E⟩
  | F4 =>
    exact FreezingOrderEquiv.transport IsPathForest _
      (OneVertexFreezingOrder.rank (⟨1,by omega⟩ : Fin 4)) e A E h
      (OneVertexFreezingOrder.rank_injective _)
      (DynkinShapeDeletion.modified_good 4 a ⟨1,by omega⟩ (2*(a 1:ℤ)) (-(a 1:ℤ)) (fun i j=>E (e i) (e j)))
  | G2 =>
    exact FreezingOrderEquiv.transport IsPathForest _
      (OneVertexFreezingOrder.rank (⟨0,by omega⟩ : Fin 2)) e A E h
      (OneVertexFreezingOrder.rank_injective _)
      (DynkinShapeDeletion.modified_good 2 a ⟨0,by omega⟩ (3*(a 0:ℤ)) (-(a 0:ℤ)) (fun i j=>E (e i) (e j)))

#print axioms path_good
#print axioms exists_order
end Verification.DynkinFreezingOrder
