/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PureContractionTransfer

/-!
# Weighted Pure Contraction

Exact weight preservation is imposed on the proved pure contraction by
extracting its degree-minus-one, weight-zero matrix component and normalizing.
This works over the original arbitrary commutative coefficient ring.
-/

namespace Verification.WeightedPureContraction

open Verification.GradedPerturbation Verification.FinitePerturbation
  Verification.GradedIntegralSplitting

variable {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι]

structure Data (d : ι → ℤ) (w : ι → ℕ) (A : Matrix ι ι R)
    extends Verification.PathPureContractionData.Data d A where
  weight_preserving : ∀ i j,w i ≠ w j → homotopy i j=0

noncomputable def ofPure (d : ι → ℤ) (w : ι → ℕ) (A : Matrix ι ι R)
    (T : Verification.PathPureContractionData.Data d A)
    (hw : ∀ i j,w i ≠ w j → A i j=0) : Data d w A := by
  let wt : ι → ℤ := fun i => w i
  have hW : Homogeneous wt 0 A := by
    intro i j hij
    exact hw i j (by intro he; apply hij; change (w i:ℤ)=(w j:ℤ)+0; rw [he,add_zero])
  let G := component d wt (-1) T.homotopy
  have hG : A*G*A=A := component_generalized d wt A T.homotopy T.differential_degree hW T.generalized
  let H := normalize A G
  have hH : H*H=0 := normalize_square A G hG
  have hHAH : H*A*H=H := normalize_regular A G T.differential_square hG
  have hAHA : A*H*A=A := normalize_generalized A G T.differential_square hG
  have hdH : Homogeneous d (-1) H := normalize_degree d A G T.differential_degree (component_degree d wt (-1) _)
  have hwH : Homogeneous wt 0 H := normalize_weight wt A G hW (component_weight d wt (-1) _)
  exact {
    differential_degree := T.differential_degree
    differential_square := T.differential_square
    homotopy := H
    homotopy_degree := hdH
    homotopy_square := hH
    homotopy_regular := hHAH
    generalized := hAHA
    supported := fun i j hi => Verification.ContractionProjectionSupport.projection_row_zero d A H
      T.differential_degree hdH T.differential_square hH hHAH hAHA (d i)
      (Verification.PureContractionTransfer.vanishing d A T (d i) hi) i j rfl
    weight_preserving := fun i j hij => hwH i j (by change (w i:ℤ) ≠ (w j:ℤ)+0; omega) }

#print axioms Data
#print axioms ofPure

end Verification.WeightedPureContraction
