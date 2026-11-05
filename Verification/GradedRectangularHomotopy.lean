/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GradedMatrixComplex

/-!
# Graded Rectangular Homotopy

A degree-compatible homogeneous rectangular contraction gives an actual
homotopy equivalence in the graded coefficient category, before any sheaf
realization.
-/

noncomputable section
namespace Verification.GradedRectangularHomotopy

open Classical CategoryTheory CategoryTheory.Limits Verification.GradedCoefficientCategory Verification.GradedMatrixComplex

variable {X Y : Space} (d : X.index → ℤ) (e : Y.index → ℤ)
variable (D H : X ⟶ X) (I : Y ⟶ X) (J : X ⟶ Y)
variable (hd : Supported d d 1 D) (hh : Supported d d (-1) H)
  (hi : Supported e d 0 I) (hj : Supported d e 0 J)
variable (hsq : D≫D=0) (hdi : I≫D=0) (hjd : D≫J=0)
variable (hji : I≫J=𝟙 Y) (hij : J≫I=𝟙 X-(D≫H)-(H≫D))

def source := complex X d D hd hsq
def target := complex Y e 0 (supported_zero e e 1) (by simp)

def inclusion : target e ⟶ source d D hd hsq :=
  map I hi (by simpa only [zero_comp] using hdi)

def retraction : source d D hd hsq ⟶ target e :=
  map J hj (by simpa only [comp_zero] using hjd.symm)

include hji in
theorem inclusion_retraction : inclusion d e D I hd hi hsq hdi ≫
    retraction d e D J hd hj hsq hjd=𝟙 (target e) := by
  apply HomologicalComplex.Hom.ext
  funext p
  change cut e d p p I ≫ cut d e p p J=𝟙 _
  rw [cut_comp e d e I J 0 hi p p p (by omega),hji,cut_id]

def homotopy : Homotopy
    (retraction d e D J hd hj hsq hjd ≫ inclusion d e D I hd hi hsq hdi)
    (𝟙 (source d D hd hsq)) where
  hom p q := if q+1=p then -cut d d p q H else 0
  zero p q hpq := by
    change (if q+1=p then -cut d d p q H else 0)=0
    exact if_neg hpq
  comm p := by
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel p (p+1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (p-1) p by change p-1+1=p;omega)]
    have hp : p-1+1=p := by omega
    simp only [if_pos rfl,if_pos hp,if_true,source]
    rw [complex_d_between X d D hd hsq p (p+1) rfl,
      complex_d_between X d D hd hsq (p-1) p hp]
    change cut d e p p J ≫ cut e d p p I=
      (cut d d p (p+1) D ≫ (-cut d d (p+1) p H))+
      ((-cut d d p (p-1) H) ≫ cut d d (p-1) p D)+𝟙 (degreeSpace X d p)
    rw [Preadditive.comp_neg,Preadditive.neg_comp,
      cut_comp d e d J I 0 hj p p p (by omega),
      cut_comp d d d D H 1 hd p (p+1) p rfl,
      cut_comp d d d H D (-1) hh p (p-1) p (by omega),hij]
    apply Subtype.ext
    funext i j
    change (1 : Matrix X.index X.index Verification.PathCoefficientRing.Coeff) i.val j.val-
        (H.val*D.val) i.val j.val-(D.val*H.val) i.val j.val=
      -(H.val*D.val) i.val j.val+ -(D.val*H.val) i.val j.val+(1 : Matrix _ _ _) i j
    have he := congrArg (fun f : degreeSpace X d p ⟶ degreeSpace X d p=>f.val i j) (cut_id d p)
    change (1 : Matrix X.index X.index Verification.PathCoefficientRing.Coeff) i.val j.val=
      (1 : Matrix _ _ _) i j at he
    rw [he]
    abel

def equivalence : HomotopyEquiv (source d D hd hsq) (target e) where
  hom := retraction d e D J hd hj hsq hjd
  inv := inclusion d e D I hd hi hsq hdi
  homotopyHomInvId := homotopy d e D H I J hd hh hi hj hsq hdi hjd hij
  homotopyInvHomId := Homotopy.ofEq (inclusion_retraction d e D I J hd hi hj hsq hdi hjd hji)

#print axioms source
#print axioms target
#print axioms inclusion
#print axioms retraction
#print axioms inclusion_retraction
#print axioms homotopy
#print axioms equivalence

end Verification.GradedRectangularHomotopy
