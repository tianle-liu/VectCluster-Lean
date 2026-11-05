/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrincipalFiniteDynkinBundles
import Verification.SevenfoldMainCounterexample

/-!
# Main theorems of VectCluster

Convenience entry point for the manuscript's main theorems A and B.
Their explicit reference-theory hypotheses remain part of the statements.
See the README for the mathematical scope and build instructions.
The source manuscript is [Liu and Liu (2026)](https://arxiv.org/abs/2610.12748).
-/

#check Verification.PrincipalFiniteDynkinBundles.all_free
#check Verification.SevenfoldMainCounterexample.exists_bundle

#print axioms Verification.PrincipalFiniteDynkinBundles.all_free
#print axioms Verification.SevenfoldMainCounterexample.exists_bundle
