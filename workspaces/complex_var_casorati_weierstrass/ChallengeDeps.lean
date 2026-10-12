/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Filter
open scoped Topology

namespace Autoform_Functions_of_a_Complex_Variable_complex_var_casorati_weierstrass

def HolomorphicOnPuncturedNhds (f : ℂ → ℂ) (c : ℂ) : Prop :=
  ∀ᶠ U in (𝓝[≠] c) , DifferentiableAt ℂ f U

def RemovableAt (f : ℂ → ℂ) (c : ℂ) : Prop :=
  ∃ L : ℂ, Tendsto f (𝓝[≠] c) (𝓝 L)

def PoleAt (f : ℂ → ℂ) (c : ℂ) : Prop :=
  Tendsto (fun z : ℂ => ‖f z‖) (𝓝[≠] c) atTop

def EssentialSingularityAt (f : ℂ → ℂ) (c : ℂ) : Prop :=
  HolomorphicOnPuncturedNhds f c ∧
    ¬ RemovableAt f c ∧
    ¬ PoleAt f c



end Autoform_Functions_of_a_Complex_Variable_complex_var_casorati_weierstrass
