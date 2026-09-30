/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib



















namespace Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_quadraticForm_represents_every_element_of_represents_zero


def QuadraticFormRepresents
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (a : K) : Prop :=
  ∃ v : V, Q v = a


def QuadraticFormRepresentsZeroNontrivially
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) : Prop :=
  ∃ v : V, v ≠ 0 ∧ Q v = 0








def QuadraticFormNondegenerate
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) : Prop :=
  ∀ v : V, (∀ w : V, Q (v + w) - Q v - Q w = 0) → v = 0



end Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_quadraticForm_represents_every_element_of_represents_zero
