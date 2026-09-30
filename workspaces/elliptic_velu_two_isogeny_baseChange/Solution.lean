/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Elliptic_Curves_elliptic_velu_two_isogeny_baseChange
open Polynomial

universe u v

variable {K : Type u} [Field K]

theorem velu_two_isogeny_over_field_containing_root [DecidableEq K] [IsAlgClosed K] [NeZero (2 : K)]
    (A B x₀ : K)
    [hE : (ShortCurve A B).IsElliptic]
    (hroot : x₀ ^ 3 + A * x₀ + B = 0) :
    ∃ hE' : (ShortCurve (veluA' A x₀) (veluB' A B x₀)).IsElliptic,
    letI : (ShortCurve (veluA' A x₀) (veluB' A B x₀)).IsElliptic := hE'
    ∃ φ : (ShortCurve A B).Point →
          (ShortCurve (veluA' A x₀) (veluB' A B x₀)).Point,
      IsSeparableIsogenyInStandardForm
        A B (veluA' A x₀) (veluB' A B x₀)
        (veluTwoStandardMap A x₀)
        (veluTwoProjectiveTriple A x₀)
        φ ∧
      (veluTwoStandardMap A x₀).degree = 2 ∧
      HasKernelGeneratedByOrderTwo
        φ
        (twoTorsionPoint hroot) := by
  apply Submission.velu_two_isogeny_over_field_containing_root <;> assumption
