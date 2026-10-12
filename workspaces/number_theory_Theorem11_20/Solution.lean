/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Number_Theory_I_number_theory_Theorem11_20

universe uK uL

theorem Theorem11_20 {K : Type uK} [Field K]
    (hK : IsGlobalField K)
    (v : AbsoluteValue K ℝ)
    (hv_nontrivial : v.IsNontrivial)
    (Lhat : Type uL)
    [Field Lhat]
    [Algebra (AbsoluteValue.Completion v) Lhat]
    (hLhat_fin : FiniteDimensional (AbsoluteValue.Completion v) Lhat)
    (hLhat_sep : Algebra.IsSeparable (AbsoluteValue.Completion v) Lhat) :
    ∃ (L : Type uK) (_ : Field L) (_ : Algebra K L)
      (hL_fin : FiniteDimensional K L)
      (_ : Algebra.IsSeparable K L)
      (w : AbsoluteValue L ℝ)
      (absLhat : AbsoluteValue Lhat ℝ),
      (∀ x : K, w (algebraMap K L x) = v x) ∧
        (Module.finrank K L = Module.finrank (AbsoluteValue.Completion v) Lhat) ∧
          ∃ (_ : Algebra (AbsoluteValue.Completion v) (AbsoluteValue.Completion w))
            (e : AbsoluteValue.Completion w ≃ₐ[AbsoluteValue.Completion v] Lhat),
            (∀ x : K,
              algebraMap (AbsoluteValue.Completion v) (AbsoluteValue.Completion w)
                  (x : AbsoluteValue.Completion v) =
                (algebraMap K L x : AbsoluteValue.Completion w)) ∧
              (∀ x : AbsoluteValue.Completion v,
                absLhat (algebraMap (AbsoluteValue.Completion v) Lhat x) = ‖x‖) ∧
                (∀ x : AbsoluteValue.Completion w, absLhat (e x) = ‖x‖) ∧
                  Algebra.adjoin (AbsoluteValue.Completion v)
                    (Set.range fun x : L =>
                      (e ((x : AbsoluteValue.Completion w)) : Lhat)) = ⊤ := by
  exact Submission.Theorem11_20 hK v hv_nontrivial Lhat hLhat_fin hLhat_sep
