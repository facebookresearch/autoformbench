/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Data.ZMod.Basic
import Submission
import ChallengeDeps

open Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_padic_completion_rat_iso_fraction_field_padic_int_limit
noncomputable section

namespace Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_padic_completion_rat_iso_fraction_field_padic_int_limit



theorem padicIntLimitTransition_dvd (p n : ℕ) : p ^ (n + 1) ∣ p ^ (n + 2) := by apply Submission.Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_padic_completion_rat_iso_fraction_field_padic_int_limit.padicIntLimitTransition_dvd <;> assumption





def padicIntLimitTransition (p n : ℕ) :
    ZMod (p ^ (n + 2)) →+* ZMod (p ^ (n + 1)) :=
  ZMod.castHom
    (padicIntLimitTransition_dvd p n)
      
    (ZMod (p ^ (n + 1)))

theorem PadicIntLimitSubring_zero_mem (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) :
    padicIntLimitTransition p n ((0 : (m : ℕ) → ZMod (p ^ (m + 1))) (n + 1))
      = (0 : (m : ℕ) → ZMod (p ^ (m + 1))) n := by apply Submission.Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_padic_completion_rat_iso_fraction_field_padic_int_limit.PadicIntLimitSubring_zero_mem <;> assumption


theorem PadicIntLimitSubring_one_mem (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) :
    padicIntLimitTransition p n ((1 : (m : ℕ) → ZMod (p ^ (m + 1))) (n + 1))
      = (1 : (m : ℕ) → ZMod (p ^ (m + 1))) n := by apply Submission.Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_padic_completion_rat_iso_fraction_field_padic_int_limit.PadicIntLimitSubring_one_mem <;> assumption


theorem PadicIntLimitSubring_add_mem (p : ℕ) [Fact (Nat.Prime p)]
    (a b : (m : ℕ) → ZMod (p ^ (m + 1)))
    (ha : ∀ n : ℕ, padicIntLimitTransition p n (a (n + 1)) = a n)
    (hb : ∀ n : ℕ, padicIntLimitTransition p n (b (n + 1)) = b n) :
    ∀ n : ℕ, padicIntLimitTransition p n ((a + b) (n + 1)) = (a + b) n := by apply Submission.Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_padic_completion_rat_iso_fraction_field_padic_int_limit.PadicIntLimitSubring_add_mem <;> assumption


theorem PadicIntLimitSubring_neg_mem (p : ℕ) [Fact (Nat.Prime p)]
    (a : (m : ℕ) → ZMod (p ^ (m + 1)))
    (ha : ∀ n : ℕ, padicIntLimitTransition p n (a (n + 1)) = a n) :
    ∀ n : ℕ, padicIntLimitTransition p n ((-a) (n + 1)) = (-a) n := by apply Submission.Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_padic_completion_rat_iso_fraction_field_padic_int_limit.PadicIntLimitSubring_neg_mem <;> assumption


theorem PadicIntLimitSubring_mul_mem (p : ℕ) [Fact (Nat.Prime p)]
    (a b : (m : ℕ) → ZMod (p ^ (m + 1)))
    (ha : ∀ n : ℕ, padicIntLimitTransition p n (a (n + 1)) = a n)
    (hb : ∀ n : ℕ, padicIntLimitTransition p n (b (n + 1)) = b n) :
    ∀ n : ℕ, padicIntLimitTransition p n ((a * b) (n + 1)) = (a * b) n := by apply Submission.Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_padic_completion_rat_iso_fraction_field_padic_int_limit.PadicIntLimitSubring_mul_mem <;> assumption










def PadicIntLimitSubring (p : ℕ) [Fact (Nat.Prime p)] :
    Subring ((n : ℕ) → ZMod (p ^ (n + 1))) where
  carrier :=
    { x | ∀ n : ℕ,
        padicIntLimitTransition p n (x (n + 1)) = x n }
  zero_mem' := fun n => PadicIntLimitSubring_zero_mem p n
  one_mem' := fun n => PadicIntLimitSubring_one_mem p n
  add_mem' := fun {a b} ha hb => PadicIntLimitSubring_add_mem p a b ha hb
  neg_mem' := fun {a} ha => PadicIntLimitSubring_neg_mem p a ha
  mul_mem' := fun {a b} ha hb => PadicIntLimitSubring_mul_mem p a b ha hb


abbrev PadicIntLimit (p : ℕ) [Fact (Nat.Prime p)] : Type :=
  PadicIntLimitSubring p

instance instIsDomainPadicIntLimit (p : ℕ) [Fact (Nat.Prime p)] :
    IsDomain (PadicIntLimit p) := by apply Submission.Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_padic_completion_rat_iso_fraction_field_padic_int_limit.instIsDomainPadicIntLimit <;> assumption





theorem padic_completion_rat_iso_fraction_field_padic_int_limit
    (p : ℕ) [Fact (Nat.Prime p)] :
    Nonempty (ℚ_[p] ≃+* FractionRing (PadicIntLimit p)) := by apply Submission.Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_padic_completion_rat_iso_fraction_field_padic_int_limit.padic_completion_rat_iso_fraction_field_padic_int_limit <;> assumption

end Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_padic_completion_rat_iso_fraction_field_padic_int_limit

end