import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Data.ZMod.Basic
import Submission.Helpers
import ChallengeDeps

namespace Submission

open _root_.Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_padic_completion_rat_iso_fraction_field_padic_int_limit
noncomputable section

namespace Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_padic_completion_rat_iso_fraction_field_padic_int_limit



theorem padicIntLimitTransition_dvd (p n : ℕ) : p ^ (n + 1) ∣ p ^ (n + 2) := by
  sorry





def padicIntLimitTransition (p n : ℕ) :
    ZMod (p ^ (n + 2)) →+* ZMod (p ^ (n + 1)) :=
  ZMod.castHom
    (padicIntLimitTransition_dvd p n)
      
    (ZMod (p ^ (n + 1)))

theorem PadicIntLimitSubring_zero_mem (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) :
    padicIntLimitTransition p n ((0 : (m : ℕ) → ZMod (p ^ (m + 1))) (n + 1))
      = (0 : (m : ℕ) → ZMod (p ^ (m + 1))) n := by
  sorry


theorem PadicIntLimitSubring_one_mem (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) :
    padicIntLimitTransition p n ((1 : (m : ℕ) → ZMod (p ^ (m + 1))) (n + 1))
      = (1 : (m : ℕ) → ZMod (p ^ (m + 1))) n := by
  sorry


theorem PadicIntLimitSubring_add_mem (p : ℕ) [Fact (Nat.Prime p)]
    (a b : (m : ℕ) → ZMod (p ^ (m + 1)))
    (ha : ∀ n : ℕ, padicIntLimitTransition p n (a (n + 1)) = a n)
    (hb : ∀ n : ℕ, padicIntLimitTransition p n (b (n + 1)) = b n) :
    ∀ n : ℕ, padicIntLimitTransition p n ((a + b) (n + 1)) = (a + b) n := by
  sorry


theorem PadicIntLimitSubring_neg_mem (p : ℕ) [Fact (Nat.Prime p)]
    (a : (m : ℕ) → ZMod (p ^ (m + 1)))
    (ha : ∀ n : ℕ, padicIntLimitTransition p n (a (n + 1)) = a n) :
    ∀ n : ℕ, padicIntLimitTransition p n ((-a) (n + 1)) = (-a) n := by
  sorry


theorem PadicIntLimitSubring_mul_mem (p : ℕ) [Fact (Nat.Prime p)]
    (a b : (m : ℕ) → ZMod (p ^ (m + 1)))
    (ha : ∀ n : ℕ, padicIntLimitTransition p n (a (n + 1)) = a n)
    (hb : ∀ n : ℕ, padicIntLimitTransition p n (b (n + 1)) = b n) :
    ∀ n : ℕ, padicIntLimitTransition p n ((a * b) (n + 1)) = (a * b) n := by
  sorry










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
    IsDomain (PadicIntLimit p) := by
  sorry





theorem padic_completion_rat_iso_fraction_field_padic_int_limit
    (p : ℕ) [Fact (Nat.Prime p)] :
    Nonempty (ℚ_[p] ≃+* FractionRing (PadicIntLimit p)) := by
  sorry

end Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_padic_completion_rat_iso_fraction_field_padic_int_limit


end
end Submission