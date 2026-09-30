import Mathlib

namespace Autoform_Elliptic_Curves_elliptic_theorem_3_44





def rabinS (K : Type*) [Fintype K] : ℕ :=
  (Fintype.card K - 1) / 2






def DifferentType {K : Type*} [MonoidWithZero K] [Fintype K] (a b : K) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ a ^ rabinS K ≠ b ^ rabinS K



end Autoform_Elliptic_Curves_elliptic_theorem_3_44
