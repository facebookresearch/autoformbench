import Mathlib

universe u

theorem isContextFree_inf_isRegular {α : Type u} [Finite α] {A B : Language α}
    (hA : A.IsContextFree) (hB : B.IsRegular) :
    (A ⊓ B).IsContextFree := by
  sorry
