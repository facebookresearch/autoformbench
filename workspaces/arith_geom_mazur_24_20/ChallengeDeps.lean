import Mathlib


















noncomputable section

namespace Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_mazur_24_20







def IsMazurCyclicOrder (n : ℕ) : Prop :=
  n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨
    n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 12


def IsMazurProductParameter (n : ℕ) : Prop :=
  n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4








def IsMazurTorsionGroup (G : Type*) [AddCommGroup G] : Prop :=
  (∃ n : ℕ, IsMazurCyclicOrder n ∧ Nonempty (G ≃+ ZMod n)) ∨
    (∃ n : ℕ,
      IsMazurProductParameter n ∧ Nonempty (G ≃+ (ZMod 2 × ZMod (2 * n))))



end Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_mazur_24_20

end