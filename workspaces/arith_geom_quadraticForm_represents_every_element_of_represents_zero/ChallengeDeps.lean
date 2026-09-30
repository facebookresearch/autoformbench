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
