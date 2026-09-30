import Mathlib

noncomputable section

namespace Autoform_Functions_of_a_Complex_Variable_complex_var_two_circles_mobius_to_concentric

structure Circle where
  center : ℂ
  radius : ℝ
  radius_pos : 0 < radius

namespace Circle

def carrier (C : Circle) : Set ℂ :=
  { z : ℂ | Complex.normSq (z - C.center) = C.radius ^ 2 }

end Circle

structure Mobius where
  a : ℂ
  b : ℂ
  c : ℂ
  d : ℂ
  det_ne_zero : a * d - b * c ≠ 0

namespace Mobius

def apply (M : Mobius) (z : ℂ) : ℂ :=
  (M.a * z + M.b) / (M.c * z + M.d)

def poleFreeOn (M : Mobius) (S : Set ℂ) : Prop :=
  ∀ z : ℂ, z ∈ S → M.c * z + M.d ≠ 0

end Mobius

def mapsCircleOnto (M : Mobius) (C D : Circle) : Prop :=
  M.poleFreeOn C.carrier ∧
    (M.apply) '' C.carrier = D.carrier

def Concentric (C D : Circle) : Prop :=
  C.center = D.center



end Autoform_Functions_of_a_Complex_Variable_complex_var_two_circles_mobius_to_concentric

end
