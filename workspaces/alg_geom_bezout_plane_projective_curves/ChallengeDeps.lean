import Mathlib





























open scoped BigOperators

universe u

namespace Autoform_Algebraic_Geometry_I_alg_geom_bezout_plane_projective_curves

noncomputable section

variable {k : Type u} [Field k]










structure PlaneProjectiveCurve (k : Type u) [Field k] where
  poly : MvPolynomial (Fin 3) k
  degree : ℕ
  homogeneous : poly.IsHomogeneous degree
  degree_pos : 0 < degree
  poly_ne_zero : poly ≠ 0





namespace PlaneProjectiveCurve











def HasCommonComponent
    (C D : PlaneProjectiveCurve k) : Prop :=
  ∃ h : MvPolynomial (Fin 3) k,
    h ≠ 0 ∧
    (∃ n : ℕ, 0 < n ∧ h.IsHomogeneous n) ∧
    h ∣ C.poly ∧ h ∣ D.poly

end PlaneProjectiveCurve







theorem exists_coord_ne_zero
    (p : Projectivization k (Fin 3 → k)) :
    ∃ i : Fin 3, p.rep i ≠ 0 := by
  classical
  by_contra h
  exact Projectivization.rep_nonzero p (funext fun i => by
    by_contra hi
    exact h ⟨i, hi⟩)







noncomputable def chartIndex
    (p : Projectivization k (Fin 3 → k)) : Fin 3 :=
  Classical.choose (exists_coord_ne_zero p)






noncomputable def normalizedCoord
    (p : Projectivization k (Fin 3 → k)) (j : Fin 3) : k :=
  p.rep j / p.rep (chartIndex p)







noncomputable def dehomogenizeInChart
    (i : Fin 3) (f : MvPolynomial (Fin 3) k) :
    MvPolynomial (Fin 3) k :=
  (MvPolynomial.aeval fun j : Fin 3 =>
    if j = i then (1 : MvPolynomial (Fin 3) k)
    else MvPolynomial.X j) f





noncomputable def chartEquation
    (p : Projectivization k (Fin 3 → k)) :
    MvPolynomial (Fin 3) k :=
  MvPolynomial.X (chartIndex p) - 1








end

end Autoform_Algebraic_Geometry_I_alg_geom_bezout_plane_projective_curves
