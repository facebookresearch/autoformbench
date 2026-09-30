import Mathlib

noncomputable section

open Set
open scoped Manifold

namespace Autoform_Elliptic_Curves_elliptic_theorem_18_10
































abbrev SL2Z : Type := Matrix.SpecialLinearGroup (Fin 2) ℤ








abbrev Cusp : Type := Option ℚ

namespace Cusp


def infinity : Cusp := none


def entry (g : SL2Z) (i j : Fin 2) : ℚ :=
  ((g : Matrix (Fin 2) (Fin 2) ℤ) i j : ℚ)







def cuspSMul (g : SL2Z) : Cusp → Cusp
  | none =>
      
      if entry g 1 0 = 0 then
        none
      else
        some (entry g 0 0 / entry g 1 0)
  | some x =>
      
      let denom : ℚ := entry g 1 0 * x + entry g 1 1
      if denom = 0 then
        none
      else
        some ((entry g 0 0 * x + entry g 0 1) / denom)

end Cusp





namespace Cusp


end Cusp







inductive HStar : Type
  | upper : UpperHalfPlane → HStar
  | cusp : Cusp → HStar

namespace HStar







def upperDisc (z₀ : UpperHalfPlane) (r : ℝ) : Set HStar :=
  {p | ∃ z : UpperHalfPlane, p = HStar.upper z ∧ dist (z : ℂ) (z₀ : ℂ) < r}







def tangentDiscAtCusp (q : ℚ) (r : ℝ) : Set HStar :=
  {HStar.cusp (some q)} ∪
    {p | ∃ z : UpperHalfPlane,
      p = HStar.upper z ∧
        dist (z : ℂ) ((q : ℂ) + (r : ℂ) * Complex.I) < r}








def infinityNeighborhood (r : ℝ) : Set HStar :=
  {HStar.cusp Cusp.infinity} ∪
    {p | ∃ z : UpperHalfPlane, p = HStar.upper z ∧ r < z.im}







def hStarNeighborhoods : Set (Set HStar) :=
  {U | ∃ z₀ : UpperHalfPlane, ∃ r : ℝ, 0 < r ∧ U = upperDisc z₀ r} ∪
  {U | ∃ q : ℚ, ∃ r : ℝ, 0 < r ∧ U = tangentDiscAtCusp q r} ∪
  {U | ∃ r : ℝ, 0 < r ∧ U = infinityNeighborhood r}







@[reducible] def hStarTopologicalSpace : TopologicalSpace HStar :=
  TopologicalSpace.generateFrom hStarNeighborhoods

instance instTopologicalSpace : TopologicalSpace HStar :=
  hStarTopologicalSpace


end HStar











def IsRiemannSurface (X : Type*) [TopologicalSpace X] : Prop :=
  ConnectedSpace X ∧
  T2Space X ∧
  SecondCountableTopology X ∧
  ∃ c : ChartedSpace ℂ X,
    letI : ChartedSpace ℂ X := c
    IsManifold (𝓘(ℂ, ℂ)) ⊤ X












noncomputable abbrev SingularHomologyZ
    (n : ℕ) (X : Type) [TopologicalSpace X] : ModuleCat ℤ :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)













def HasTopologicalGenus (X : Type) [TopologicalSpace X] (g : ℕ) : Prop :=
  Nonempty (↑(SingularHomologyZ 1 X) ≃ₗ[ℤ] (Fin (2 * g) → ℤ))



end Autoform_Elliptic_Curves_elliptic_theorem_18_10

end