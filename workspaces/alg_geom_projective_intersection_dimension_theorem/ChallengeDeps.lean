import Mathlib

open Set
open MvPolynomial

noncomputable section

universe u

namespace Autoform_Algebraic_Geometry_I_alg_geom_projective_intersection_dimension_theorem








abbrev ProjectiveSpace (k : Type u) [Field k] (n : ℕ) : Type u :=
  Projectivization k (Fin (n + 1) → k)











structure HomogeneousPolynomial (k : Type u) [CommSemiring k] (n : ℕ) where
  degree : ℕ
  poly : MvPolynomial (Fin (n + 1)) k
  homogeneous : MvPolynomial.IsHomogeneous poly degree

namespace HomogeneousPolynomial

variable {k : Type u} [Field k] {n : ℕ}








def VanishesAt (f : HomogeneousPolynomial k n) (x : ProjectiveSpace k n) : Prop :=
  ∀ (v : Fin (n + 1) → k) (hv : v ≠ 0),
    Projectivization.mk k v hv = x →
      (MvPolynomial.eval v) f.poly = 0

end HomogeneousPolynomial









def ProjectiveZariskiClosed
    (k : Type u) [Field k] (n : ℕ)
    (Z : Set (ProjectiveSpace k n)) : Prop :=
  ∃ equations : Set (HomogeneousPolynomial k n),
    Z = { x : ProjectiveSpace k n |
      ∀ f ∈ equations, HomogeneousPolynomial.VanishesAt f x }








def projectiveZariskiTopology
    (k : Type u) [Field k] (n : ℕ) :
    TopologicalSpace (ProjectiveSpace k n) :=
  TopologicalSpace.generateFrom
    { U : Set (ProjectiveSpace k n) |
      ∃ Z : Set (ProjectiveSpace k n),
        ProjectiveZariskiClosed k n Z ∧ U = Zᶜ }










structure ProjectiveSubvariety
    (k : Type u) [Field k] (n : ℕ) where
  carrier : Set (ProjectiveSpace k n)
  zariskiClosed : ProjectiveZariskiClosed k n carrier
  irreducible :
    @IsIrreducible
      (ProjectiveSpace k n)
      (projectiveZariskiTopology k n)
      carrier

namespace ProjectiveSubvariety

variable {k : Type u} [Field k] {n : ℕ}









def dim (X : ProjectiveSubvariety k n) : WithBot ℕ∞ := by
  letI : TopologicalSpace (ProjectiveSpace k n) :=
    projectiveZariskiTopology k n
  exact topologicalKrullDim X.carrier

end ProjectiveSubvariety







def projectiveSetDim
    (k : Type u) [Field k] (n : ℕ)
    (Z : Set (ProjectiveSpace k n)) : WithBot ℕ∞ := by
  letI : TopologicalSpace (ProjectiveSpace k n) :=
    projectiveZariskiTopology k n
  exact topologicalKrullDim Z











def IsIrreducibleComponentOf
    (k : Type u) [Field k] (n : ℕ)
    (S Z : Set (ProjectiveSpace k n)) : Prop := by
  letI : TopologicalSpace (ProjectiveSpace k n) :=
    projectiveZariskiTopology k n
  exact
    ∃ C : Set S,
      C ∈ irreducibleComponents S ∧
        Z = Subtype.val '' C

namespace ProjectiveSubvariety




def intersection
    {k : Type u} [Field k] {n : ℕ}
    (X Y : ProjectiveSubvariety k n) :
    Set (ProjectiveSpace k n) :=
  X.carrier ∩ Y.carrier

end ProjectiveSubvariety



end Autoform_Algebraic_Geometry_I_alg_geom_projective_intersection_dimension_theorem
