import Mathlib























open scoped BigOperators

universe u v

namespace Autoform_Noncommutative_Algebra_noncomm_alg_theorem_22_9_amitsur_levitzki

noncomputable section








def orderedProduct
    {A : Type u} [Monoid A]
    {m : ℕ}
    (x : Fin m → A) : A :=
  (List.ofFn x).prod







def permutationSignScalar
    (R : Type u) [CommRing R]
    {m : ℕ}
    (σ : Equiv.Perm (Fin m)) : R :=
  (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R)








def standardPolynomial
    (R : Type u) [CommRing R]
    (m : ℕ) :
    FreeAlgebra R (Fin m) :=
  ∑ σ : Equiv.Perm (Fin m),
    permutationSignScalar R σ •
      orderedProduct
        (fun i : Fin m => FreeAlgebra.ι R (σ i))








def IsPolynomialIdentityForMatrices
    (R : Type u) [CommRing R]
    (n vars : ℕ)
    (p : FreeAlgebra R (Fin vars)) : Prop :=
  ∀ x : Fin vars → Matrix (Fin n) (Fin n) R,
    ((FreeAlgebra.lift R) x) p = 0












def noncommutativePolynomialSupport
    (R : Type u) [CommRing R]
    (X : Type v)
    (p : FreeAlgebra R X) :
    Finset (FreeMonoid X) :=
  (((FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := R) (X := X)) p).coeff).support





def IsHomogeneousNoncommutativePolynomial
    (R : Type u) [CommRing R]
    (X : Type v)
    (d : ℕ)
    (p : FreeAlgebra R X) : Prop :=
  ∀ w : FreeMonoid X,
    w ∈ noncommutativePolynomialSupport R X p →
      FreeMonoid.length w = d



end

end Autoform_Noncommutative_Algebra_noncomm_alg_theorem_22_9_amitsur_levitzki
