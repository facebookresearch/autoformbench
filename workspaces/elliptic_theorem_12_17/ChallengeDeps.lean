import Mathlib



























noncomputable section

open scoped TensorProduct
open MvPolynomial

universe u

namespace Autoform_Elliptic_Curves_elliptic_theorem_12_17

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  [Algebra.IsAlgebraic k K] [IsAlgClosed K]







def curveIdeal (W : WeierstrassCurve k) :
    Ideal (MvPolynomial (Fin 3) k) :=
  Ideal.span ({W.toProjective.polynomial} : Set (MvPolynomial (Fin 3) k))










abbrev baseChangeProjective (W : WeierstrassCurve k) :
    WeierstrassCurve.Projective K :=
  (W.map (algebraMap k K)).toProjective




abbrev GeomPoint (W : WeierstrassCurve k) : Type u :=
  (baseChangeProjective (K := K) W).Point





def evalBaseChanged (p : MvPolynomial (Fin 3) k) (P : Fin 3 → K) : K :=
  MvPolynomial.eval P (MvPolynomial.map (algebraMap k K) p)








structure ProjectiveTriple (W₁ : WeierstrassCurve k) where
  coord : Fin 3 → MvPolynomial (Fin 3) k
  degree : ℕ
  homogeneous : ∀ i, MvPolynomial.IsHomogeneous (coord i) degree
  not_all_in_source_ideal : ∃ i, coord i ∉ curveIdeal W₁

namespace ProjectiveTriple


def eval {W₁ : WeierstrassCurve k}
    (τ : ProjectiveTriple W₁) (P : Fin 3 → K) : Fin 3 → K :=
  fun i => evalBaseChanged (K := K) (τ.coord i) P








def subst {W₁ : WeierstrassCurve k}
    (τ : ProjectiveTriple W₁) (p : MvPolynomial (Fin 3) k) :
    MvPolynomial (Fin 3) k :=
  (MvPolynomial.eval₂Hom
    (MvPolynomial.C : k →+* MvPolynomial (Fin 3) k)
    τ.coord) p

end ProjectiveTriple







structure RationalMapData (W₁ W₂ : WeierstrassCurve k) where
  triple : ProjectiveTriple W₁
  maps_equation :
    triple.subst W₂.toProjective.polynomial ∈ curveIdeal W₁

namespace RationalMapData





def Equivalent {W₁ W₂ : WeierstrassCurve k}
    (ρ σ : RationalMapData W₁ W₂) : Prop :=
  ∀ i j : Fin 3,
    ρ.triple.coord i * σ.triple.coord j -
      σ.triple.coord i * ρ.triple.coord j ∈ curveIdeal W₁









def IsDefinedAt {W₁ W₂ : WeierstrassCurve k}
    (ρ : RationalMapData W₁ W₂) (P : Fin 3 → K) : Prop :=
  ∃ σ : RationalMapData W₁ W₂,
    Equivalent ρ σ ∧
      ∃ i : Fin 3, (σ.triple.eval (K := K) P) i ≠ 0

end RationalMapData









namespace RationalMap

end RationalMap



























structure QField where
  carrier : Type u
  [instField : Field carrier]
  [instAlgebra : Algebra ℚ carrier]

attribute [instance] QField.instField
attribute [instance] QField.instAlgebra









def IsImaginaryQuadraticField (L : QField.{u}) : Prop :=
  FiniteDimensional ℚ L.carrier ∧
    Module.finrank ℚ L.carrier = 2 ∧
      ∃ α : L.carrier,
        Algebra.adjoin ℚ ({α} : Set L.carrier) = ⊤ ∧
          ∃ a : ℚ, a < 0 ∧ α ^ 2 = algebraMap ℚ L.carrier a




def IsRationalEnd0 (A : Type u) [Ring A] [Algebra ℚ A] : Prop :=
  Nonempty (A ≃ₐ[ℚ] ℚ)




def IsImaginaryQuadraticEnd0
    (A : Type u) [Ring A] [Algebra ℚ A] : Prop :=
  ∃ L : QField.{u},
    IsImaginaryQuadraticField L ∧
      Nonempty (A ≃ₐ[ℚ] L.carrier)








def IsNegativeQuaternionEnd0
    (A : Type u) [Ring A] [Algebra ℚ A] : Prop :=
  ∃ a b : ℚ,
    a < 0 ∧ b < 0 ∧
      Nonempty (A ≃ₐ[ℚ] QuaternionAlgebra ℚ a 0 b)




def ExactlyOneOfThree (P Q R : Prop) : Prop :=
  (P ∨ Q ∨ R) ∧
    (P → ¬ Q ∧ ¬ R) ∧
      (Q → ¬ P ∧ ¬ R) ∧
        (R → ¬ P ∧ ¬ Q)




def End0Classification
    (A : Type u) [Ring A] [Algebra ℚ A] : Prop :=
  ExactlyOneOfThree
    (IsRationalEnd0 A)
    (IsImaginaryQuadraticEnd0 A)
    (IsNegativeQuaternionEnd0 A)



end Autoform_Elliptic_Curves_elliptic_theorem_12_17

end