import ChallengeDeps

open Autoform_Tensor_Categories_tensor_cat_preservesProjectiveObjects_of_subquotientSurjective_quasiTensor
open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v₁ v₂ u₁ u₂
universe u v w

variable (k : Type u₁) [Field k] [IsAlgClosed k]

theorem preservesProjectiveObjects_of_subquotientSurjective_quasiTensor (C : Type u₁) (D : Type u₂) [Category.{v₁} C] [Category.{v₂} D]
    [Abelian C] [Linear k C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [Abelian D] [Linear k D] [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear k D]
    [TensorCategory k C] [TensorCategory k D] [kFiniteCategory k C] [kFiniteCategory k D]
    (F : QuasiFiberFunctor k C D)
    (hF : SubquotientSurjective C D F.functor) :
  ∀ P : C, Projective P → Projective (F.functor.obj P) := by
  sorry
