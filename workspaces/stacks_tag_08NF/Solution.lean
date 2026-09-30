import ChallengeDeps
import Submission

open Autoform_Stacks_Project_stacks_tag_08NF
open CategoryTheory

universe uC vC u v

variable {C : Type uC} [Category.{vC, uC} C]

theorem tag_08NF (X Y : Type u) [Category.{v, u} X] [Category.{v, u} Y]
    (p₁ : X ⥤ C) [p₁.IsFibered]
    (p₂ : Y ⥤ C) [p₂.IsFibered]
    (F : X ⥤ Y)
    (hF : IsFibred1MorphismOver p₁ p₂ F) :
    ∃ (X' : Type (max u v)) (_inst : Category.{v, max u v} X') (p₃ : X' ⥤ C),
      p₃.IsFibered ∧
      ∃ (u' : X ⥤ X') (v' : X' ⥤ Y) (w : X' ⥤ X),
        IsFibred1MorphismOver p₁ p₃ u' ∧
        IsFibred1MorphismOver p₃ p₁ w ∧
        IsFibred1MorphismOver p₃ p₂ v' ∧
        F = u' ⋙ v' ∧
        Functor.Full u' ∧
        Functor.Faithful u' ∧
        Nonempty (w ⊣ u') ∧
        v'.IsFibered := by
  exact Submission.tag_08NF X Y p₁ p₂ F hF
