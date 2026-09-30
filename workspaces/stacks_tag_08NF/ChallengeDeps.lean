import Mathlib

open CategoryTheory

universe uC vC u₁ v₁ u₂ v₂

namespace Autoform_Stacks_Project_stacks_tag_08NF




def IsFibred1MorphismOver {B : Type uC} {E₁ : Type u₁} {E₂ : Type u₂}
    [Category.{vC, uC} B] [Category.{v₁, u₁} E₁] [Category.{v₂, u₂} E₂]
    (p₁ : E₁ ⥤ B) (p₂ : E₂ ⥤ B) (F : E₁ ⥤ E₂) : Prop :=
  F ⋙ p₂ = p₁ ∧
    ∀ ⦃R S : B⦄ ⦃a b : E₁⦄ ⦃f : R ⟶ S⦄ ⦃φ : a ⟶ b⦄,
      p₁.IsStronglyCartesian f φ →
        p₂.IsStronglyCartesian f (F.map φ)

section

variable {C : Type uC} [Category.{vC, uC} C]



end

end Autoform_Stacks_Project_stacks_tag_08NF


