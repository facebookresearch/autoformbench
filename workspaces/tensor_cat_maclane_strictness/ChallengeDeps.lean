import Mathlib

open CategoryTheory
open scoped MonoidalCategory

universe v u

namespace Autoform_Tensor_Categories_tensor_cat_maclane_strictness



class IsStrictMonoidalCategory (C : Type u) [Category.{v} C] [MonoidalCategory C] : Prop where
  tensorUnit_tensor (X : C) : 𝟙_ C ⊗ X = X
  tensor_tensorUnit (X : C) : X ⊗ 𝟙_ C = X
  tensor_assoc (X Y Z : C) : (X ⊗ Y) ⊗ Z = X ⊗ (Y ⊗ Z)
  leftUnitor_eq (X : C) : (λ_ X).hom = eqToHom (tensorUnit_tensor X)
  rightUnitor_eq (X : C) : (ρ_ X).hom = eqToHom (tensor_tensorUnit X)
  associator_eq (X Y Z : C) : (α_ X Y Z).hom = eqToHom (tensor_assoc X Y Z)



end Autoform_Tensor_Categories_tensor_cat_maclane_strictness
