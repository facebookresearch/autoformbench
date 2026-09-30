import Mathlib

universe u v

open CategoryTheory
open CategoryTheory.Limits

namespace Autoform_Stacks_Project_stacks_lemma_24_1




















structure StacksSite (C : Type u) [Category.{v} C] where
  coverage : Precoverage C
  hasIsos : Precoverage.HasIsos coverage
  hasPullbacks : Precoverage.HasPullbacks coverage
  stableUnderBaseChange : Precoverage.IsStableUnderBaseChange coverage
  stableUnderComposition : Precoverage.IsStableUnderComposition coverage









structure MorphismOfTopoi
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (SC : StacksSite C) (SD : StacksSite D) where
  inverseImage :
    Sheaf SC.coverage.toGrothendieck (Type (max u v)) ⥤
      Sheaf SD.coverage.toGrothendieck (Type (max u v))
  directImage :
    Sheaf SD.coverage.toGrothendieck (Type (max u v)) ⥤
      Sheaf SC.coverage.toGrothendieck (Type (max u v))
  adjunction : inverseImage ⊣ directImage
  leftExact : PreservesFiniteLimits inverseImage



end Autoform_Stacks_Project_stacks_lemma_24_1
