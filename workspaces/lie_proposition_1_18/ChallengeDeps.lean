import Mathlib

noncomputable section

namespace Autoform_Lie_groups_lie_algebras_lie_proposition_1_18

universe uK uE uH uE2 uH2 uM uN







abbrev LevelSet {M : Type uM} {N : Type uN} (f : M → N) (q : N) : Type uM :=
  {x : M // f x = q}

variable {𝕜 : Type uK} [NontriviallyNormedField 𝕜]

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]

variable {E' : Type uE2} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH2} [TopologicalSpace H']

variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]






def DifferentialSurjectiveAt
    (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
    (f : M → N) (x : M) : Prop :=
  ∀ w : TangentSpace I' (f x),
    ∃ v : TangentSpace I x, mfderiv I I' f x v = w








def IsSubmersion
    (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
    (n : WithTop ℕ∞) (f : M → N) : Prop :=
  ContMDiff I I' n f ∧
    ∀ x : M, DifferentialSurjectiveAt I I' f x










structure LevelSetManifoldData
    (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
    (n : WithTop ℕ∞) (f : M → N) (q : N) where
  K : Type uE
  [normedAddCommGroup : NormedAddCommGroup K]
  [normedSpace : NormedSpace 𝕜 K]
  [completeSpace : CompleteSpace K]
  [finiteDimensional : FiniteDimensional 𝕜 K]
  [chartedSpace : ChartedSpace K (LevelSet f q)]
  dim_eq :
    Module.finrank 𝕜 K = Module.finrank 𝕜 E - Module.finrank 𝕜 E'
  isManifold :
    IsManifold (modelWithCornersSelf 𝕜 K) n (LevelSet f q)







def LevelSetIsManifoldOfExpectedDimension
    (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
    (n : WithTop ℕ∞) (f : M → N) (q : N) : Prop :=
  T2Space (LevelSet f q) ∧
    SecondCountableTopology (LevelSet f q) ∧
      Nonempty (LevelSetManifoldData I I' n f q)



end Autoform_Lie_groups_lie_algebras_lie_proposition_1_18
