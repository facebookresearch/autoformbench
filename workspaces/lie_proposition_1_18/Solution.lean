import ChallengeDeps
import Submission

open Autoform_Lie_groups_lie_algebras_lie_proposition_1_18

universe uK uE uH uE2 uH2 uM uN

variable {𝕜 : Type uK} [RCLike 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {E' : Type uE2} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH2} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]

theorem proposition_1_18
    {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
    {I' : ModelWithCorners 𝕜 E' H'} [I'.Boundaryless]
    {n : WithTop ℕ∞}
    [IsManifold I n M] [IsManifold I' n N]
    [T2Space M] [SecondCountableTopology M]
    [T2Space N] [SecondCountableTopology N]
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E']
    (hn : (1 : WithTop ℕ∞) ≤ n)
    {f : M → N} (hf : IsSubmersion I I' n f) (q : N) :
    LevelSetIsManifoldOfExpectedDimension I I' n f q := by
  exact Submission.proposition_1_18 hn hf q
