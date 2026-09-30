import ChallengeDeps
import Submission.Helpers

open Autoform_Lie_groups_lie_algebras_lie_theorem_4_1.Theorem41
open scoped Manifold

namespace Submission

theorem theorem_4_1 {n : WithTop ℕ∞}
    {𝕜 : Type*} [RCLike 𝕜]
    {EG HG EH HH G : Type*}
    [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [FiniteDimensional 𝕜 EG]
    [TopologicalSpace HG]
    [NormedAddCommGroup EH] [NormedSpace 𝕜 EH] [FiniteDimensional 𝕜 EH]
    [TopologicalSpace HH]
    (IG : ModelWithCorners 𝕜 EG HG)
    (IH : ModelWithCorners 𝕜 EH HH)
    [Group G] [TopologicalSpace G] [T2Space G] [SecondCountableTopology G]
    [ChartedSpace HG G] [LieGroup IG n G] [BoundarylessManifold IG G]
    (H : Subgroup G)
    [T2Space H] [SecondCountableTopology H]
    [ChartedSpace HH H] [LieGroup IH n H] [BoundarylessManifold IH H]
    {m k : ℕ}
    (hGdim : Module.finrank 𝕜 EG = m)
    (hHdim : Module.finrank 𝕜 EH = k)
    (hClosed : IsClosedLieSubgroup (n := n) IG IH H)
    (hn : 1 ≤ n)
    (hkn : k ≤ m) :
    ∃ Q : QuotientModel 𝕜 (m - k),
      Nonempty (HomogeneousSpaceResult (n := n) IG IH H Q) := by
  sorry

end Submission
