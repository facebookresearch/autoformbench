import ChallengeDeps
import Submission.Helpers

open Autoform_Buildings_and_Classical_Groups_buildings_further_bruhatTits_doubleCoset_bijection

universe u v w

variable {G : Type u} [Group G] {ι : Type v} {M : CoxeterMatrix ι}

namespace Submission

theorem further_bruhatTits_doubleCoset_bijection (bn : StrictBNPair G ι M) [Fintype ι]
    (h_building : Nonempty (BuildingOrigin.{u, v, w} bn)) (I J : Set ι) :
    ∃ e : weylDoubleCosetSpace bn I J ≃ parabolicDoubleCosetSpace bn I J,
      ∀ (w₀ : WeylGroup bn) (n : bn.N),
        QuotientGroup.mk' (T bn) n = w₀ →
          e ⟨weylDoubleCoset bn I J w₀, ⟨w₀, rfl⟩⟩ =
            ⟨parabolicDoubleCosetOfRepresentative bn I J n, ⟨(n : G), rfl⟩⟩ := by
  sorry

end Submission
