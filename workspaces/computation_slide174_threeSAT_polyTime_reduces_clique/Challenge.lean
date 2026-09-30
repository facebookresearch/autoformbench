import ChallengeDeps

open Autoform_Introduction_to_the_Theory_of_Computation_computation_slide174_threeSAT_polyTime_reduces_clique

universe u v

theorem slide174_threeSAT_polyTime_reduces_clique :
    Nonempty (ThreeSAT ≤ₚ[encodeThreeCNF, CliqueInstance.encode] CLIQUE) := by
  sorry
