import ChallengeDeps
import Submission

open Autoform_Algebraic_Topology_I_alg_top_theorem62
open CategoryTheory Limits AlgebraicTopology

theorem theorem62 :
    ∃ cross : CrossFamily,
      CrossNatural cross ∧
      CrossAddLeft cross ∧
      CrossAddRight cross ∧
      CrossLeibniz cross ∧
      CrossNormalizedLeft cross ∧
      CrossNormalizedRight cross := by
  exact Submission.theorem62
