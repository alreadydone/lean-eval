import ChallengeDeps
import Submission.Helpers

open LeanEval.Combinatorics.HoneycombConnectiveConstant
open Filter Topology

namespace Submission

theorem honeycomb_connective_constant :
    Tendsto
      (fun n ↦ (walkCount n : ℝ) ^ (1 / n : ℝ))
      atTop
      (nhds (Real.sqrt (2 + Real.sqrt 2))) := by
  sorry

end Submission
