import Mathlib
import Submission.Helpers
import ChallengeDeps
/-!
Regression test for the multi-hole / trusted-helpers pipeline.
-/



namespace Submission

open _root_.Helpers
open _root_.Helpers.WithCompanions
namespace Helpers
def first : Nat := 41
theorem second_eq : first + rootHelper + preHole = first + 141 := by
  show (41 : Nat) + 41 + 100 = 41 + 141
  decide
theorem third_eq : postHole + ({ value := 0 } : WithCompanions).value = 1000 := by
  decide

end Helpers

end Submission
