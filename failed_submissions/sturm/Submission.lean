import ChallengeDeps
import Submission.Helpers

open LeanEval.Algebra
open Polynomial
open Set
open scoped Classical

namespace Submission

def chainEvalsAux (a b : ℝ[X]) (n : ℕ) (x : ℝ) : List ℝ :=
  (sturmAux a b n).map (·.eval x)

def sigmaAux (a b : ℝ[X]) (n : ℕ) (x : ℝ) : ℕ :=
  signChanges (chainEvalsAux a b n x)

lemma sigma_eq_sigmaAux (p : ℝ[X]) (x : ℝ) : sigma p x = sigmaAux p (derivative p) (p.natDegree + 2) x := by
  unfold sigma sigmaAux chainEvalsAux sturmChain; rfl

lemma pderiv_ne_zero_at_root (p : ℝ[X]) (hp : Squarefree p) (r : ℝ) (hr : p.eval r = 0) :
    (derivative p).eval r ≠ 0 :=
  Helpers.eval_derivative_ne_zero_of_squarefree_root p hp r hr

end Submission
