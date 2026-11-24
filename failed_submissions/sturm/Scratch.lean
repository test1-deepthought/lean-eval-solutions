Verified this turn (isolated auxiliary facts only, not the target):

```lean
import Mathlib

namespace Aux

inductive St where
  | none : St
  | some (b : Bool) : St
  deriving DecidableEq

def scAux : List Bool → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => scAux (b :: rest) + (if a = b then 0 else 1)

example (x y : Bool) : scAux [x, y] = (if x = y then 0 else 1) := by
  show scAux [y] + (if x = y then 0 else 1) = (if x = y then 0 else 1)
  show 0 + (if x = y then 0 else 1) = (if x = y then 0 else 1)
  simp

theorem falseEq (b : Bool) : (if false = b then (0 : ℕ) else 1) = (if b then 1 else 0) := by
  cases b <;> rfl

end Aux
```
