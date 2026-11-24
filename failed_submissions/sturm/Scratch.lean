```lean
import Mathlib

namespace Aux

def scLast : List Bool → Bool
  | [] => false
  | [a] => a
  | _ :: b :: rest => scLast (b :: rest)

def scAux : List Bool → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => scAux (b :: rest) + (if a = b then 0 else 1)

theorem scAux_cons_cons : ∀ (l : List Bool) (x y : Bool),
    scAux (x :: y :: l) = scAux (y :: l) + (if x = y then 0 else 1) :=
  fun l x y => rfl

theorem falseEq (b : Bool) : (if false = b then (0 : ℕ) else 1) = (if b then 1 else 0) := by
  cases b <;> rfl

end Aux
```
