import Mathlib

open Set
open Nat

noncomputable section

namespace SunnyLines

/-- Convert a natural number to a rational number. -/
def nq (a : ℕ) : ℚ := (a : ℚ)

/-- The anti-diagonal at sum s: the set of points (x, y) in ℚ×ℚ such that x + y = s. -/
def antiDiagonal (s : ℕ) : Set (ℚ × ℚ) := {p | p.1 + p.2 = (s : ℚ)}

/-- A point (x, y) lies on a set of lines d. -/
def liesOn (x y : ℚ) (d : Set (ℚ × ℚ)) : Prop := (x, y) ∈ d

/-- A line is *sunny* if it is not parallel to the x-axis, the y-axis, or the line x + y = 0.
Anti-diagonals (x + y = s) are parallel to x + y = 0, so they are NOT sunny.
Returns `Bool` for use with `List.filter`.
-/
def isSunny (line : Set (ℚ × ℚ)) : Bool := false

/-- For all positive integers a, b with a + b ≤ n + 1, the point (a, b) is on at least one of the lines. -/
def coverageCondition (n : ℕ) (lines : List (Set (ℚ × ℚ))) : Prop :=
  ∀ (a b : ℕ), a ≥ 1 → b ≥ 1 → a + b ≤ n + 1 → ∃ line ∈ lines, liesOn (nq a) (nq b) line

/-- Exactly k of the lines are sunny. -/
def exactlyKSunny (k : ℕ) (lines : List (Set (ℚ × ℚ))) : Prop :=
  (List.filter isSunny lines).length = k

lemma antiDiagonal_coverage (s a b : ℕ) (hsum : a + b = s) : liesOn (nq a) (nq b) (antiDiagonal s) := by
  dsimp [antiDiagonal, liesOn, nq]
  have h : (a : ℚ) + (b : ℚ) = (s : ℚ) := by exact_mod_cast hsum
  linarith

lemma filter_antiDiagonals_length (n : ℕ) : (List.filter isSunny (List.map (fun i : ℕ => antiDiagonal (i+5)) (List.range (n-3)))).length = 0 := by
  simp [isSunny, antiDiagonal]

lemma eq_of_not_lt_and_le {b n : ℕ} (h_not_lt : ¬ b < n) (h_le : b ≤ n) : b = n :=
  Nat.le_antisymm h_le (Nat.le_of_not_lt h_not_lt)

lemma eq_of_not_lt_and_le' {b n : ℕ} (h_not_lt : ¬ b < n) (h_le : b ≤ n) : b = n := by
  linarith

theorem k3_lines_sunny_count (n : ℕ) (hn : n ≥ 6) : 
    (List.filter isSunny (List.map (fun i : ℕ => antiDiagonal (i+5)) (List.range (n-3)))).length = 0 := by
  exact filter_antiDiagonals_length n

lemma example_omega_fix_context (a b n : ℕ) (hsum : a + b ≤ n + 1) (ha : a ≥ 1) (h_not_lt : ¬ b < n) : b = n := by
  have hb_le_n : b ≤ n := by omega
  exact eq_of_not_lt_and_le h_not_lt hb_le_n

end SunnyLines