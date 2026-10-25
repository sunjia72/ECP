import Mathlib
import Aesop
open BigOperators Classical ENNReal Equiv EuclideanGeometry Filter Finset Fintype Function Lex List MeasureTheory Nat ProbabilityTheory Real SimpleGraph Real Nat Topology Rat
set_option maxHeartbeats 0
theorem P2026HMMT_14 : ∃ (P2026HMMT_14_answer : ℚ), (let ChoiceSeq := (i : Fin (5 : ℕ)) → Fin ((↑i : ℕ) + (1 : ℕ)); (∑ c : ChoiceSeq, ∏ i : Fin (5 : ℕ), if (↑(c i) : ℕ) = (0 : ℕ) then (1 / 2 : ℚ) else (1 : ℚ)) / (↑(Fintype.card ChoiceSeq) : ℚ) = P2026HMMT_14_answer) := by
  use ((63 / 256 : ℚ) : ℚ)
  try native_decide
  try simp
  try aesop
  try nlinarith
  try ring
  try norm_num
