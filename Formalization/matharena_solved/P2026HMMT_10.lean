import Mathlib
import Aesop
open BigOperators Classical ENNReal Equiv EuclideanGeometry Filter Finset Fintype Function Lex List MeasureTheory Nat ProbabilityTheory Real SimpleGraph Real Nat Topology Rat
set_option maxHeartbeats 0
theorem P2026HMMT_10 : ∃ (P2026HMMT_10_answer : ℕ), ((∑ k ∈ Finset.range (2027 : ℕ), k * ((2 : ℕ) * k).choose k * (2 : ℕ) ^ k) % (2027 : ℕ) = P2026HMMT_10_answer) := by
  use (289 : ℕ)
  try native_decide
  try simp
  try aesop
  try nlinarith
  try ring
  try norm_num
