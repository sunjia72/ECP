import Mathlib
import Aesop
open BigOperators Classical ENNReal Equiv EuclideanGeometry Filter Finset Fintype Function Lex List MeasureTheory Nat ProbabilityTheory Real SimpleGraph Real Nat Topology Rat
set_option maxHeartbeats 0
theorem P2026AIMEII_4 : ∃ (P2026AIMEII_4_answer : Nat), (#({n ∈ Finset.range (1000 : ℕ) | (0 : ℕ) < n ∧ let hundreds := n / (100 : ℕ); let tens := n / (10 : ℕ) % (10 : ℕ); let ones := n % (10 : ℕ); let b := hundreds.max (tens.max ones) + (1 : ℕ); hundreds * b ^ (2 : ℕ) + tens * b + ones = n}) = P2026AIMEII_4_answer) := by
  use (279 : Nat)
  try native_decide
  try simp
  try aesop
  try nlinarith
  try ring
  try norm_num
