import Mathlib
import Aesop
open BigOperators Classical ENNReal Equiv EuclideanGeometry Filter Finset Fintype Function Lex List MeasureTheory Nat ProbabilityTheory Real SimpleGraph Real Nat Topology Rat
set_option maxHeartbeats 0
theorem P2026AIMEI_13 : ∃ (P2026AIMEI_13_answer : Nat), (let S := fun (r : ℕ) => ∑ k ∈ Finset.range (10001 : ℕ), if k % (502 : ℕ) = r % (502 : ℕ) then Nat.choose (10000 : ℕ) k else (0 : ℕ); #({r ∈ Finset.range (502 : ℕ) | S r % (503 : ℕ) = (0 : ℕ)}) = P2026AIMEI_13_answer) := by
  use (39 : Nat)
  try native_decide
  try simp
  try aesop
  try nlinarith
  try ring
  try norm_num
