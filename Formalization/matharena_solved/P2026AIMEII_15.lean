import Mathlib
import Aesop
open BigOperators Classical ENNReal Equiv EuclideanGeometry Filter Finset Fintype Function Lex List MeasureTheory Nat ProbabilityTheory Real SimpleGraph Real Nat Topology Rat
set_option maxHeartbeats 0
theorem P2026AIMEII_15 : ∃ (P2026AIMEII_15_answer : Nat), (#{a : Fin (7 : ℕ) → Fin (3 : ℕ) | let b := fun (i : Fin (7 : ℕ)) => (↑(a i) : ℕ) + (1 : ℕ); (∑ i : Fin (7 : ℕ), b i) % (3 : ℕ) = (0 : ℕ) ∧ (b (0 : Fin (7 : ℕ)) * b (1 : Fin (7 : ℕ)) * b (3 : Fin (7 : ℕ)) + b (1 : Fin (7 : ℕ)) * b (2 : Fin (7 : ℕ)) * b (4 : Fin (7 : ℕ)) + b (2 : Fin (7 : ℕ)) * b (3 : Fin (7 : ℕ)) * b (5 : Fin (7 : ℕ)) + b (3 : Fin (7 : ℕ)) * b (4 : Fin (7 : ℕ)) * b (6 : Fin (7 : ℕ)) + b (4 : Fin (7 : ℕ)) * b (5 : Fin (7 : ℕ)) * b (0 : Fin (7 : ℕ)) + b (5 : Fin (7 : ℕ)) * b (6 : Fin (7 : ℕ)) * b (1 : Fin (7 : ℕ)) + b (6 : Fin (7 : ℕ)) * b (0 : Fin (7 : ℕ)) * b (2 : Fin (7 : ℕ))) % (3 : ℕ) = (0 : ℕ)} = P2026AIMEII_15_answer) := by
  use (393 : Nat)
  try native_decide
  try simp
  try aesop
  try nlinarith
  try ring
  try norm_num
