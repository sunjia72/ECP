import Mathlib
import Aesop
open BigOperators Classical ENNReal Equiv EuclideanGeometry Filter Finset Fintype Function Lex List MeasureTheory Nat ProbabilityTheory Real SimpleGraph Real Nat Topology Rat
set_option maxHeartbeats 0
theorem P2026AIMEI_7 : ∃ (P2026AIMEI_7_answer : Nat), (Fintype.card (↑{perm : Equiv.Perm (Fin (6 : ℕ)) | perm ^ (6 : ℕ) = (1 : Equiv.Perm (Fin (6 : ℕ)))} : Type) = P2026AIMEI_7_answer) := by
  use (396 : Nat)
  try native_decide
  try simp
  try aesop
  try nlinarith
  try ring
  try norm_num
