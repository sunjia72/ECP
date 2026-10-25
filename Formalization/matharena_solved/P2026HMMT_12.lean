import Mathlib
import Aesop
open BigOperators Classical ENNReal Equiv EuclideanGeometry Filter Finset Fintype Function Lex List MeasureTheory Nat ProbabilityTheory Real SimpleGraph Real Nat Topology Rat
set_option maxHeartbeats 0
theorem P2026HMMT_12 : ∃ (P2026HMMT_12_answer : ℚ), (let RollSeq := Fin (4 : ℕ) → Fin (4 : ℕ); let faceValue := fun (f : Fin (4 : ℕ)) => (↑(↑f : ℕ) : ℚ) + (1 : ℚ); let contribution := fun (σ : RollSeq) (t : Fin (4 : ℕ)) => if ∃ u < t, σ u = σ t then (0 : ℚ) else faceValue (σ t); let score := fun (σ : RollSeq) => ∑ t : Fin (4 : ℕ), contribution σ t; (∑ σ : RollSeq, score σ) / (4 : ℚ) ^ (4 : ℕ) = P2026HMMT_12_answer) := by
  use ((875 : ℚ) / 128 : ℚ)
  try native_decide
  try simp
  try aesop
  try nlinarith
  try ring
  try norm_num
