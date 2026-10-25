import Mathlib
import Aesop
import utils.extract_exists_witness
open BigOperators Classical ENNReal Equiv EuclideanGeometry Filter Finset Fintype Function Lex List MeasureTheory Nat ProbabilityTheory Real SimpleGraph Real Nat Topology Rat
set_option maxHeartbeats 0
theorem P2026AIMEII_8 : ∃ (P2026AIMEII_8_answer : Nat), (IsLeast {x : ℕ | ∃ (y : ℕ) (z : ℕ), (0 : ℕ) < x ∧ (0 : ℕ) < y ∧ (0 : ℕ) < z ∧ y < (2 : ℕ) * x ∧ z ^ (2 : ℕ) * ((2 : ℕ) * x + y) = x * y ^ (2 : ℕ) ∧ (6 : ℕ) * ((2 : ℕ) * x + y) = (125 : ℕ) * (y + (2 : ℕ) * z)} (P2026AIMEII_8_answer)) := by
  let S : Set ℕ := {x : ℕ | ∃ (y : ℕ) (z : ℕ),
    (0 : ℕ) < x ∧ (0 : ℕ) < y ∧ (0 : ℕ) < z ∧
    y < (2 : ℕ) * x ∧
    z ^ (2 : ℕ) * ((2 : ℕ) * x + y) = x * y ^ (2 : ℕ) ∧
    (6 : ℕ) * ((2 : ℕ) * x + y) = (125 : ℕ) * (y + (2 : ℕ) * z)}
  refine ⟨sInf S, ?_⟩
  have h : S.Nonempty := ⟨490, 20, 14, by norm_num [S]⟩
  exact ⟨Nat.sInf_mem h, fun y hy => Nat.sInf_le hy⟩

#extract_first_exists_witness P2026AIMEII_8
#check_first_exists_witness_canonical P2026AIMEII_8
  with admissible_vocabulary := [``OfNat.ofNat]
    allow_quantifier := false

#isCanonical (sInf {x : ℕ | ∃ (y : ℕ) (z : ℕ),
    (0 : ℕ) < x ∧ (0 : ℕ) < y ∧ (0 : ℕ) < z ∧
    y < (2 : ℕ) * x ∧
    z ^ (2 : ℕ) * ((2 : ℕ) * x + y) = x * y ^ (2 : ℕ) ∧
    (6 : ℕ) * ((2 : ℕ) * x + y) = (125 : ℕ) * (y + (2 : ℕ) * z)}) with admissible_vocabulary := [``ofNat.ofNat]
