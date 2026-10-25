import Mathlib
import Aesop
open BigOperators Classical ENNReal Equiv EuclideanGeometry Filter Finset Fintype Function Lex List MeasureTheory Nat ProbabilityTheory Real SimpleGraph Real Nat Topology Rat
set_option maxHeartbeats 0
theorem P2026AIMEII_6 : ∃ (P2026AIMEII_6_answer : Nat), ({r : ℝ | (0 : ℝ) < r ∧ ∃ (x : ℝ) (y : ℝ), (2 : ℝ) * y = x ^ (2 : ℕ) - (8 : ℝ) * x + (12 : ℝ) ∧ (x - (4 : ℝ)) ^ (2 : ℕ) + (y - (39 : ℝ)) ^ (2 : ℕ) = r ^ (2 : ℕ) ∧ x - (4 : ℝ) + (y - (39 : ℝ)) * (x - (4 : ℝ)) = (0 : ℝ)} = {(9 : ℝ), (41 : ℝ)} ∧ ∑ r ∈ {(9 : ℝ), (41 : ℝ)}, r = (↑P2026AIMEII_6_answer : ℝ)) := by
  use (50 : Nat)
  have h_subset₁ : {r : ℝ | (0 : ℝ) < r ∧ ∃ (x : ℝ) (y : ℝ), (2 : ℝ) * y = x ^ (2 : ℕ) - (8 : ℝ) * x + (12 : ℝ) ∧ (x - (4 : ℝ)) ^ (2 : ℕ) + (y - (39 : ℝ)) ^ (2 : ℕ) = r ^ (2 : ℕ) ∧ x - (4 : ℝ) + (y - (39 : ℝ)) * (x - (4 : ℝ)) = (0 : ℝ)} ⊆ {(9 : ℝ), (41 : ℝ)} := by
    intro r hr
    have h₁ : (0 : ℝ) < r := hr.1
    have h₂ : ∃ (x : ℝ) (y : ℝ), (2 : ℝ) * y = x ^ (2 : ℕ) - (8 : ℝ) * x + (12 : ℝ) ∧ (x - (4 : ℝ)) ^ (2 : ℕ) + (y - (39 : ℝ)) ^ (2 : ℕ) = r ^ (2 : ℕ) ∧ x - (4 : ℝ) + (y - (39 : ℝ)) * (x - (4 : ℝ)) = (0 : ℝ) := hr.2
    rcases h₂ with ⟨x, y, h₂, h₃, h₄⟩
    have h₅ : x - (4 : ℝ) = 0 ∨ y - (39 : ℝ) = -1 := by
      have h₅₁ : (x - (4 : ℝ)) + (y - (39 : ℝ)) * (x - (4 : ℝ)) = 0 := by simpa using h₄
      have h₅₂ : (x - (4 : ℝ)) * (1 + (y - (39 : ℝ))) = 0 := by linarith
      have h₅₃ : (x - (4 : ℝ)) = 0 ∨ (1 + (y - (39 : ℝ))) = 0 := by
        apply eq_zero_or_eq_zero_of_mul_eq_zero h₅₂
      cases h₅₃ with
      | inl h₅₃ =>
        exact Or.inl h₅₃
      | inr h₅₃ =>
        have h₅₄ : y - (39 : ℝ) = -1 := by linarith
        exact Or.inr h₅₄
    cases h₅ with
    | inl h₅ =>

      have h₆ : x = (4 : ℝ) := by linarith
      have h₇ : (2 : ℝ) * y = (x : ℝ) ^ 2 - (8 : ℝ) * x + (12 : ℝ) := by simpa using h₂
      rw [h₆] at h₇
      have h₈ : (2 : ℝ) * y = (4 : ℝ) ^ 2 - (8 : ℝ) * (4 : ℝ) + (12 : ℝ) := by simpa using h₇
      have h₉ : (2 : ℝ) * y = -4 := by norm_num at h₈ ⊢; linarith
      have h₁₀ : y = -2 := by linarith
      have h₁₁ : (x - (4 : ℝ)) ^ 2 + (y - (39 : ℝ)) ^ 2 = r ^ 2 := by simpa using h₃
      rw [h₆, h₁₀] at h₁₁
      have h₁₂ : ( (4 : ℝ) - (4 : ℝ)) ^ 2 + (-2 - (39 : ℝ)) ^ 2 = r ^ 2 := by simpa using h₁₁
      have h₁₃ : r ^ 2 = (41 : ℝ) ^ 2 := by norm_num at h₁₂ ⊢; nlinarith
      have h₁₄ : r = (41 : ℝ) := by
        have h₁₅ : r > 0 := h₁
        have h₁₆ : r ^ 2 = (41 : ℝ) ^ 2 := by simpa using h₁₃
        have h₁₇ : r = 41 := by
          nlinarith
        exact h₁₇
      have h₁₈ : r = (41 : ℝ) := by simpa using h₁₄
      have h₁₉ : r ∈ ({(9 : ℝ), (41 : ℝ)} : Set ℝ) := by
        rw [h₁₈]
        norm_num
      exact h₁₉
    | inr h₅ =>

      have h₆ : y = (38 : ℝ) := by linarith
      have h₇ : (2 : ℝ) * y = (x : ℝ) ^ 2 - (8 : ℝ) * x + (12 : ℝ) := by simpa using h₂
      rw [h₆] at h₇
      have h₈ : (2 : ℝ) * (38 : ℝ) = (x : ℝ) ^ 2 - (8 : ℝ) * x + (12 : ℝ) := by simpa using h₇
      have h₉ : (x : ℝ) ^ 2 - (8 : ℝ) * x - (64 : ℝ) = 0 := by
        norm_num at h₈ ⊢
        linarith
      have h₁₀ : (x - (4 : ℝ)) ^ 2 = (80 : ℝ) := by
        have h₁₀₁ : (x : ℝ) ^ 2 - (8 : ℝ) * x - (64 : ℝ) = 0 := by simpa using h₉
        have h₁₀₂ : (x - (4 : ℝ)) ^ 2 = (80 : ℝ) := by
          nlinarith
        exact h₁₀₂
      have h₁₁ : (x - (4 : ℝ)) ^ 2 + (y - (39 : ℝ)) ^ 2 = r ^ 2 := by simpa using h₃
      rw [h₆] at h₁₁
      have h₁₂ : (x - (4 : ℝ)) ^ 2 + ((38 : ℝ) - (39 : ℝ)) ^ 2 = r ^ 2 := by simpa using h₁₁
      have h₁₃ : (x - (4 : ℝ)) ^ 2 + (1 : ℝ) = r ^ 2 := by
        norm_num at h₁₂ ⊢
        <;> linarith
      have h₁₄ : r ^ 2 = (9 : ℝ) ^ 2 := by
        have h₁₄₁ : (x - (4 : ℝ)) ^ 2 = (80 : ℝ) := by simpa using h₁₀
        have h₁₄₂ : (x - (4 : ℝ)) ^ 2 + (1 : ℝ) = r ^ 2 := by simpa using h₁₃
        nlinarith
      have h₁₅ : r = (9 : ℝ) := by
        have h₁₅₁ : r > 0 := h₁
        have h₁₅₂ : r ^ 2 = (9 : ℝ) ^ 2 := by simpa using h₁₄
        have h₁₅₃ : r = 9 := by
          nlinarith
        exact h₁₅₃
      have h₁₆ : r ∈ ({(9 : ℝ), (41 : ℝ)} : Set ℝ) := by
        rw [h₁₅]
        norm_num
      exact h₁₆

  have h_subset₂ : {(9 : ℝ), (41 : ℝ)} ⊆ {r : ℝ | (0 : ℝ) < r ∧ ∃ (x : ℝ) (y : ℝ), (2 : ℝ) * y = x ^ (2 : ℕ) - (8 : ℝ) * x + (12 : ℝ) ∧ (x - (4 : ℝ)) ^ (2 : ℕ) + (y - (39 : ℝ)) ^ (2 : ℕ) = r ^ (2 : ℕ) ∧ x - (4 : ℝ) + (y - (39 : ℝ)) * (x - (4 : ℝ)) = (0 : ℝ)} := by
    intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with (rfl | rfl)
    · 
      have h₁ : (0 : ℝ) < (9 : ℝ) := by norm_num
      have h₂ : ∃ (x : ℝ) (y : ℝ), (2 : ℝ) * y = x ^ (2 : ℕ) - (8 : ℝ) * x + (12 : ℝ) ∧ (x - (4 : ℝ)) ^ (2 : ℕ) + (y - (39 : ℝ)) ^ (2 : ℕ) = (9 : ℝ) ^ (2 : ℕ) ∧ x - (4 : ℝ) + (y - (39 : ℝ)) * (x - (4 : ℝ)) = (0 : ℝ) := by

        use (4 + Real.sqrt 80 : ℝ), (38 : ℝ)
        constructor
        · 
          norm_num [pow_two]
          <;>
          nlinarith [Real.sq_sqrt (show 0 ≤ 80 by norm_num), Real.sqrt_nonneg 80]
        · constructor
          · 
            norm_num [pow_two]
            <;>
            nlinarith [Real.sq_sqrt (show 0 ≤ 80 by norm_num), Real.sqrt_nonneg 80]
          · 
            norm_num [pow_two]
            <;>
            nlinarith [Real.sq_sqrt (show 0 ≤ 80 by norm_num), Real.sqrt_nonneg 80]
      exact ⟨h₁, h₂⟩
    · 
      have h₁ : (0 : ℝ) < (41 : ℝ) := by norm_num
      have h₂ : ∃ (x : ℝ) (y : ℝ), (2 : ℝ) * y = x ^ (2 : ℕ) - (8 : ℝ) * x + (12 : ℝ) ∧ (x - (4 : ℝ)) ^ (2 : ℕ) + (y - (39 : ℝ)) ^ (2 : ℕ) = (41 : ℝ) ^ (2 : ℕ) ∧ x - (4 : ℝ) + (y - (39 : ℝ)) * (x - (4 : ℝ)) = (0 : ℝ) := by

        use (4 : ℝ), (-2 : ℝ)
        norm_num [pow_two]
        <;>
        ring_nf
        <;>
        norm_num
        <;>
        linarith
      exact ⟨h₁, h₂⟩

  have h_set_eq : {r : ℝ | (0 : ℝ) < r ∧ ∃ (x : ℝ) (y : ℝ), (2 : ℝ) * y = x ^ (2 : ℕ) - (8 : ℝ) * x + (12 : ℝ) ∧ (x - (4 : ℝ)) ^ (2 : ℕ) + (y - (39 : ℝ)) ^ (2 : ℕ) = r ^ (2 : ℕ) ∧ x - (4 : ℝ) + (y - (39 : ℝ)) * (x - (4 : ℝ)) = (0 : ℝ)} = {(9 : ℝ), (41 : ℝ)} := by
    apply Set.Subset.antisymm
    · 
      exact h_subset₁
    · 
      exact h_subset₂

  have h_sum : ∑ r ∈ {(9 : ℝ), (41 : ℝ)}, r = (↑(50 : Nat) : ℝ) := by
    norm_num [Finset.sum_pair (show (9 : ℝ) ≠ 41 by norm_num)]
    <;>
    simp_all [Set.ext_iff]
    <;>
    norm_num
    <;>
    aesop

  exact ⟨h_set_eq, h_sum⟩
