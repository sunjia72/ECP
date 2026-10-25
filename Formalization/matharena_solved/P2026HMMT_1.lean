import Mathlib
import Aesop
open BigOperators Classical ENNReal Equiv EuclideanGeometry Filter Finset Fintype Function Lex List MeasureTheory Nat ProbabilityTheory Real SimpleGraph Real Nat Topology Rat
set_option maxHeartbeats 0
theorem P2026HMMT_1 : ∃ (P2026HMMT_1_answer : ℝ), ∀ (m b x₃ : ℝ), ((x₃ ≠ (0 : ℝ)) ∧ (x₃ ≠ (6 : ℝ) ∧ x₃ ≠ (7 : ℝ)) ∧ (∀ (x : ℝ), x ≠ (0 : ℝ) → (x ^ (2 : ℕ) + (2 : ℝ) / x = m * x + b ↔ x = (6 : ℝ) ∨ x = (7 : ℝ) ∨ x = x₃))) → (x₃ = P2026HMMT_1_answer) := by
  use ((-1 : ℝ) / 21 : ℝ)
  intro m b x₃ h
  have h₁ : 216 - 36 * m - 6 * b + 2 = 0 := by
    have h₂ : (6 : ℝ) ≠ (0 : ℝ) := by norm_num
    have h₃ : (6 : ℝ) ^ (2 : ℕ) + (2 : ℝ) / (6 : ℝ) = m * (6 : ℝ) + b := by
      have h₄ : (6 : ℝ) ^ (2 : ℕ) + (2 : ℝ) / (6 : ℝ) = m * (6 : ℝ) + b ↔ (6 : ℝ) = (6 : ℝ) ∨ (6 : ℝ) = (7 : ℝ) ∨ (6 : ℝ) = x₃ := by
        apply h.2.2 (6 : ℝ) (by norm_num)
      have h₅ : (6 : ℝ) = (6 : ℝ) ∨ (6 : ℝ) = (7 : ℝ) ∨ (6 : ℝ) = x₃ := by
        exact Or.inl rfl
      have h₆ : (6 : ℝ) ^ (2 : ℕ) + (2 : ℝ) / (6 : ℝ) = m * (6 : ℝ) + b := by
        rw [h₄] at *
        tauto
      exact h₆
    have h₇ : (6 : ℝ) ^ (2 : ℕ) + (2 : ℝ) / (6 : ℝ) = m * (6 : ℝ) + b := h₃
    norm_num at h₇ ⊢
    linarith

  have h₂ : 343 - 49 * m - 7 * b + 2 = 0 := by
    have h₃ : (7 : ℝ) ≠ (0 : ℝ) := by norm_num
    have h₄ : (7 : ℝ) ^ (2 : ℕ) + (2 : ℝ) / (7 : ℝ) = m * (7 : ℝ) + b := by
      have h₅ : (7 : ℝ) ^ (2 : ℕ) + (2 : ℝ) / (7 : ℝ) = m * (7 : ℝ) + b ↔ (7 : ℝ) = (6 : ℝ) ∨ (7 : ℝ) = (7 : ℝ) ∨ (7 : ℝ) = x₃ := by
        apply h.2.2 (7 : ℝ) (by norm_num)
      have h₆ : (7 : ℝ) = (6 : ℝ) ∨ (7 : ℝ) = (7 : ℝ) ∨ (7 : ℝ) = x₃ := by
        exact Or.inr (Or.inl rfl)
      have h₇ : (7 : ℝ) ^ (2 : ℕ) + (2 : ℝ) / (7 : ℝ) = m * (7 : ℝ) + b := by
        rw [h₅] at *
        tauto
      exact h₇
    have h₈ : (7 : ℝ) ^ (2 : ℕ) + (2 : ℝ) / (7 : ℝ) = m * (7 : ℝ) + b := h₄
    norm_num at h₈ ⊢
    <;>
    (try norm_num at h₈ ⊢) <;>
    (try linarith) <;>
    (try ring_nf at h₈ ⊢) <;>
    (try nlinarith)

  have h₃ : m = 272 / 21 := by
    have h₄ : m = 272 / 21 := by

      have h₅ : 216 - 36 * m - 6 * b + 2 = 0 := h₁
      have h₆ : 343 - 49 * m - 7 * b + 2 = 0 := h₂

      have h₇ : 7 * (216 - 36 * m - 6 * b + 2) = 0 := by linarith
      have h₈ : 6 * (343 - 49 * m - 7 * b + 2) = 0 := by linarith

      ring_nf at h₇ h₈ ⊢

      linarith
    exact h₄

  have h₄ : b = -869 / 21 := by
    have h₅ : 216 - 36 * m - 6 * b + 2 = 0 := h₁
    have h₆ : m = 272 / 21 := h₃
    rw [h₆] at h₅
    ring_nf at h₅ ⊢
    linarith

  have h₅ : x₃ ^ 3 - m * x₃ ^ 2 - b * x₃ + 2 = 0 := by
    have h₅₁ : x₃ ≠ (0 : ℝ) := h.1
    have h₅₂ : x₃ ^ (2 : ℕ) + (2 : ℝ) / x₃ = m * x₃ + b := by
      have h₅₃ : x₃ ^ (2 : ℕ) + (2 : ℝ) / x₃ = m * x₃ + b ↔ x₃ = (6 : ℝ) ∨ x₃ = (7 : ℝ) ∨ x₃ = x₃ := by
        apply h.2.2 x₃ h₅₁
      have h₅₄ : x₃ = (6 : ℝ) ∨ x₃ = (7 : ℝ) ∨ x₃ = x₃ := by
        exact Or.inr (Or.inr rfl)
      have h₅₅ : x₃ ^ (2 : ℕ) + (2 : ℝ) / x₃ = m * x₃ + b := by
        rw [h₅₃] at *
        tauto
      exact h₅₅
    have h₅₆ : x₃ ≠ 0 := h₅₁
    have h₅₇ : x₃ ^ 3 - m * x₃ ^ 2 - b * x₃ + 2 = 0 := by
      have h₅₈ : x₃ ^ (2 : ℕ) + (2 : ℝ) / x₃ = m * x₃ + b := h₅₂
      have h₅₉ : x₃ ^ 3 - m * x₃ ^ 2 - b * x₃ + 2 = 0 := by
        have h₆₀ : x₃ ≠ 0 := h₅₁
        field_simp [h₆₀] at h₅₈ ⊢
        ring_nf at h₅₈ ⊢
        nlinarith [sq_pos_of_ne_zero (sub_ne_zero_of_ne h.2.1.1), sq_pos_of_ne_zero (sub_ne_zero_of_ne h.2.1.2)]
      exact h₅₉
    exact h₅₇

  have h₆ : 21 * x₃ ^ 3 - 272 * x₃ ^ 2 + 869 * x₃ + 42 = 0 := by
    have h₆₁ : x₃ ^ 3 - m * x₃ ^ 2 - b * x₃ + 2 = 0 := h₅
    have h₆₂ : m = 272 / 21 := h₃
    have h₆₃ : b = -869 / 21 := h₄
    rw [h₆₂, h₆₃] at h₆₁
    ring_nf at h₆₁ ⊢
    nlinarith

  have h₇ : (x₃ - 6) * (x₃ - 7) * (21 * x₃ + 1) = 0 := by
    have h₇₁ : 21 * x₃ ^ 3 - 272 * x₃ ^ 2 + 869 * x₃ + 42 = 0 := h₆
    have h₇₂ : (x₃ - 6) * (x₃ - 7) * (21 * x₃ + 1) = 0 := by
      nlinarith [sq_pos_of_ne_zero (sub_ne_zero_of_ne h.1), sq_pos_of_ne_zero (sub_ne_zero_of_ne h.2.1.1),
        sq_pos_of_ne_zero (sub_ne_zero_of_ne h.2.1.2)]
    exact h₇₂

  have h₈ : x₃ = -1 / 21 := by
    have h₈₁ : (x₃ - 6) * (x₃ - 7) * (21 * x₃ + 1) = 0 := h₇
    have h₈₂ : x₃ ≠ 6 := by
      intro h₈₃
      apply h.2.1.1
      linarith
    have h₈₃ : x₃ ≠ 7 := by
      intro h₈₄
      apply h.2.1.2
      linarith
    have h₈₄ : 21 * x₃ + 1 = 0 := by
      have h₈₅ : (x₃ - 6) ≠ 0 := by
        intro h₈₆
        apply h₈₂
        linarith
      have h₈₆ : (x₃ - 7) ≠ 0 := by
        intro h₈₇
        apply h₈₃
        linarith
      have h₈₇ : (x₃ - 6) * (x₃ - 7) ≠ 0 := by
        exact mul_ne_zero h₈₅ h₈₆
      have h₈₈ : (x₃ - 6) * (x₃ - 7) * (21 * x₃ + 1) = 0 := h₈₁
      have h₈₉ : 21 * x₃ + 1 = 0 := by
        apply mul_left_cancel₀ h₈₇
        linarith
      exact h₈₉
    have h₈₅ : x₃ = -1 / 21 := by
      have h₈₆ : 21 * x₃ + 1 = 0 := h₈₄
      have h₈₇ : 21 * x₃ = -1 := by linarith
      have h₈₈ : x₃ = -1 / 21 := by
        field_simp at h₈₇ ⊢
        <;> nlinarith
      exact h₈₈
    exact h₈₅

  rw [h₈]
  <;> norm_num
