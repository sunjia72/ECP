import Mathlib
import Aesop
open BigOperators Classical ENNReal Equiv EuclideanGeometry Filter Finset Fintype Function Lex List MeasureTheory Nat ProbabilityTheory Real SimpleGraph Real Nat Topology Rat
set_option maxHeartbeats 0
theorem P2026HMMT_23 : ∃ (P2026HMMT_23_answer : ℝ), ∀ (w x y z : ℝ), (((0 : ℝ) ≤ w ∧ w ≤ (12 : ℝ)) ∧ ((0 : ℝ) ≤ x ∧ x ≤ (16 : ℝ)) ∧ ((0 : ℝ) ≤ y ∧ y ≤ (12 : ℝ)) ∧ ((0 : ℝ) ≤ z ∧ z ≤ (16 : ℝ)) ∧ (w + y = (12 : ℝ) ∧ x + z = (16 : ℝ) ∧ ((12 : ℝ) - w) ^ (2 : ℕ) + x ^ (2 : ℕ) = ((12 : ℝ) - y) ^ (2 : ℕ) + ((16 : ℝ) - x) ^ (2 : ℕ) ∧ ((12 : ℝ) - y) ^ (2 : ℕ) + ((16 : ℝ) - x) ^ (2 : ℕ) = y ^ (2 : ℕ) + ((16 : ℝ) - z) ^ (2 : ℕ) ∧ y ^ (2 : ℕ) + ((16 : ℝ) - z) ^ (2 : ℕ) = w ^ (2 : ℕ) + z ^ (2 : ℕ)) ∧ (|((12 : ℝ) - w) * ((16 : ℝ) - x) - x * (y - (12 : ℝ))| = (120 : ℝ))) → (√(((12 : ℝ) - y) ^ (2 : ℕ) + ((16 : ℝ) - x) ^ (2 : ℕ)) = P2026HMMT_23_answer) := by
  use (Real.sqrt 125 : ℝ)
  intro w x y z h
  have hw : (0 : ℝ) ≤ w ∧ w ≤ (12 : ℝ) := by tauto
  have hx : (0 : ℝ) ≤ x ∧ x ≤ (16 : ℝ) := by tauto
  have hy : (0 : ℝ) ≤ y ∧ y ≤ (12 : ℝ) := by tauto
  have hz : (0 : ℝ) ≤ z ∧ z ≤ (16 : ℝ) := by tauto
  have h_sum_wy : w + y = (12 : ℝ) := by tauto
  have h_sum_xz : x + z = (16 : ℝ) := by tauto
  have h_sq1 : ((12 : ℝ) - w) ^ (2 : ℕ) + x ^ (2 : ℕ) = ((12 : ℝ) - y) ^ (2 : ℕ) + ((16 : ℝ) - x) ^ (2 : ℕ) := by tauto
  have h_sq2 : ((12 : ℝ) - y) ^ (2 : ℕ) + ((16 : ℝ) - x) ^ (2 : ℕ) = y ^ (2 : ℕ) + ((16 : ℝ) - z) ^ (2 : ℕ) := by tauto
  have h_sq3 : y ^ (2 : ℕ) + ((16 : ℝ) - z) ^ (2 : ℕ) = w ^ (2 : ℕ) + z ^ (2 : ℕ) := by tauto
  have h_abs : |((12 : ℝ) - w) * ((16 : ℝ) - x) - x * (y - (12 : ℝ))| = (120 : ℝ) := by tauto

  have h₁ : w = 12 - y := by
    have h₁₁ : w + y = 12 := h_sum_wy
    linarith

  have h₂ : z = 16 - x := by
    have h₂₁ : x + z = 16 := h_sum_xz
    linarith

  have h₃ : 3 * y + 4 * x = 50 := by
    have h₃₁ : ((12 : ℝ) - w) ^ 2 + x ^ 2 = ((12 : ℝ) - y) ^ 2 + ((16 : ℝ) - x) ^ 2 := by
      norm_cast at h_sq1 ⊢
      <;> simp_all [pow_two]
      <;> ring_nf at *
      <;> nlinarith
    have h₃₃ : w = 12 - y := h₁
    rw [h₃₃] at h₃₁
    ring_nf at h₃₁ ⊢
    nlinarith [sq_nonneg (y - 2), sq_nonneg (x - 11)]

  have h₄ : x = 5 ∨ x = 11 := by
    have h₄₁ : |((12 : ℝ) - w) * ((16 : ℝ) - x) - x * (y - (12 : ℝ))| = (120 : ℝ) := h_abs
    have h₄₂ : w = 12 - y := h₁
    rw [h₄₂] at h₄₁
    have h₄₃ : |(y : ℝ) * ((16 : ℝ) - x) - x * (y - (12 : ℝ))| = (120 : ℝ) := by
      ring_nf at h₄₁ ⊢
      <;> simpa [abs_mul, abs_of_nonneg, abs_of_nonpos] using h₄₁
    have h₄₄ : (y : ℝ) * ((16 : ℝ) - x) - x * (y - (12 : ℝ)) = (16 * y - 2 * x * y + 12 * x : ℝ) := by
      ring_nf
      <;> linarith
    rw [h₄₄] at h₄₃
    have h₄₅ : |(16 * y - 2 * x * y + 12 * x : ℝ)| = (120 : ℝ) := by
      exact h₄₃
    have h₄₆ : (16 * y - 2 * x * y + 12 * x : ℝ) = (8 * x ^ 2 - 128 * x + 800) / 3 := by
      have h₄₇ : 3 * y + 4 * x = 50 := h₃
      have h₄₈ : y = (50 - 4 * x) / 3 := by
        linarith
      rw [h₄₈]
      ring_nf
      <;> field_simp
      <;> ring_nf
      <;> nlinarith
    rw [h₄₆] at h₄₅
    have h₄₉ : |(8 * x ^ 2 - 128 * x + 800 : ℝ) / 3| = (120 : ℝ) := by
      exact h₄₅
    have h₅₀ : |(8 * x ^ 2 - 128 * x + 800 : ℝ)| = 360 := by
      have h₅₁ : |(8 * x ^ 2 - 128 * x + 800 : ℝ) / 3| = (120 : ℝ) := h₄₉
      have h₅₂ : |(8 * x ^ 2 - 128 * x + 800 : ℝ) / 3| = |(8 * x ^ 2 - 128 * x + 800 : ℝ)| / 3 := by
        rw [abs_div, abs_of_pos (by norm_num : (3 : ℝ) > 0)]
        <;> ring_nf
      rw [h₅₂] at h₅₁
      have h₅₃ : |(8 * x ^ 2 - 128 * x + 800 : ℝ)| / 3 = (120 : ℝ) := by
        linarith
      have h₅₄ : |(8 * x ^ 2 - 128 * x + 800 : ℝ)| = 360 := by
        linarith
      exact h₅₄
    have h₅₁ : (8 * x ^ 2 - 128 * x + 800 : ℝ) > 0 := by
      nlinarith [sq_nonneg (x - 8)]
    have h₅₂ : (8 * x ^ 2 - 128 * x + 800 : ℝ) = 360 := by
      rw [abs_of_pos h₅₁] at h₅₀
      linarith
    have h₅₃ : (x : ℝ) = 5 ∨ (x : ℝ) = 11 := by
      have h₅₄ : (x : ℝ) ^ 2 - 16 * x + 55 = 0 := by
        nlinarith
      have h₅₅ : (x : ℝ) = 5 ∨ (x : ℝ) = 11 := by
        have h₅₆ : ((x : ℝ) - 5) * ((x : ℝ) - 11) = 0 := by
          nlinarith
        have h₅₇ : (x : ℝ) - 5 = 0 ∨ (x : ℝ) - 11 = 0 := by
          apply eq_zero_or_eq_zero_of_mul_eq_zero h₅₆
        cases h₅₇ with
        | inl h₅₈ =>
          have h₅₉ : (x : ℝ) = 5 := by linarith
          exact Or.inl h₅₉
        | inr h₅₈ =>
          have h₅₉ : (x : ℝ) = 11 := by linarith
          exact Or.inr h₅₉
      exact h₅₅
    cases h₅₃ with
    | inl h₅₄ =>
      have h₅₅ : x = 5 := by
        norm_cast at h₅₄ ⊢
        <;> linarith
      exact Or.inl h₅₅
    | inr h₅₄ =>
      have h₅₅ : x = 11 := by
        norm_cast at h₅₄ ⊢
        <;> linarith
      exact Or.inr h₅₅

  have h₅ : √(((12 : ℝ) - y) ^ (2 : ℕ) + ((16 : ℝ) - x) ^ (2 : ℕ)) = (Real.sqrt 125 : ℝ) := by
    have h₅₁ : x = 5 ∨ x = 11 := h₄
    cases h₅₁ with
    | inl h₅₁ =>
      have h₅₂ : x = 5 := h₅₁
      have h₅₃ : 3 * y + 4 * x = 50 := h₃
      have h₅₄ : y = 10 := by
        rw [h₅₂] at h₅₃
        linarith
      have h₅₅ : √(((12 : ℝ) - y) ^ (2 : ℕ) + ((16 : ℝ) - x) ^ (2 : ℕ)) = (Real.sqrt 125 : ℝ) := by
        rw [h₅₄, h₅₂]
        have h₅₆ : √(((12 : ℝ) - (10 : ℝ)) ^ (2 : ℕ) + ((16 : ℝ) - (5 : ℝ)) ^ (2 : ℕ)) = Real.sqrt 125 := by
          have h₅₇ : ((12 : ℝ) - (10 : ℝ)) ^ (2 : ℕ) + ((16 : ℝ) - (5 : ℝ)) ^ (2 : ℕ) = (125 : ℝ) := by
            norm_num
          rw [h₅₇]
          <;> simp [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        exact h₅₆
      exact h₅₅
    | inr h₅₁ =>
      have h₅₂ : x = 11 := h₅₁
      have h₅₃ : 3 * y + 4 * x = 50 := h₃
      have h₅₄ : y = 2 := by
        rw [h₅₂] at h₅₃
        linarith
      have h₅₅ : √(((12 : ℝ) - y) ^ (2 : ℕ) + ((16 : ℝ) - x) ^ (2 : ℕ)) = (Real.sqrt 125 : ℝ) := by
        rw [h₅₄, h₅₂]
        have h₅₆ : √(((12 : ℝ) - (2 : ℝ)) ^ (2 : ℕ) + ((16 : ℝ) - (11 : ℝ)) ^ (2 : ℕ)) = Real.sqrt 125 := by
          have h₅₇ : ((12 : ℝ) - (2 : ℝ)) ^ (2 : ℕ) + ((16 : ℝ) - (11 : ℝ)) ^ (2 : ℕ) = (125 : ℝ) := by
            norm_num
          rw [h₅₇]
          <;> simp [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        exact h₅₆
      exact h₅₅

  exact h₅
