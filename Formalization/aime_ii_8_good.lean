import Mathlib
import Aesop
open BigOperators Classical ENNReal Equiv EuclideanGeometry Filter Finset Fintype Function Lex List MeasureTheory Nat ProbabilityTheory Real SimpleGraph Real Nat Topology Rat
set_option maxHeartbeats 0
theorem P2026AIMEII_8 : ∃ (P2026AIMEII_8_answer : Nat), (IsLeast {x : ℕ | ∃ (y : ℕ) (z : ℕ), (0 : ℕ) < x ∧ (0 : ℕ) < y ∧ (0 : ℕ) < z ∧ y < (2 : ℕ) * x ∧ z ^ (2 : ℕ) * ((2 : ℕ) * x + y) = x * y ^ (2 : ℕ) ∧ (6 : ℕ) * ((2 : ℕ) * x + y) = (125 : ℕ) * (y + (2 : ℕ) * z)} P2026AIMEII_8_answer) := by
  use (245 : Nat)
  have h245 : 245 ∈ {x : ℕ | ∃ (y : ℕ) (z : ℕ), (0 : ℕ) < x ∧ (0 : ℕ) < y ∧ (0 : ℕ) < z ∧ y < (2 : ℕ) * x ∧ z ^ (2 : ℕ) * ((2 : ℕ) * x + y) = x * y ^ (2 : ℕ) ∧ (6 : ℕ) * ((2 : ℕ) * x + y) = (125 : ℕ) * (y + (2 : ℕ) * z)} := by

    refine' ⟨10, 7, by decide, by decide, by decide, by norm_num, _⟩
    <;> norm_num
    <;> ring_nf at *
    <;> norm_num
    <;> rfl

  have hmin : ∀ (x' : ℕ), x' ∈ {x : ℕ | ∃ (y : ℕ) (z : ℕ), (0 : ℕ) < x ∧ (0 : ℕ) < y ∧ (0 : ℕ) < z ∧ y < (2 : ℕ) * x ∧ z ^ (2 : ℕ) * ((2 : ℕ) * x + y) = x * y ^ (2 : ℕ) ∧ (6 : ℕ) * ((2 : ℕ) * x + y) = (125 : ℕ) * (y + (2 : ℕ) * z)} → 245 ≤ x' := by
    intro x' hx'
    rcases hx' with ⟨y, z, hx'_pos, hy_pos, hz_pos, h_y_lt_2x', h_z_sq_eq, h_6_eq⟩
    have h₁ : 245 ≤ x' := by
      by_contra! h
      have h₂ : x' ≤ 244 := by linarith
      have h₃ : 0 < x' := hx'_pos
      have h₄ : 0 < y := hy_pos
      have h₅ : 0 < z := hz_pos
      have h₆ : y < 2 * x' := h_y_lt_2x'
      have h₇ : z ^ 2 * (2 * x' + y) = x' * y ^ 2 := h_z_sq_eq
      have h₈ : 6 * (2 * x' + y) = 125 * (y + 2 * z) := h_6_eq
      have h₉ : x' ≤ 244 := by linarith

      have h₁₀ : 12 * x' = 119 * y + 250 * z := by
        have h₁₀₁ : 6 * (2 * x' + y) = 125 * (y + 2 * z) := h_6_eq
        ring_nf at h₁₀₁ ⊢
        omega

      have h₁₁ : y ≤ 24 := by
        by_contra! h₁₁
        have h₁₂ : y ≥ 25 := by linarith
        have h₁₃ : 12 * x' = 119 * y + 250 * z := h₁₀
        have h₁₄ : 119 * y + 250 * z ≥ 119 * 25 + 250 * 1 := by
          nlinarith
        have h₁₅ : 12 * x' ≥ 119 * 25 + 250 * 1 := by linarith
        have h₁₆ : x' ≥ (119 * 25 + 250 * 1) / 12 := by
          omega
        norm_num at h₁₆ ⊢
        <;> omega
      have h₁₂ : z ≤ 11 := by
        by_contra! h₁₂
        have h₁₃ : z ≥ 12 := by linarith
        have h₁₄ : 12 * x' = 119 * y + 250 * z := h₁₀
        have h₁₅ : 119 * y + 250 * z ≥ 119 * 1 + 250 * 12 := by
          nlinarith
        have h₁₆ : 12 * x' ≥ 119 * 1 + 250 * 12 := by linarith
        have h₁₇ : x' ≥ (119 * 1 + 250 * 12) / 12 := by
          omega
        norm_num at h₁₇ ⊢
        <;> omega

      interval_cases y <;> interval_cases z <;> norm_num at h₁₀ h₇ h₈ ⊢ <;>
        (try omega) <;>
        (try {
          ring_nf at h₇ h₈ ⊢
          norm_num at h₇ h₈ ⊢
          <;>
          (try omega) <;>
          (try {
            have h₁₃ : x' ≤ 244 := by linarith
            interval_cases x' <;> norm_num at h₇ h₈ ⊢ <;> omega
          })
        }) <;>
        (try {
          have h₁₃ : x' ≤ 244 := by linarith
          interval_cases x' <;> norm_num at h₇ h₈ ⊢ <;> omega
        })
    exact h₁

  have hmain : IsLeast {x : ℕ | ∃ (y : ℕ) (z : ℕ), (0 : ℕ) < x ∧ (0 : ℕ) < y ∧ (0 : ℕ) < z ∧ y < (2 : ℕ) * x ∧ z ^ (2 : ℕ) * ((2 : ℕ) * x + y) = x * y ^ (2 : ℕ) ∧ (6 : ℕ) * ((2 : ℕ) * x + y) = (125 : ℕ) * (y + (2 : ℕ) * z)} 245 := by
    refine' ⟨h245, _⟩
    intro x' hx'
    have h₁ : 245 ≤ x' := hmin x' hx'
    exact h₁

  exact hmain

