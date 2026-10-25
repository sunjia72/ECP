import Mathlib
import Aesop
open BigOperators Classical ENNReal Equiv EuclideanGeometry Filter Finset Fintype Function Lex List MeasureTheory Nat ProbabilityTheory Real SimpleGraph Real Nat Topology Rat
set_option maxHeartbeats 0
theorem P2026AIMEII_8 : ∃ (P2026AIMEII_8_answer : Nat), (IsLeast {x : ℕ | ∃ (y : ℕ) (z : ℕ), (0 : ℕ) < x ∧ (0 : ℕ) < y ∧ (0 : ℕ) < z ∧ y < (2 : ℕ) * x ∧ z ^ (2 : ℕ) * ((2 : ℕ) * x + y) = x * y ^ (2 : ℕ) ∧ (6 : ℕ) * ((2 : ℕ) * x + y) = (125 : ℕ) * (y + (2 : ℕ) * z)} P2026AIMEII_8_answer) := by
  use (245 : Nat)
  have h_main₁ : 245 ∈ {x : ℕ | ∃ (y : ℕ) (z : ℕ), (0 : ℕ) < x ∧ (0 : ℕ) < y ∧ (0 : ℕ) < z ∧ y < (2 : ℕ) * x ∧ z ^ (2 : ℕ) * ((2 : ℕ) * x + y) = x * y ^ (2 : ℕ) ∧ (6 : ℕ) * ((2 : ℕ) * x + y) = (125 : ℕ) * (y + (2 : ℕ) * z)} := by

    refine' ⟨10, 7, by decide, by decide, by decide, by norm_num, by norm_num, by norm_num⟩

  have h_main₂ : ∀ x' ∈ {x : ℕ | ∃ (y : ℕ) (z : ℕ), (0 : ℕ) < x ∧ (0 : ℕ) < y ∧ (0 : ℕ) < z ∧ y < (2 : ℕ) * x ∧ z ^ (2 : ℕ) * ((2 : ℕ) * x + y) = x * y ^ (2 : ℕ) ∧ (6 : ℕ) * ((2 : ℕ) * x + y) = (125 : ℕ) * (y + (2 : ℕ) * z)}, 245 ≤ x' := by
    intro x' hx'
    rcases hx' with ⟨y', z', hx'₁, hx'₂, hx'₃, hx'₄, hx'₅, hx'₆⟩
    have h₁ : 245 ≤ x' := by
      by_contra! h
      have h₂ : x' ≤ 244 := by linarith
      have h₃ : 0 < x' := by linarith
      have h₄ : 0 < y' := by linarith
      have h₅ : 0 < z' := by linarith
      have h₆ : y' < 2 * x' := by simpa using hx'₄
      have h₇ : z' ^ 2 * (2 * x' + y') = x' * y' ^ 2 := by simpa using hx'₅
      have h₈ : 6 * (2 * x' + y') = 125 * (y' + 2 * z') := by simpa using hx'₆
      have h₉ : 12 * x' = 119 * y' + 250 * z' := by
        have h₉₁ : 6 * (2 * x' + y') = 125 * (y' + 2 * z') := h₈
        ring_nf at h₉₁ ⊢
        omega

      have h₁₀ : z' ≤ 6 := by
        by_contra! h₁₀
        have h₁₁ : z' ≥ 7 := by linarith
        have h₁₂ : 119 * y' + 250 * z' ≥ 119 * y' + 250 * 7 := by
          have h₁₃ : 250 * z' ≥ 250 * 7 := by
            nlinarith
          nlinarith
        have h₁₃ : 12 * x' ≥ 12 * 1 := by
          nlinarith
        have h₁₄ : 119 * y' + 250 * z' ≥ 119 * y' + 1750 := by
          nlinarith
        have h₁₅ : 12 * x' < 2928 := by
          nlinarith
        have h₁₆ : 119 * y' + 250 * z' < 2928 := by
          nlinarith
        have h₁₇ : y' ≤ 24 := by
          nlinarith
        interval_cases y' <;> norm_num at h₉ ⊢ <;>
          (try omega) <;>
          (try {
            have h₁₈ : z' ≤ 11 := by
              nlinarith
            interval_cases z' <;> norm_num at h₉ ⊢ <;> omega
          }) <;>
          omega

      interval_cases z' <;>
        (try omega) <;>
        (try {
          have h₁₁ : y' ≤ 20 := by
            nlinarith
          interval_cases y' <;> norm_num at h₉ ⊢ <;>
            (try omega) <;>
            (try {
              have h₁₂ : x' ≤ 244 := by linarith
              interval_cases x' <;> norm_num at h₇ h₈ ⊢ <;>
                (try omega)
            })
        }) <;>
        (try {
          have h₁₁ : y' ≤ 18 := by
            nlinarith
          interval_cases y' <;> norm_num at h₉ ⊢ <;>
            (try omega) <;>
            (try {
              have h₁₂ : x' ≤ 244 := by linarith
              interval_cases x' <;> norm_num at h₇ h₈ ⊢ <;>
                (try omega)
            })
        }) <;>
        (try {
          have h₁₁ : y' ≤ 16 := by
            nlinarith
          interval_cases y' <;> norm_num at h₉ ⊢ <;>
            (try omega) <;>
            (try {
              have h₁₂ : x' ≤ 244 := by linarith
              interval_cases x' <;> norm_num at h₇ h₈ ⊢ <;>
                (try omega)
            })
        }) <;>
        (try {
          have h₁₁ : y' ≤ 14 := by
            nlinarith
          interval_cases y' <;> norm_num at h₉ ⊢ <;>
            (try omega) <;>
            (try {
              have h₁₂ : x' ≤ 244 := by linarith
              interval_cases x' <;> norm_num at h₇ h₈ ⊢ <;>
                (try omega)
            })
        }) <;>
        (try {
          have h₁₁ : y' ≤ 12 := by
            nlinarith
          interval_cases y' <;> norm_num at h₉ ⊢ <;>
            (try omega) <;>
            (try {
              have h₁₂ : x' ≤ 244 := by linarith
              interval_cases x' <;> norm_num at h₇ h₈ ⊢ <;>
                (try omega)
            })
        }) <;>
        (try {
          have h₁₁ : y' ≤ 10 := by
            nlinarith
          interval_cases y' <;> norm_num at h₉ ⊢ <;>
            (try omega) <;>
            (try {
              have h₁₂ : x' ≤ 244 := by linarith
              interval_cases x' <;> norm_num at h₇ h₈ ⊢ <;>
                (try omega)
            })
        }) <;>
        (try {
          have h₁₁ : y' ≤ 8 := by
            nlinarith
          interval_cases y' <;> norm_num at h₉ ⊢ <;>
            (try omega) <;>
            (try {
              have h₁₂ : x' ≤ 244 := by linarith
              interval_cases x' <;> norm_num at h₇ h₈ ⊢ <;>
                (try omega)
            })
        }) <;>
        (try {
          have h₁₁ : y' ≤ 6 := by
            nlinarith
          interval_cases y' <;> norm_num at h₉ ⊢ <;>
            (try omega) <;>
            (try {
              have h₁₂ : x' ≤ 244 := by linarith
              interval_cases x' <;> norm_num at h₇ h₈ ⊢ <;>
                (try omega)
            })
        }) <;>
        (try {
          have h₁₁ : y' ≤ 4 := by
            nlinarith
          interval_cases y' <;> norm_num at h₉ ⊢ <;>
            (try omega) <;>
            (try {
              have h₁₂ : x' ≤ 244 := by linarith
              interval_cases x' <;> norm_num at h₇ h₈ ⊢ <;>
                (try omega)
            })
        }) <;>
        (try {
          have h₁₁ : y' ≤ 2 := by
            nlinarith
          interval_cases y' <;> norm_num at h₉ ⊢ <;>
            (try omega) <;>
            (try {
              have h₁₂ : x' ≤ 244 := by linarith
              interval_cases x' <;> norm_num at h₇ h₈ ⊢ <;>
                (try omega)
            })
        }) <;>
        omega
    exact h₁

  have h_main : IsLeast {x : ℕ | ∃ (y : ℕ) (z : ℕ), (0 : ℕ) < x ∧ (0 : ℕ) < y ∧ (0 : ℕ) < z ∧ y < (2 : ℕ) * x ∧ z ^ (2 : ℕ) * ((2 : ℕ) * x + y) = x * y ^ (2 : ℕ) ∧ (6 : ℕ) * ((2 : ℕ) * x + y) = (125 : ℕ) * (y + (2 : ℕ) * z)} (245 : Nat) := by
    refine' ⟨h_main₁, _⟩
    intro x' hx'
    have h₁ : 245 ≤ x' := h_main₂ x' hx'
    exact h₁

  exact h_main
