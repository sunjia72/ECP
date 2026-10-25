import Mathlib
import Aesop
open BigOperators Classical ENNReal Equiv EuclideanGeometry Filter Finset Fintype Function Lex List MeasureTheory Nat ProbabilityTheory Real SimpleGraph Real Nat Topology Rat
set_option maxHeartbeats 0
theorem putnam_1998_b1 : ∃ (putnam_1998_b1_solution : ℝ), (sInf {x : ℝ | ∃ x_1 > (0 : ℝ), ((x_1 + (1 : ℝ) / x_1) ^ (6 : ℕ) - (x_1 ^ (6 : ℕ) + (1 : ℝ) / x_1 ^ (6 : ℕ)) - (2 : ℝ)) / ((x_1 + (1 : ℝ) / x_1) ^ (3 : ℕ) + (x_1 ^ (3 : ℕ) + (1 : ℝ) / x_1 ^ (3 : ℕ))) = x} = putnam_1998_b1_solution) := by
  use ((6 : ℝ) : ℝ)
  have h_main : sInf {x : ℝ | ∃ x_1 > (0 : ℝ), ((x_1 + (1 : ℝ) / x_1) ^ (6 : ℕ) - (x_1 ^ (6 : ℕ) + (1 : ℝ) / x_1 ^ (6 : ℕ)) - (2 : ℝ)) / ((x_1 + (1 : ℝ) / x_1) ^ (3 : ℕ) + (x_1 ^ (3 : ℕ) + (1 : ℝ) / x_1 ^ (3 : ℕ))) = x} = 6 := by
    have h₁ : (6 : ℝ) ∈ {x : ℝ | ∃ x_1 > (0 : ℝ), ((x_1 + (1 : ℝ) / x_1) ^ (6 : ℕ) - (x_1 ^ (6 : ℕ) + (1 : ℝ) / x_1 ^ (6 : ℕ)) - (2 : ℝ)) / ((x_1 + (1 : ℝ) / x_1) ^ (3 : ℕ) + (x_1 ^ (3 : ℕ) + (1 : ℝ) / x_1 ^ (3 : ℕ))) = x} := by

      have h₁₁ : ((1 : ℝ) + (1 : ℝ) / (1 : ℝ)) ^ (6 : ℕ) - ((1 : ℝ) ^ (6 : ℕ) + (1 : ℝ) / (1 : ℝ) ^ (6 : ℕ)) - (2 : ℝ) = 60 := by
        norm_num
      have h₁₂ : ((1 : ℝ) + (1 : ℝ) / (1 : ℝ)) ^ (3 : ℕ) + ((1 : ℝ) ^ (3 : ℕ) + (1 : ℝ) / (1 : ℝ) ^ (3 : ℕ)) = 10 := by
        norm_num
      have h₁₃ : ((1 : ℝ) + (1 : ℝ) / (1 : ℝ)) ^ (6 : ℕ) - ((1 : ℝ) ^ (6 : ℕ) + (1 : ℝ) / (1 : ℝ) ^ (6 : ℕ)) - (2 : ℝ) = 60 := by
        norm_num
      have h₁₄ : ((1 : ℝ) + (1 : ℝ) / (1 : ℝ)) ^ (3 : ℕ) + ((1 : ℝ) ^ (3 : ℕ) + (1 : ℝ) / (1 : ℝ) ^ (3 : ℕ)) = 10 := by
        norm_num
      refine' ⟨1, by norm_num, _⟩
      have h₁₅ : ((1 : ℝ) + (1 : ℝ) / (1 : ℝ)) ^ (6 : ℕ) - ((1 : ℝ) ^ (6 : ℕ) + (1 : ℝ) / (1 : ℝ) ^ (6 : ℕ)) - (2 : ℝ) = 60 := by norm_num
      have h₁₆ : ((1 : ℝ) + (1 : ℝ) / (1 : ℝ)) ^ (3 : ℕ) + ((1 : ℝ) ^ (3 : ℕ) + (1 : ℝ) / (1 : ℝ) ^ (3 : ℕ)) = 10 := by norm_num
      have h₁₇ : ((1 : ℝ) + (1 : ℝ) / (1 : ℝ)) ^ (6 : ℕ) - ((1 : ℝ) ^ (6 : ℕ) + (1 : ℝ) / (1 : ℝ) ^ (6 : ℕ)) - (2 : ℝ) = 60 := by norm_num
      have h₁₈ : ((1 : ℝ) + (1 : ℝ) / (1 : ℝ)) ^ (3 : ℕ) + ((1 : ℝ) ^ (3 : ℕ) + (1 : ℝ) / (1 : ℝ) ^ (3 : ℕ)) = 10 := by norm_num
      field_simp [h₁₆, h₁₈] at h₁₅ h₁₇ ⊢
      <;> norm_num at h₁₅ h₁₇ ⊢ <;> linarith
    have h₂ : ∀ (x : ℝ), x ∈ {x : ℝ | ∃ x_1 > (0 : ℝ), ((x_1 + (1 : ℝ) / x_1) ^ (6 : ℕ) - (x_1 ^ (6 : ℕ) + (1 : ℝ) / x_1 ^ (6 : ℕ)) - (2 : ℝ)) / ((x_1 + (1 : ℝ) / x_1) ^ (3 : ℕ) + (x_1 ^ (3 : ℕ) + (1 : ℝ) / x_1 ^ (3 : ℕ))) = x} → x ≥ 6 := by
      intro x hx
      rcases hx with ⟨x₁, hx₁_pos, hx_eq⟩
      have h₃ : 0 < x₁ := hx₁_pos
      have h₄ : ((x₁ + (1 : ℝ) / x₁) ^ (6 : ℕ) - (x₁ ^ (6 : ℕ) + (1 : ℝ) / x₁ ^ (6 : ℕ)) - (2 : ℝ)) / ((x₁ + (1 : ℝ) / x₁) ^ (3 : ℕ) + (x₁ ^ (3 : ℕ) + (1 : ℝ) / x₁ ^ (3 : ℕ))) = x := hx_eq
      have h₅ : x = 3 * (x₁ + 1 / x₁) := by
        have h₅₁ : 0 < x₁ := h₃
        have h₅₂ : 0 < x₁ ^ 3 := by positivity
        have h₅₃ : 0 < x₁ ^ 6 := by positivity
        have h₅₄ : 0 < x₁ + 1 / x₁ := by positivity
        have h₅₅ : x₁ + 1 / x₁ ≥ 2 := by
          have h₅₅₁ : x₁ + 1 / x₁ - 2 = (x₁ - 1) ^ 2 / x₁ := by
            field_simp [h₅₁.ne']
            ring
          have h₅₅₂ : (x₁ - 1) ^ 2 / x₁ ≥ 0 := by
            exact div_nonneg (sq_nonneg (x₁ - 1)) (le_of_lt h₅₁)
          linarith

        have h₅₆ : (x₁ + 1 / x₁ : ℝ) ^ 6 - (x₁ ^ 6 + 1 / x₁ ^ 6 : ℝ) - 2 = 6 * (x₁ + 1 / x₁ : ℝ) ^ 4 - 9 * (x₁ + 1 / x₁ : ℝ) ^ 2 := by
          have h₅₆₁ : (x₁ ^ 3 + 1 / x₁ ^ 3 : ℝ) = (x₁ + 1 / x₁ : ℝ) ^ 3 - 3 * (x₁ + 1 / x₁ : ℝ) := by
            have h₅₆₁₁ : (x₁ + 1 / x₁ : ℝ) ^ 3 = x₁ ^ 3 + 1 / x₁ ^ 3 + 3 * (x₁ + 1 / x₁ : ℝ) := by
              field_simp [h₅₁.ne']
              ring
            linarith
          have h₅₆₂ : (x₁ ^ 6 + 1 / x₁ ^ 6 : ℝ) = (x₁ ^ 3 + 1 / x₁ ^ 3 : ℝ) ^ 2 - 2 := by
            have h₅₆₂₁ : (x₁ ^ 3 + 1 / x₁ ^ 3 : ℝ) ^ 2 = x₁ ^ 6 + 1 / x₁ ^ 6 + 2 := by
              field_simp [h₅₁.ne']
              ring
            linarith
          have h₅₆₃ : (x₁ + 1 / x₁ : ℝ) ^ 6 - (x₁ ^ 6 + 1 / x₁ ^ 6 : ℝ) - 2 = 6 * (x₁ + 1 / x₁ : ℝ) ^ 4 - 9 * (x₁ + 1 / x₁ : ℝ) ^ 2 := by
            calc
              (x₁ + 1 / x₁ : ℝ) ^ 6 - (x₁ ^ 6 + 1 / x₁ ^ 6 : ℝ) - 2 = (x₁ + 1 / x₁ : ℝ) ^ 6 - ((x₁ ^ 3 + 1 / x₁ ^ 3 : ℝ) ^ 2 - 2) - 2 := by rw [h₅₆₂]
              _ = (x₁ + 1 / x₁ : ℝ) ^ 6 - (x₁ ^ 3 + 1 / x₁ ^ 3 : ℝ) ^ 2 := by ring
              _ = (x₁ + 1 / x₁ : ℝ) ^ 6 - ((x₁ + 1 / x₁ : ℝ) ^ 3 - 3 * (x₁ + 1 / x₁ : ℝ)) ^ 2 := by rw [h₅₆₁]
              _ = 6 * (x₁ + 1 / x₁ : ℝ) ^ 4 - 9 * (x₁ + 1 / x₁ : ℝ) ^ 2 := by
                ring_nf
                <;> field_simp [h₅₁.ne']
                <;> ring_nf
                <;> nlinarith [sq_nonneg (x₁ - 1)]
              _ = 6 * (x₁ + 1 / x₁ : ℝ) ^ 4 - 9 * (x₁ + 1 / x₁ : ℝ) ^ 2 := by ring
          exact h₅₆₃
        have h₅₇ : (x₁ + 1 / x₁ : ℝ) ^ 3 + (x₁ ^ 3 + 1 / x₁ ^ 3 : ℝ) = 2 * (x₁ + 1 / x₁ : ℝ) ^ 3 - 3 * (x₁ + 1 / x₁ : ℝ) := by
          have h₅₇₁ : (x₁ ^ 3 + 1 / x₁ ^ 3 : ℝ) = (x₁ + 1 / x₁ : ℝ) ^ 3 - 3 * (x₁ + 1 / x₁ : ℝ) := by
            have h₅₇₁₁ : (x₁ + 1 / x₁ : ℝ) ^ 3 = x₁ ^ 3 + 1 / x₁ ^ 3 + 3 * (x₁ + 1 / x₁ : ℝ) := by
              field_simp [h₅₁.ne']
              ring
            linarith
          calc
            (x₁ + 1 / x₁ : ℝ) ^ 3 + (x₁ ^ 3 + 1 / x₁ ^ 3 : ℝ) = (x₁ + 1 / x₁ : ℝ) ^ 3 + ((x₁ + 1 / x₁ : ℝ) ^ 3 - 3 * (x₁ + 1 / x₁ : ℝ)) := by rw [h₅₇₁]
            _ = 2 * (x₁ + 1 / x₁ : ℝ) ^ 3 - 3 * (x₁ + 1 / x₁ : ℝ) := by ring
        have h₅₈ : 6 * (x₁ + 1 / x₁ : ℝ) ^ 4 - 9 * (x₁ + 1 / x₁ : ℝ) ^ 2 = 3 * (x₁ + 1 / x₁ : ℝ) ^ 2 * (2 * (x₁ + 1 / x₁ : ℝ) ^ 2 - 3) := by
          ring
        have h₅₉ : 2 * (x₁ + 1 / x₁ : ℝ) ^ 3 - 3 * (x₁ + 1 / x₁ : ℝ) = (x₁ + 1 / x₁ : ℝ) * (2 * (x₁ + 1 / x₁ : ℝ) ^ 2 - 3) := by
          ring
        have h₅₁₀ : (x₁ + 1 / x₁ : ℝ) ≥ 2 := by
          have h₅₁₀₁ : x₁ + 1 / x₁ - 2 = (x₁ - 1) ^ 2 / x₁ := by
            field_simp [h₅₁.ne']
            ring
          have h₅₁₀₂ : (x₁ - 1) ^ 2 / x₁ ≥ 0 := by
            exact div_nonneg (sq_nonneg (x₁ - 1)) (le_of_lt h₅₁)
          linarith
        have h₅₁₁ : (2 : ℝ) * (x₁ + 1 / x₁ : ℝ) ^ 2 - 3 ≥ 5 := by
          have h₅₁₁₁ : (x₁ + 1 / x₁ : ℝ) ≥ 2 := h₅₁₀
          nlinarith [sq_nonneg (x₁ + 1 / x₁ - 2)]
        have h₅₁₂ : (x₁ + 1 / x₁ : ℝ) > 0 := by positivity
        have h₅₁₃ : (2 : ℝ) * (x₁ + 1 / x₁ : ℝ) ^ 3 - 3 * (x₁ + 1 / x₁ : ℝ) > 0 := by
          have h₅₁₃₁ : (x₁ + 1 / x₁ : ℝ) ≥ 2 := h₅₁₀
          have h₅₁₃₂ : (2 : ℝ) * (x₁ + 1 / x₁ : ℝ) ^ 3 - 3 * (x₁ + 1 / x₁ : ℝ) = (x₁ + 1 / x₁ : ℝ) * (2 * (x₁ + 1 / x₁ : ℝ) ^ 2 - 3) := by ring
          rw [h₅₁₃₂]
          have h₅₁₃₃ : (x₁ + 1 / x₁ : ℝ) > 0 := by positivity
          have h₅₁₃₄ : (2 : ℝ) * (x₁ + 1 / x₁ : ℝ) ^ 2 - 3 ≥ 5 := h₅₁₁
          nlinarith
        have h₅₁₄ : (6 : ℝ) * (x₁ + 1 / x₁ : ℝ) ^ 4 - 9 * (x₁ + 1 / x₁ : ℝ) ^ 2 = 3 * (x₁ + 1 / x₁ : ℝ) ^ 2 * (2 * (x₁ + 1 / x₁ : ℝ) ^ 2 - 3) := by
          ring
        have h₅₁₅ : (2 : ℝ) * (x₁ + 1 / x₁ : ℝ) ^ 3 - 3 * (x₁ + 1 / x₁ : ℝ) = (x₁ + 1 / x₁ : ℝ) * (2 * (x₁ + 1 / x₁ : ℝ) ^ 2 - 3) := by
          ring
        have h₅₁₆ : ((x₁ + 1 / x₁ : ℝ) ^ 6 - (x₁ ^ 6 + 1 / x₁ ^ 6 : ℝ) - 2) / ((x₁ + 1 / x₁ : ℝ) ^ 3 + (x₁ ^ 3 + 1 / x₁ ^ 3 : ℝ)) = 3 * (x₁ + 1 / x₁ : ℝ) := by
          have h₅₁₆₁ : (x₁ + 1 / x₁ : ℝ) ^ 6 - (x₁ ^ 6 + 1 / x₁ ^ 6 : ℝ) - 2 = 6 * (x₁ + 1 / x₁ : ℝ) ^ 4 - 9 * (x₁ + 1 / x₁ : ℝ) ^ 2 := by
            exact h₅₆
          have h₅₁₆₂ : (x₁ + 1 / x₁ : ℝ) ^ 3 + (x₁ ^ 3 + 1 / x₁ ^ 3 : ℝ) = 2 * (x₁ + 1 / x₁ : ℝ) ^ 3 - 3 * (x₁ + 1 / x₁ : ℝ) := by
            exact h₅₇
          rw [h₅₁₆₁, h₅₁₆₂]
          have h₅₁₆₃ : 6 * (x₁ + 1 / x₁ : ℝ) ^ 4 - 9 * (x₁ + 1 / x₁ : ℝ) ^ 2 = 3 * (x₁ + 1 / x₁ : ℝ) ^ 2 * (2 * (x₁ + 1 / x₁ : ℝ) ^ 2 - 3) := by
            ring
          have h₅₁₆₄ : 2 * (x₁ + 1 / x₁ : ℝ) ^ 3 - 3 * (x₁ + 1 / x₁ : ℝ) = (x₁ + 1 / x₁ : ℝ) * (2 * (x₁ + 1 / x₁ : ℝ) ^ 2 - 3) := by
            ring
          rw [h₅₁₆₃, h₅₁₆₄]
          have h₅₁₆₅ : (x₁ + 1 / x₁ : ℝ) > 0 := by positivity
          have h₅₁₆₆ : (2 : ℝ) * (x₁ + 1 / x₁ : ℝ) ^ 2 - 3 ≠ 0 := by
            have h₅₁₆₇ : (2 : ℝ) * (x₁ + 1 / x₁ : ℝ) ^ 2 - 3 ≥ 5 := h₅₁₁
            linarith
          have h₅₁₆₇ : (x₁ + 1 / x₁ : ℝ) ≠ 0 := by positivity
          field_simp [h₅₁₆₆, h₅₁₆₇]
          <;> ring_nf
          <;> field_simp [h₅₁.ne']
          <;> nlinarith
        have h₅₁₇ : x = 3 * (x₁ + 1 / x₁) := by
          have h₅₁₇₁ : ((x₁ + 1 / x₁ : ℝ) ^ 6 - (x₁ ^ 6 + 1 / x₁ ^ 6 : ℝ) - 2) / ((x₁ + 1 / x₁ : ℝ) ^ 3 + (x₁ ^ 3 + 1 / x₁ ^ 3 : ℝ)) = x := by
            simpa using hx_eq
          have h₅₁₇₂ : ((x₁ + 1 / x₁ : ℝ) ^ 6 - (x₁ ^ 6 + 1 / x₁ ^ 6 : ℝ) - 2) / ((x₁ + 1 / x₁ : ℝ) ^ 3 + (x₁ ^ 3 + 1 / x₁ ^ 3 : ℝ)) = 3 * (x₁ + 1 / x₁ : ℝ) := by
            exact h₅₁₆
          linarith
        exact h₅₁₇
      have h₆ : x ≥ 6 := by
        have h₆₁ : x = 3 * (x₁ + 1 / x₁) := h₅
        have h₆₂ : x₁ + 1 / x₁ ≥ 2 := by
          have h₆₂₁ : x₁ + 1 / x₁ - 2 = (x₁ - 1) ^ 2 / x₁ := by
            field_simp [h₃.ne']
            ring
          have h₆₂₂ : (x₁ - 1) ^ 2 / x₁ ≥ 0 := by
            exact div_nonneg (sq_nonneg (x₁ - 1)) (le_of_lt h₃)
          linarith
        have h₆₃ : 3 * (x₁ + 1 / x₁) ≥ 6 := by
          linarith
        linarith
      exact h₆
    have h₃ : sInf {x : ℝ | ∃ x_1 > (0 : ℝ), ((x_1 + (1 : ℝ) / x_1) ^ (6 : ℕ) - (x_1 ^ (6 : ℕ) + (1 : ℝ) / x_1 ^ (6 : ℕ)) - (2 : ℝ)) / ((x_1 + (1 : ℝ) / x_1) ^ (3 : ℕ) + (x_1 ^ (3 : ℕ) + (1 : ℝ) / x_1 ^ (3 : ℕ))) = x} ≤ 6 := by
      apply csInf_le
      · 
        use 6
        intro x hx
        have h₄ : x ≥ 6 := h₂ x hx
        linarith
      · 
        exact h₁
    have h₄ : sInf {x : ℝ | ∃ x_1 > (0 : ℝ), ((x_1 + (1 : ℝ) / x_1) ^ (6 : ℕ) - (x_1 ^ (6 : ℕ) + (1 : ℝ) / x_1 ^ (6 : ℕ)) - (2 : ℝ)) / ((x_1 + (1 : ℝ) / x_1) ^ (3 : ℕ) + (x_1 ^ (3 : ℕ) + (1 : ℝ) / x_1 ^ (3 : ℕ))) = x} ≥ 6 := by

      have h₄₁ : ∀ x ∈ {x : ℝ | ∃ x_1 > (0 : ℝ), ((x_1 + (1 : ℝ) / x_1) ^ (6 : ℕ) - (x_1 ^ (6 : ℕ) + (1 : ℝ) / x_1 ^ (6 : ℕ)) - (2 : ℝ)) / ((x_1 + (1 : ℝ) / x_1) ^ (3 : ℕ) + (x_1 ^ (3 : ℕ) + (1 : ℝ) / x_1 ^ (3 : ℕ))) = x}, x ≥ 6 := by
        intro x hx
        exact h₂ x hx
      have h₄₂ : BddBelow {x : ℝ | ∃ x_1 > (0 : ℝ), ((x_1 + (1 : ℝ) / x_1) ^ (6 : ℕ) - (x_1 ^ (6 : ℕ) + (1 : ℝ) / x_1 ^ (6 : ℕ)) - (2 : ℝ)) / ((x_1 + (1 : ℝ) / x_1) ^ (3 : ℕ) + (x_1 ^ (3 : ℕ) + (1 : ℝ) / x_1 ^ (3 : ℕ))) = x} := by
        use 6
        intro x hx
        have h₄₃ : x ≥ 6 := h₂ x hx
        linarith

      have h₄₃ : sInf {x : ℝ | ∃ x_1 > (0 : ℝ), ((x_1 + (1 : ℝ) / x_1) ^ (6 : ℕ) - (x_1 ^ (6 : ℕ) + (1 : ℝ) / x_1 ^ (6 : ℕ)) - (2 : ℝ)) / ((x_1 + (1 : ℝ) / x_1) ^ (3 : ℕ) + (x_1 ^ (3 : ℕ) + (1 : ℝ) / x_1 ^ (3 : ℕ))) = x} ≥ 6 := by
        apply le_csInf
        · 
          exact ⟨6, h₁⟩
        · 
          intro x hx
          have h₄₄ : x ≥ 6 := h₂ x hx
          linarith
      exact h₄₃

    have h₅ : sInf {x : ℝ | ∃ x_1 > (0 : ℝ), ((x_1 + (1 : ℝ) / x_1) ^ (6 : ℕ) - (x_1 ^ (6 : ℕ) + (1 : ℝ) / x_1 ^ (6 : ℕ)) - (2 : ℝ)) / ((x_1 + (1 : ℝ) / x_1) ^ (3 : ℕ) + (x_1 ^ (3 : ℕ) + (1 : ℝ) / x_1 ^ (3 : ℕ))) = x} = 6 := by
      linarith
    exact h₅
  exact h_main
