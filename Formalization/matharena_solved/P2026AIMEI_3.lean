import Mathlib
import Aesop
open BigOperators Classical ENNReal Equiv EuclideanGeometry Filter Finset Fintype Function Lex List MeasureTheory Nat ProbabilityTheory Real SimpleGraph Real Nat Topology Rat
set_option maxHeartbeats 0
theorem P2026AIMEI_3 : ∃ (P2026AIMEI_3_answer : Nat), (IsLeast {s : ℕ | ∃ (p : ℕ) (q : ℕ), p.Coprime q ∧ ((158 : ℚ) ^ (2 : ℕ) - (42 : ℚ) ^ (2 : ℕ)) / (200 : ℚ) ^ (2 : ℕ) = (↑p : ℚ) / (↑q : ℚ) ∧ s = p + q} P2026AIMEI_3_answer) := by
  use (79 : Nat)
  have h_main : IsLeast {s : ℕ | ∃ (p : ℕ) (q : ℕ), p.Coprime q ∧ ((158 : ℚ) ^ (2 : ℕ) - (42 : ℚ) ^ (2 : ℕ)) / (200 : ℚ) ^ (2 : ℕ) = (↑p : ℚ) / (↑q : ℚ) ∧ s = p + q} 79 := by
    refine' ⟨_, _⟩
    · 
      have h₁ : (29 : ℕ).Coprime 50 := by decide
      have h₂ : ((158 : ℚ) ^ 2 - (42 : ℚ) ^ 2) / (200 : ℚ) ^ 2 = (29 : ℚ) / 50 := by
        norm_num [pow_two]
        <;> field_simp
        <;> ring_nf
        <;> norm_num
      have h₃ : (79 : ℕ) = 29 + 50 := by norm_num
      refine' ⟨29, 50, h₁, _, by norm_num⟩

      norm_num [h₂] at h₂ ⊢
      <;>
      (try norm_num) <;>
      (try simp_all [div_eq_mul_inv]) <;>
      (try ring_nf at * <;> norm_num at * <;> linarith)
      <;>
      (try field_simp at * <;> ring_nf at * <;> norm_num at * <;> linarith)
    · 
      intro s hs
      rcases hs with ⟨p, q, hcoprime, hrat, rfl⟩
      have h₁ : ((158 : ℚ) ^ 2 - (42 : ℚ) ^ 2) / (200 : ℚ) ^ 2 = (29 : ℚ) / 50 := by
        norm_num [pow_two]
        <;> field_simp
        <;> ring_nf
        <;> norm_num
      have h₂ : ((158 : ℚ) ^ 2 - (42 : ℚ) ^ 2) / (200 : ℚ) ^ 2 = (p : ℚ) / q := by
        simpa using hrat
      have h₃ : (p : ℚ) / q = (29 : ℚ) / 50 := by linarith
      have h₄ : (q : ℚ) ≠ 0 := by
        by_contra h
        rw [h] at h₃
        norm_num at h₃
        <;>
        (try simp_all [div_eq_mul_inv]) <;>
        (try ring_nf at * <;> norm_num at * <;> linarith)
        <;>
        (try field_simp at * <;> ring_nf at * <;> norm_num at * <;> linarith)
      have h₅ : (p : ℚ) * 50 = (q : ℚ) * 29 := by
        field_simp at h₃
        <;> ring_nf at h₃ ⊢ <;> norm_cast at h₃ ⊢ <;>
        (try linarith) <;>
        (try nlinarith)
        <;>
        (try
          {
            norm_num at h₃ ⊢
            <;>
            (try ring_nf at h₃ ⊢)
            <;>
            (try norm_cast at h₃ ⊢)
            <;>
            (try linarith)
          })
        <;>
        (try
          {
            simp_all [div_eq_mul_inv]
            <;>
            ring_nf at *
            <;>
            norm_num at *
            <;>
            linarith
          })
      have h₆ : (p : ℕ) * 50 = (q : ℕ) * 29 := by
        norm_cast at h₅ ⊢
        <;>
        (try ring_nf at h₅ ⊢) <;>
        (try norm_num at h₅ ⊢) <;>
        (try linarith)
      have h₇ : p * 50 = q * 29 := by simpa using h₆
      have h₈ : p + q ≥ 79 := by
        by_contra h
        have h₉ : p + q < 79 := by linarith
        have h₁₀ : p ≤ 78 := by
          omega
        have h₁₁ : q ≤ 78 := by
          omega

        have h₁₂ : p * 50 = q * 29 := by simpa using h₇
        have h₁₃ : p ≥ 0 := by omega
        have h₁₄ : q ≥ 1 := by
          by_contra h₁₄
          have h₁₅ : q = 0 := by omega
          simp [h₁₅] at h₁₂ h₄ h₃ hrat
          <;> norm_num at h₁₂ h₄ h₃ hrat <;>
          (try contradiction) <;>
          (try linarith)

        interval_cases p <;> norm_num at h₁₂ ⊢ <;>
          (try omega) <;>
          (try {
            have h₁₅ : q ≤ 78 := by omega
            interval_cases q <;> norm_num at h₁₂ hcoprime ⊢ <;>
              (try omega) <;>
              (try {
                norm_num [Nat.coprime_iff_gcd_eq_one, Nat.gcd_eq_right] at hcoprime ⊢ <;>
                  (try contradiction)
              })
          })
      omega
  exact h_main
