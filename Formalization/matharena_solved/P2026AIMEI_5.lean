import Mathlib
import Aesop
open BigOperators Classical ENNReal Equiv EuclideanGeometry Filter Finset Fintype Function Lex List MeasureTheory Nat ProbabilityTheory Real SimpleGraph Real Nat Topology Rat
set_option maxHeartbeats 0
theorem P2026AIMEI_5 : ∃ (P2026AIMEI_5_answer : Nat), ∀ (θ : ℝ), (((0 : ℝ) < θ ∧ θ < π / (2 : ℝ)) ∧ (√(((2 : ℝ) - cos θ) ^ (2 : ℕ) + sin θ ^ (2 : ℕ)) = (4 / 3 : ℝ))) → (Coprime (29 : ℕ) (36 : ℕ) ∧ cos θ = (29 / 36 : ℝ) ∧ (29 : ℕ) + (36 : ℕ) = P2026AIMEI_5_answer) := by
  use (65 : Nat)
  intro θ h
  have h₁ : cos θ = (29 / 36 : ℝ) := by
    have h₂ : √(((2 : ℝ) - cos θ) ^ (2 : ℕ) + sin θ ^ (2 : ℕ)) = (4 / 3 : ℝ) := h.2
    have h₃ : 0 ≤ ((2 : ℝ) - cos θ) ^ (2 : ℕ) + sin θ ^ (2 : ℕ) := by
      positivity
    have h₄ : ((2 : ℝ) - cos θ) ^ (2 : ℕ) + sin θ ^ (2 : ℕ) = (16 / 9 : ℝ) := by
      have h₅ : √(((2 : ℝ) - cos θ) ^ (2 : ℕ) + sin θ ^ (2 : ℕ)) = (4 / 3 : ℝ) := h₂
      have h₆ : 0 ≤ ((2 : ℝ) - cos θ) ^ (2 : ℕ) + sin θ ^ (2 : ℕ) := h₃
      have h₇ : √(((2 : ℝ) - cos θ) ^ (2 : ℕ) + sin θ ^ (2 : ℕ)) ^ 2 = ((2 : ℝ) - cos θ) ^ (2 : ℕ) + sin θ ^ (2 : ℕ) := by
        rw [Real.sq_sqrt] <;> linarith
      have h₈ : √(((2 : ℝ) - cos θ) ^ (2 : ℕ) + sin θ ^ (2 : ℕ)) ^ 2 = (4 / 3 : ℝ) ^ 2 := by
        rw [h₅]
      have h₉ : ((2 : ℝ) - cos θ) ^ (2 : ℕ) + sin θ ^ (2 : ℕ) = (4 / 3 : ℝ) ^ 2 := by
        linarith
      norm_num at h₉ ⊢
      <;>
      (try ring_nf at h₉ ⊢) <;>
      (try nlinarith [sin_sq_add_cos_sq θ]) <;>
      (try linarith) <;>
      (try nlinarith)
      <;>
      (try
        {
          simp_all [pow_two]
          <;>
          ring_nf at *
          <;>
          nlinarith [sin_sq_add_cos_sq θ]
        })
      <;>
      (try
        {
          simp_all [pow_two]
          <;>
          ring_nf at *
          <;>
          nlinarith [sin_sq_add_cos_sq θ]
        })
    have h₅ : ((2 : ℝ) - cos θ) ^ 2 + sin θ ^ 2 = (16 / 9 : ℝ) := by
      norm_num [pow_two] at h₄ ⊢
      <;>
      (try ring_nf at h₄ ⊢) <;>
      (try nlinarith [sin_sq_add_cos_sq θ]) <;>
      (try linarith) <;>
      (try nlinarith)
      <;>
      (try
        {
          simp_all [pow_two]
          <;>
          ring_nf at *
          <;>
          nlinarith [sin_sq_add_cos_sq θ]
        })
      <;>
      (try
        {
          simp_all [pow_two]
          <;>
          ring_nf at *
          <;>
          nlinarith [sin_sq_add_cos_sq θ]
        })
    have h₆ : 4 - 4 * cos θ + cos θ ^ 2 + sin θ ^ 2 = (16 / 9 : ℝ) := by
      have h₇ : ((2 : ℝ) - cos θ) ^ 2 = 4 - 4 * cos θ + cos θ ^ 2 := by
        ring_nf
      rw [h₇] at h₅
      linarith
    have h₇ : 5 - 4 * cos θ = (16 / 9 : ℝ) := by
      have h₈ : cos θ ^ 2 + sin θ ^ 2 = 1 := by
        rw [Real.cos_sq_add_sin_sq]
      nlinarith
    have h₈ : 4 * cos θ = (29 / 9 : ℝ) := by
      linarith
    have h₉ : cos θ = (29 / 36 : ℝ) := by
      linarith
    exact h₉

  have h₂ : Coprime (29 : ℕ) (36 : ℕ) := by
    norm_num [Nat.coprime_iff_gcd_eq_one, Nat.gcd_eq_right]
    <;>
    decide

  have h₃ : (29 : ℕ) + (36 : ℕ) = (65 : ℕ) := by
    norm_num

  exact ⟨h₂, h₁, h₃⟩
