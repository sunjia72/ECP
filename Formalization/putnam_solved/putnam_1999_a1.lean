import Mathlib
import Aesop
open BigOperators Classical ENNReal Equiv EuclideanGeometry Filter Finset Fintype Function Lex List MeasureTheory Nat ProbabilityTheory Real SimpleGraph Real Nat Topology Rat
set_option maxHeartbeats 0
theorem putnam_1999_a1 : ∃ (putnam_1999_a1_solution : Prop), (putnam_1999_a1_solution ↔ ∃ (f : Polynomial ℝ) (g : Polynomial ℝ) (h : Polynomial ℝ), ∀ (x : ℝ), |Polynomial.eval x f| - |Polynomial.eval x g| + Polynomial.eval x h = if x < (-1 : ℝ) then (-1 : ℝ) else if x ≤ (0 : ℝ) then (3 : ℝ) * x + (2 : ℝ) else (-2 : ℝ) * x + (2 : ℝ)) := by
  use (True : Prop)
  have h_main : ∃ (f : Polynomial ℝ) (g : Polynomial ℝ) (h : Polynomial ℝ), ∀ (x : ℝ), |Polynomial.eval x f| - |Polynomial.eval x g| + Polynomial.eval x h = if x < (-1 : ℝ) then (-1 : ℝ) else if x ≤ (0 : ℝ) then (3 : ℝ) * x + (2 : ℝ) else (-2 : ℝ) * x + (2 : ℝ) := by
    use (Polynomial.C (3 / 2 : ℝ) * (Polynomial.X + Polynomial.C 1))
    use (Polynomial.C (5 / 2 : ℝ) * Polynomial.X)
    use (Polynomial.C (-1 : ℝ) * Polynomial.X + Polynomial.C (1 / 2 : ℝ))
    intro x
    have h₁ : Polynomial.eval x (Polynomial.C (3 / 2 : ℝ) * (Polynomial.X + Polynomial.C 1)) = (3 / 2 : ℝ) * (x + 1) := by
      simp [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
      <;> ring_nf
      <;> norm_num
      <;> linarith
    have h₂ : Polynomial.eval x (Polynomial.C (5 / 2 : ℝ) * Polynomial.X) = (5 / 2 : ℝ) * x := by
      simp [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
      <;> ring_nf
      <;> norm_num
      <;> linarith
    have h₃ : Polynomial.eval x (Polynomial.C (-1 : ℝ) * Polynomial.X + Polynomial.C (1 / 2 : ℝ)) = (-1 : ℝ) * x + (1 / 2 : ℝ) := by
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
      <;> ring_nf
      <;> norm_num
      <;> linarith
    rw [h₁, h₂, h₃]
    have h₄ : |(3 / 2 : ℝ) * (x + 1)| - |(5 / 2 : ℝ) * x| + ((-1 : ℝ) * x + (1 / 2 : ℝ)) = if x < (-1 : ℝ) then (-1 : ℝ) else if x ≤ (0 : ℝ) then (3 : ℝ) * x + (2 : ℝ) else (-2 : ℝ) * x + (2 : ℝ) := by
      split_ifs with h₅ h₆
      · 
        have h₇ : x < (-1 : ℝ) := h₅
        have h₈ : (x + 1 : ℝ) < 0 := by linarith
        have h₉ : (x : ℝ) < 0 := by linarith
        have h₁₀ : |(3 / 2 : ℝ) * (x + 1)| = -(3 / 2 : ℝ) * (x + 1) := by
          rw [abs_of_neg (by
            have h₁₁ : (3 / 2 : ℝ) * (x + 1) < 0 := by
              nlinarith
            linarith)]
          <;> ring_nf
          <;> linarith
        have h₁₁ : |(5 / 2 : ℝ) * x| = -(5 / 2 : ℝ) * x := by
          rw [abs_of_neg (by
            have h₁₂ : (5 / 2 : ℝ) * x < 0 := by
              nlinarith
            linarith)]
          <;> ring_nf
          <;> linarith
        rw [h₁₀, h₁₁]
        ring_nf at *
        <;> nlinarith
      · 
        have h₇ : ¬x < (-1 : ℝ) := by tauto
        have h₈ : x ≤ (0 : ℝ) := h₆
        have h₉ : (x + 1 : ℝ) ≥ 0 := by linarith
        have h₁₀ : (x : ℝ) ≤ 0 := by linarith
        have h₁₁ : |(3 / 2 : ℝ) * (x + 1)| = (3 / 2 : ℝ) * (x + 1) := by
          rw [abs_of_nonneg (by
            have h₁₂ : (3 / 2 : ℝ) * (x + 1) ≥ 0 := by
              nlinarith
            linarith)]
          <;> ring_nf
          <;> linarith
        have h₁₂ : |(5 / 2 : ℝ) * x| = -(5 / 2 : ℝ) * x := by
          rw [abs_of_nonpos (by
            have h₁₃ : (5 / 2 : ℝ) * x ≤ 0 := by
              nlinarith
            linarith)]
          <;> ring_nf
          <;> linarith
        rw [h₁₁, h₁₂]
        ring_nf at *
        <;> nlinarith
      · 
        have h₇ : ¬x < (-1 : ℝ) := by tauto
        have h₈ : ¬x ≤ (0 : ℝ) := by tauto
        have h₉ : (x : ℝ) > 0 := by
          by_contra h₉
          have h₁₀ : x ≤ 0 := by linarith
          contradiction
        have h₁₀ : (x + 1 : ℝ) > 0 := by linarith
        have h₁₁ : |(3 / 2 : ℝ) * (x + 1)| = (3 / 2 : ℝ) * (x + 1) := by
          rw [abs_of_nonneg (by
            have h₁₂ : (3 / 2 : ℝ) * (x + 1) ≥ 0 := by
              nlinarith
            linarith)]
          <;> ring_nf
          <;> linarith
        have h₁₂ : |(5 / 2 : ℝ) * x| = (5 / 2 : ℝ) * x := by
          rw [abs_of_nonneg (by
            have h₁₃ : (5 / 2 : ℝ) * x ≥ 0 := by
              nlinarith
            linarith)]
          <;> ring_nf
          <;> linarith
        rw [h₁₁, h₁₂]
        ring_nf at *
        <;> nlinarith
    rw [h₄]
    <;> simp_all

  have h_final : ((True : Prop) ↔ ∃ (f : Polynomial ℝ) (g : Polynomial ℝ) (h : Polynomial ℝ), ∀ (x : ℝ), |Polynomial.eval x f| - |Polynomial.eval x g| + Polynomial.eval x h = if x < (-1 : ℝ) then (-1 : ℝ) else if x ≤ (0 : ℝ) then (3 : ℝ) * x + (2 : ℝ) else (-2 : ℝ) * x + (2 : ℝ)) := by
    constructor
    · intro _
      exact h_main
    · intro h
      trivial

  exact h_final
