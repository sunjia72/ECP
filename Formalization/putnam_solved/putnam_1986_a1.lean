import Mathlib
import Aesop
open BigOperators Classical ENNReal Equiv EuclideanGeometry Filter Finset Fintype Function Lex List MeasureTheory Nat ProbabilityTheory Real SimpleGraph Real Nat Topology Rat
set_option maxHeartbeats 0
theorem putnam_1986_a1 : ∃ (putnam_1986_a1_solution : ℝ), ∀ (S : Set ℝ), ∀ (f : ℝ → ℝ), ((S = {x : ℝ | x ^ (4 : ℕ) + (36 : ℝ) ≤ (13 : ℝ) * x ^ (2 : ℕ)}) ∧ (f = fun (x : ℝ) => x ^ (3 : ℕ) - (3 : ℝ) * x)) → (IsGreatest {x : ℝ | ∃ x_1 ∈ S, f x_1 = x} putnam_1986_a1_solution) := by
  use ((18 : ℝ) : ℝ)
  intro S f hf
  have hS_def : S = {x : ℝ | x ^ 4 + 36 ≤ 13 * x ^ 2} := by
    have h₁ : S = {x : ℝ | x ^ (4 : ℕ) + (36 : ℝ) ≤ (13 : ℝ) * x ^ (2 : ℕ)} := hf.1
    rw [h₁]
    <;> simp [pow_succ]
    <;> ring_nf
    <;> norm_num
    <;> simp_all [Set.ext_iff]
    <;> norm_num
    <;> aesop

  have hf_def : f = fun (x : ℝ) => x ^ 3 - 3 * x := by
    have h₂ : f = fun (x : ℝ) => x ^ (3 : ℕ) - (3 : ℝ) * x := hf.2
    rw [h₂]
    <;> simp [pow_succ]
    <;> ring_nf
    <;> norm_num
    <;> simp_all [Set.ext_iff]
    <;> norm_num
    <;> aesop

  have h3_in_S : (3 : ℝ) ∈ S := by
    rw [hS_def]
    norm_num
    <;>
    (try norm_num) <;>
    (try ring_nf) <;>
    (try norm_num) <;>
    (try linarith)

  have h_f3 : f 3 = (18 : ℝ) := by
    rw [hf_def]
    norm_num
    <;>
    (try norm_num) <;>
    (try ring_nf) <;>
    (try norm_num) <;>
    (try linarith)

  have h18_in_set : (18 : ℝ) ∈ {x : ℝ | ∃ x_1 ∈ S, f x_1 = x} := by
    have h₃ : ∃ (x_1 : ℝ), x_1 ∈ S ∧ f x_1 = (18 : ℝ) := by
      refine' ⟨3, h3_in_S, _⟩
      rw [h_f3]

    have h₄ : (18 : ℝ) ∈ {x : ℝ | ∃ x_1 ∈ S, f x_1 = x} := by

      simpa using h₃
    exact h₄

  have h_main_ineq : ∀ (x : ℝ), x ∈ S → f x ≤ (18 : ℝ) := by
    intro x hx
    have h₁ : x ∈ S := hx
    have h₂ : x ^ 4 + 36 ≤ 13 * x ^ 2 := by
      rw [hS_def] at h₁
      exact h₁
    have h₃ : x ^ 2 ≤ 9 := by
      by_contra h
      have h₄ : x ^ 2 > 9 := by linarith
      have h₅ : x ^ 4 + 36 > 13 * x ^ 2 := by
        nlinarith [sq_nonneg (x ^ 2 - 9), sq_nonneg (x ^ 2 - 4)]
      linarith
    have h₄ : x ≤ 3 := by
      nlinarith [sq_nonneg x]
    have h₅ : ∀ (x : ℝ), (x ^ 2 + 3 * x + 6 : ℝ) > 0 := by
      intro x
      nlinarith [sq_nonneg (x + 3 / 2)]
    have h₆ : (x ^ 2 + 3 * x + 6 : ℝ) > 0 := h₅ x
    have h₇ : (3 - x : ℝ) ≥ 0 := by linarith
    have h₈ : (3 - x : ℝ) * (x ^ 2 + 3 * x + 6 : ℝ) ≥ 0 := by
      nlinarith
    have h₉ : (18 : ℝ) - (x ^ 3 - 3 * x : ℝ) ≥ 0 := by
      have h₁₀ : (3 - x : ℝ) * (x ^ 2 + 3 * x + 6 : ℝ) = (18 : ℝ) - (x ^ 3 - 3 * x : ℝ) := by
        ring_nf
        <;>
        nlinarith
      linarith
    have h₁₀ : (x ^ 3 - 3 * x : ℝ) ≤ (18 : ℝ) := by linarith
    have h₁₁ : f x = (x ^ 3 - 3 * x : ℝ) := by
      rw [hf_def]
      <;> simp [pow_three]
      <;> ring_nf
    rw [h₁₁]
    linarith

  have h_is_greatest : IsGreatest {x : ℝ | ∃ x_1 ∈ S, f x_1 = x} (18 : ℝ) := by
    refine' ⟨h18_in_set, _⟩
    rintro y ⟨x₁, hx₁, hy⟩
    have h₁ : f x₁ ≤ (18 : ℝ) := h_main_ineq x₁ hx₁
    have h₂ : f x₁ = y := by linarith
    linarith

  exact h_is_greatest
