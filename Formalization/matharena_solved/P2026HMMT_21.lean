import Mathlib
import Aesop
open BigOperators Classical ENNReal Equiv EuclideanGeometry Filter Finset Fintype Function Lex List MeasureTheory Nat ProbabilityTheory Real SimpleGraph Real Nat Topology Rat
set_option maxHeartbeats 0
theorem P2026HMMT_21 : ∃ (P2026HMMT_21_answer : ℝ), ∀ (A B C D W X Y Z : ℝ × ℝ), ((A = ((0 : ℝ), (0 : ℝ)) ∧ B = ((12 : ℝ), (0 : ℝ)) ∧ C = ((12 : ℝ), (12 : ℝ)) ∧ D = ((0 : ℝ), (12 : ℝ))) ∧ (W = ((0 : ℝ), (4 : ℝ))) ∧ (X = ((5 : ℝ), (0 : ℝ))) ∧ (Y = (X.1 - (X.2 - W.2), X.2 + (X.1 - W.1)) ∧ Z = (W.1 - (X.2 - W.2), W.2 + (X.1 - W.1)) ∨ Y = (X.1 + (X.2 - W.2), X.2 - (X.1 - W.1)) ∧ Z = (W.1 + (X.2 - W.2), W.2 - (X.1 - W.1))) ∧ ((0 : ℝ) < Y.1 ∧ Y.1 < (12 : ℝ) ∧ (0 : ℝ) < Y.2 ∧ Y.2 < (12 : ℝ)) ∧ ((0 : ℝ) < Z.1 ∧ Z.1 < (12 : ℝ) ∧ (0 : ℝ) < Z.2 ∧ Z.2 < (12 : ℝ))) → (let triangleArea := |B.1 * (C.2 - Y.2) + C.1 * (Y.2 - B.2) + Y.1 * (B.2 - C.2)| / (2 : ℝ); triangleArea = P2026HMMT_21_answer) := by
  use ((18 : ℝ) : ℝ)
  intro A B C D W X Y Z h
  have h₁ : B = ((12 : ℝ), (0 : ℝ)) := by
    have h₂ : A = ((0 : ℝ), (0 : ℝ)) ∧ B = ((12 : ℝ), (0 : ℝ)) ∧ C = ((12 : ℝ), (12 : ℝ)) ∧ D = ((0 : ℝ), (12 : ℝ)) := by
      exact h.1
    exact h₂.2.1

  have h₂ : C = ((12 : ℝ), (12 : ℝ)) := by
    have h₃ : A = ((0 : ℝ), (0 : ℝ)) ∧ B = ((12 : ℝ), (0 : ℝ)) ∧ C = ((12 : ℝ), (12 : ℝ)) ∧ D = ((0 : ℝ), (12 : ℝ)) := by
      exact h.1
    exact h₃.2.2.1

  have h₃ : W = ((0 : ℝ), (4 : ℝ)) := by
    have h₄ : W = ((0 : ℝ), (4 : ℝ)) := by
      exact h.2.1
    exact h₄

  have h₄ : X = ((5 : ℝ), (0 : ℝ)) := by
    have h₅ : X = ((5 : ℝ), (0 : ℝ)) := by
      exact h.2.2.1
    exact h₅

  have h₅ : (Y = (X.1 - (X.2 - W.2), X.2 + (X.1 - W.1)) ∧ Z = (W.1 - (X.2 - W.2), W.2 + (X.1 - W.1))) ∨ (Y = (X.1 + (X.2 - W.2), X.2 - (X.1 - W.1)) ∧ Z = (W.1 + (X.2 - W.2), W.2 - (X.1 - W.1))) := by
    have h₅₁ : (Y = (X.1 - (X.2 - W.2), X.2 + (X.1 - W.1)) ∧ Z = (W.1 - (X.2 - W.2), W.2 + (X.1 - W.1))) ∨ (Y = (X.1 + (X.2 - W.2), X.2 - (X.1 - W.1)) ∧ Z = (W.1 + (X.2 - W.2), W.2 - (X.1 - W.1))) := by
      exact h.2.2.2.1
    exact h₅₁

  have h₆ : (0 : ℝ) < Y.1 ∧ Y.1 < (12 : ℝ) ∧ (0 : ℝ) < Y.2 ∧ Y.2 < (12 : ℝ) := by
    exact h.2.2.2.2.1

  have h₇ : (0 : ℝ) < Z.1 ∧ Z.1 < (12 : ℝ) ∧ (0 : ℝ) < Z.2 ∧ Z.2 < (12 : ℝ) := by
    exact h.2.2.2.2.2

  have h_main : (let triangleArea := |B.1 * (C.2 - Y.2) + C.1 * (Y.2 - B.2) + Y.1 * (B.2 - C.2)| / (2 : ℝ); triangleArea = ((18 : ℝ) : ℝ)) := by
    have h₈ : B.1 = (12 : ℝ) := by
      simp [h₁]
      <;> norm_num
    have h₉ : B.2 = (0 : ℝ) := by
      simp [h₁]
      <;> norm_num
    have h₁₀ : C.1 = (12 : ℝ) := by
      simp [h₂]
      <;> norm_num
    have h₁₁ : C.2 = (12 : ℝ) := by
      simp [h₂]
      <;> norm_num
    have h₁₂ : W.1 = (0 : ℝ) := by
      simp [h₃]
      <;> norm_num
    have h₁₃ : W.2 = (4 : ℝ) := by
      simp [h₃]
      <;> norm_num
    have h₁₄ : X.1 = (5 : ℝ) := by
      simp [h₄]
      <;> norm_num
    have h₁₅ : X.2 = (0 : ℝ) := by
      simp [h₄]
      <;> norm_num

    cases h₅ with
    | inl h₅ =>

      have h₁₆ : Y = (X.1 - (X.2 - W.2), X.2 + (X.1 - W.1)) := h₅.1
      have h₁₇ : Z = (W.1 - (X.2 - W.2), W.2 + (X.1 - W.1)) := h₅.2
      have h₁₈ : Y.1 = (9 : ℝ) := by
        simp [h₁₆, h₁₄, h₁₅, h₁₂, h₁₃]
        <;> norm_num
      have h₁₉ : Y.2 = (5 : ℝ) := by
        simp [h₁₆, h₁₄, h₁₅, h₁₂, h₁₃]
        <;> norm_num
      dsimp only
      rw [h₈, h₉, h₁₀, h₁₁]
      rw [h₁₉]
      rw [h₁₈]
      norm_num [abs_of_pos]
      <;>
      (try norm_num) <;>
      (try linarith) <;>
      (try ring_nf) <;>
      (try field_simp) <;>
      (try norm_num) <;>
      (try linarith)
    | inr h₅ =>

      have h₁₆ : Y = (X.1 + (X.2 - W.2), X.2 - (X.1 - W.1)) := h₅.1
      have h₁₇ : Z = (W.1 + (X.2 - W.2), W.2 - (X.1 - W.1)) := h₅.2
      have h₁₈ : Y.2 = (-5 : ℝ) := by
        simp [h₁₆, h₁₄, h₁₅, h₁₂, h₁₃]
        <;> norm_num
      have h₁₉ : (0 : ℝ) < Y.2 := h₆.2.2.1
      linarith

  exact h_main
