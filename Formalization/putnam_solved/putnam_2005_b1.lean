import Mathlib
import Aesop
open BigOperators Classical ENNReal Equiv EuclideanGeometry Filter Finset Fintype Function Lex List MeasureTheory Nat ProbabilityTheory Real SimpleGraph Real Nat Topology Rat
set_option maxHeartbeats 0
theorem putnam_2005_b1 : ∃ (putnam_2005_b1_solution : MvPolynomial (Fin 2) ℝ), (putnam_2005_b1_solution ≠ (0 : MvPolynomial (Fin (2 : ℕ)) ℝ) ∧ ∀ (a : ℝ), (MvPolynomial.eval fun (n : Fin (2 : ℕ)) => if n = (0 : Fin (2 : ℕ)) then (↑⌊a⌋ : ℝ) else (↑⌊(2 : ℝ) * a⌋ : ℝ) : MvPolynomial (Fin (2 : ℕ)) ℝ → ℝ) putnam_2005_b1_solution = (0 : ℝ)) := by
  use ((MvPolynomial.X (1 : Fin 2) - MvPolynomial.C (2 : ℝ) * MvPolynomial.X (0 : Fin 2)) * (MvPolynomial.X (1 : Fin 2) - MvPolynomial.C (2 : ℝ) * MvPolynomial.X (0 : Fin 2) - 1) : MvPolynomial (Fin 2) ℝ)
  have h₁ : ((MvPolynomial.X (1 : Fin 2) - MvPolynomial.C (2 : ℝ) * MvPolynomial.X (0 : Fin 2)) * (MvPolynomial.X (1 : Fin 2) - MvPolynomial.C (2 : ℝ) * MvPolynomial.X (0 : Fin 2) - 1) : MvPolynomial (Fin 2) ℝ) ≠ (0 : MvPolynomial (Fin (2 : ℕ)) ℝ) := by
    intro h
    have h₂ := congr_arg (fun p => MvPolynomial.eval (fun i => if i = (0 : Fin 2) then (0 : ℝ) else (2 : ℝ)) p) h
    simp [MvPolynomial.eval_mul, MvPolynomial.eval_sub, MvPolynomial.eval_add, MvPolynomial.eval_pow,
      MvPolynomial.eval_C, MvPolynomial.eval_X] at h₂
    <;> norm_num at h₂ <;>
    (try contradiction) <;>
    (try linarith)

  have h₂ : ∀ (a : ℝ), (MvPolynomial.eval fun (n : Fin (2 : ℕ)) => if n = (0 : Fin (2 : ℕ)) then (↑⌊a⌋ : ℝ) else (↑⌊(2 : ℝ) * a⌋ : ℝ) : MvPolynomial (Fin (2 : ℕ)) ℝ → ℝ) ((MvPolynomial.X (1 : Fin 2) - MvPolynomial.C (2 : ℝ) * MvPolynomial.X (0 : Fin 2)) * (MvPolynomial.X (1 : Fin 2) - MvPolynomial.C (2 : ℝ) * MvPolynomial.X (0 : Fin 2) - 1) : MvPolynomial (Fin 2) ℝ) = (0 : ℝ) := by
    intro a
    have h₃ : (MvPolynomial.eval (fun (n : Fin (2 : ℕ)) => if n = (0 : Fin (2 : ℕ)) then (↑⌊a⌋ : ℝ) else (↑⌊(2 : ℝ) * a⌋ : ℝ)) ((MvPolynomial.X (1 : Fin 2) - MvPolynomial.C (2 : ℝ) * MvPolynomial.X (0 : Fin 2)) * (MvPolynomial.X (1 : Fin 2) - MvPolynomial.C (2 : ℝ) * MvPolynomial.X (0 : Fin 2) - 1) : MvPolynomial (Fin 2) ℝ)) = (0 : ℝ) := by
      have h₄ : ⌊(2 : ℝ) * a⌋ = 2 * ⌊a⌋ ∨ ⌊(2 : ℝ) * a⌋ = 2 * ⌊a⌋ + 1 := by
        have h₅ : (⌊a⌋ : ℝ) ≤ a := Int.floor_le a
        have h₆ : a < (⌊a⌋ : ℝ) + 1 := Int.lt_floor_add_one a
        have h₇ : (2 : ℝ) * ⌊a⌋ ≤ (2 : ℝ) * a := by linarith
        have h₈ : (2 : ℝ) * a < (2 : ℝ) * ⌊a⌋ + 2 := by linarith
        have h₉ : ⌊(2 : ℝ) * a⌋ = 2 * ⌊a⌋ ∨ ⌊(2 : ℝ) * a⌋ = 2 * ⌊a⌋ + 1 := by
          have h₁₀ : (2 : ℝ) * ⌊a⌋ ≤ (2 : ℝ) * a := by linarith
          have h₁₁ : (2 : ℝ) * a < (2 : ℝ) * ⌊a⌋ + 2 := by linarith
          have h₁₂ : ⌊(2 : ℝ) * a⌋ = 2 * ⌊a⌋ ∨ ⌊(2 : ℝ) * a⌋ = 2 * ⌊a⌋ + 1 := by
            have h₁₃ : (2 : ℝ) * ⌊a⌋ ≤ (2 : ℝ) * a := by linarith
            have h₁₄ : (2 : ℝ) * a < (2 : ℝ) * ⌊a⌋ + 2 := by linarith
            have h₁₅ : ⌊(2 : ℝ) * a⌋ = 2 * ⌊a⌋ ∨ ⌊(2 : ℝ) * a⌋ = 2 * ⌊a⌋ + 1 := by

              have h₁₆ : (2 : ℝ) * ⌊a⌋ ≤ (2 : ℝ) * a := by linarith
              have h₁₇ : (2 : ℝ) * a < (2 : ℝ) * ⌊a⌋ + 2 := by linarith
              have h₁₈ : ⌊(2 : ℝ) * a⌋ = 2 * ⌊a⌋ ∨ ⌊(2 : ℝ) * a⌋ = 2 * ⌊a⌋ + 1 := by

                by_cases h₁₉ : (2 : ℝ) * a < (2 : ℝ) * ⌊a⌋ + 1
                · 
                  have h₂₀ : ⌊(2 : ℝ) * a⌋ = 2 * ⌊a⌋ := by
                    rw [Int.floor_eq_iff]
                    constructor <;> norm_num at h₁₉ ⊢ <;>
                    (try { nlinarith }) <;>
                    (try { linarith }) <;>
                    (try { nlinarith [Int.floor_le a, Int.lt_floor_add_one a] })
                  exact Or.inl h₂₀
                · 
                  have h₂₀ : (2 : ℝ) * a ≥ (2 : ℝ) * ⌊a⌋ + 1 := by linarith
                  have h₂₁ : ⌊(2 : ℝ) * a⌋ = 2 * ⌊a⌋ + 1 := by
                    rw [Int.floor_eq_iff]
                    constructor <;> norm_num at h₂₀ ⊢ <;>
                    (try { nlinarith }) <;>
                    (try { linarith }) <;>
                    (try { nlinarith [Int.floor_le a, Int.lt_floor_add_one a] })
                  exact Or.inr h₂₁
              exact h₁₈
            exact h₁₅
          exact h₁₂
        exact h₉


      have h₁₀ : (MvPolynomial.eval (fun (n : Fin (2 : ℕ)) => if n = (0 : Fin (2 : ℕ)) then (↑⌊a⌋ : ℝ) else (↑⌊(2 : ℝ) * a⌋ : ℝ)) ((MvPolynomial.X (1 : Fin 2) - MvPolynomial.C (2 : ℝ) * MvPolynomial.X (0 : Fin 2)) * (MvPolynomial.X (1 : Fin 2) - MvPolynomial.C (2 : ℝ) * MvPolynomial.X (0 : Fin 2) - 1) : MvPolynomial (Fin 2) ℝ)) = (0 : ℝ) := by

        cases h₄ with
        | inl h₄ =>

          have h₁₁ : ⌊(2 : ℝ) * a⌋ = 2 * ⌊a⌋ := h₄
          simp [h₁₁, MvPolynomial.eval_mul, MvPolynomial.eval_sub, MvPolynomial.eval_add,
            MvPolynomial.eval_pow, MvPolynomial.eval_C, MvPolynomial.eval_X, Fin.forall_fin_two]
          <;> norm_num <;> ring_nf <;> norm_cast <;> field_simp <;> ring_nf <;> norm_num
          <;>
          (try {
            simp_all [Int.cast_add, Int.cast_mul, Int.cast_ofNat]
            <;> ring_nf at *
            <;> norm_num at *
            <;> linarith [Int.floor_le a, Int.lt_floor_add_one a]
          })
          <;>
          (try {
            simp_all [Int.cast_add, Int.cast_mul, Int.cast_ofNat]
            <;> ring_nf at *
            <;> norm_num at *
            <;> linarith [Int.floor_le a, Int.lt_floor_add_one a]
          })
        | inr h₄ =>

          have h₁₁ : ⌊(2 : ℝ) * a⌋ = 2 * ⌊a⌋ + 1 := h₄
          simp [h₁₁, MvPolynomial.eval_mul, MvPolynomial.eval_sub, MvPolynomial.eval_add,
            MvPolynomial.eval_pow, MvPolynomial.eval_C, MvPolynomial.eval_X, Fin.forall_fin_two]
          <;> norm_num <;> ring_nf <;> norm_cast <;> field_simp <;> ring_nf <;> norm_num
          <;>
          (try {
            simp_all [Int.cast_add, Int.cast_mul, Int.cast_ofNat]
            <;> ring_nf at *
            <;> norm_num at *
            <;> linarith [Int.floor_le a, Int.lt_floor_add_one a]
          })
          <;>
          (try {
            simp_all [Int.cast_add, Int.cast_mul, Int.cast_ofNat]
            <;> ring_nf at *
            <;> norm_num at *
            <;> linarith [Int.floor_le a, Int.lt_floor_add_one a]
          })
      exact h₁₀
    exact h₃

  exact ⟨h₁, h₂⟩
