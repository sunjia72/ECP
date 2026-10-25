import Mathlib
import Aesop
open BigOperators Classical ENNReal Equiv EuclideanGeometry Filter Finset Fintype Function Lex List MeasureTheory Nat ProbabilityTheory Real SimpleGraph Real Nat Topology Rat
set_option maxHeartbeats 0
theorem putnam_1985_a4 : ∃ (putnam_1985_a4_solution : Set (Fin 100)), ∀ (a : ℕ → ℕ), ((a (1 : ℕ) = (3 : ℕ)) ∧ (∀ i ≥ (1 : ℕ), a (i + (1 : ℕ)) = (3 : ℕ) ^ a i)) → ({k : Fin (100 : ℕ) | ∀ (N : ℕ), ∃ i ≥ N, a i % (100 : ℕ) = (↑k : ℕ)} = putnam_1985_a4_solution) := by
  use (({(87 : Fin 100)} : Set (Fin 100)) : Set (Fin 100))
  intro a h
  have h3_pow_20 : (3 : ℕ) ^ 20 % 100 = 1 := by
    norm_num [pow_succ]
    <;> rfl

  have h3_pow_100 : (3 : ℕ) ^ 100 % 100 = 1 := by
    have h₁ : (3 : ℕ) ^ 100 % 100 = 1 := by
      norm_num [pow_succ, Nat.mul_mod, Nat.pow_mod]
      <;> rfl
    exact h₁

  have h_a3 : a 3 % 100 = 87 := by
    have h₁ : a 1 = 3 := h.1
    have h₂ : ∀ i ≥ 1, a (i + 1) = 3 ^ a i := h.2
    have h₃ : a 2 = 3 ^ a 1 := by
      have h₄ := h₂ 1 (by norm_num)
      simpa using h₄
    have h₄ : a 2 = 27 := by
      rw [h₃, h₁]
      <;> norm_num
    have h₅ : a 3 = 3 ^ a 2 := by
      have h₆ := h₂ 2 (by norm_num)
      simpa using h₆
    have h₆ : a 3 = 3 ^ 27 := by
      rw [h₅, h₄]
      <;> norm_num
    have h₇ : a 3 % 100 = 87 := by
      rw [h₆]
      norm_num [pow_succ, Nat.mul_mod, Nat.pow_mod]
      <;> rfl
    exact h₇

  have h_inductive_step : ∀ (k : ℕ), k ≥ 3 → a k % 100 = 87 → a (k + 1) % 100 = 87 := by
    intro k hk h_mod
    have h₁ : ∀ i ≥ 1, a (i + 1) = 3 ^ a i := h.2
    have h₂ : a (k + 1) = 3 ^ a k := by
      have h₃ : k ≥ 1 := by linarith
      have h₄ := h₁ k h₃
      simpa using h₄
    rw [h₂]
    have h₃ : a k % 100 = 87 := h_mod
    have h₄ : (3 : ℕ) ^ a k % 100 = 87 := by
      have h₅ : a k % 100 = 87 := h₃
      have h₆ : (3 : ℕ) ^ a k % 100 = 87 := by
        have h₇ : a k % 100 = 87 := h₅
        have h₈ : (3 : ℕ) ^ a k % 100 = (3 : ℕ) ^ (a k % 100) % 100 := by
          have h₉ : (3 : ℕ) ^ a k % 100 = (3 : ℕ) ^ (a k % 100) % 100 := by
            rw [← Nat.mod_add_div (a k) 100]
            simp [pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, h3_pow_100]
            <;> norm_num <;>
            simp_all [Nat.pow_mod, Nat.mul_mod]
            <;>
            ring_nf at *
            <;>
            omega
          exact h₉
        rw [h₈]
        have h₉ : (3 : ℕ) ^ (a k % 100) % 100 = (3 : ℕ) ^ 87 % 100 := by
          rw [h₇]
        rw [h₉]
        norm_num [pow_succ, Nat.mul_mod, Nat.pow_mod]
        <;> rfl
      exact h₆
    exact h₄

  have h_a_ge_3 : ∀ (n : ℕ), n ≥ 3 → a n % 100 = 87 := by
    intro n hn
    induction' hn with n hn IH
    · 
      exact h_a3
    · 
      have h₁ : a (n + 1) % 100 = 87 := h_inductive_step n hn IH
      simpa using h₁

  have h_main : {k : Fin (100 : ℕ) | ∀ (N : ℕ), ∃ i ≥ N, a i % (100 : ℕ) = (↑k : ℕ)} = ({(87 : Fin 100)} : Set (Fin 100)) := by
    apply Set.Subset.antisymm
    · 
      intro k hk
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hk ⊢
      have h₁ : ∀ (N : ℕ), ∃ i ≥ N, a i % 100 = (k : ℕ) := hk
      have h₂ : (k : ℕ) < 100 := by
        exact Fin.is_lt k

      have h₃ : (k : ℕ) = 87 := by
        by_contra h

        have h₄ : (k : ℕ) ≠ 87 := h
        have h₅ : ∃ (N : ℕ), ∀ (i : ℕ), i ≥ N → a i % 100 ≠ (k : ℕ) := by
          use 3
          intro i hi
          have h₆ : a i % 100 = 87 := h_a_ge_3 i hi
          have h₇ : (k : ℕ) ≠ 87 := h₄
          omega

        obtain ⟨N, hN⟩ := h₅
        have h₆ := h₁ N
        obtain ⟨i, hi, h₇⟩ := h₆
        have h₈ : a i % 100 = (k : ℕ) := h₇
        have h₉ : i ≥ N := hi
        have h₁₀ : a i % 100 ≠ (k : ℕ) := hN i (by linarith)
        contradiction

      have h₄ : k = (87 : Fin 100) := by
        apply Fin.ext
        <;> simp_all [Fin.val_mk]
        <;> omega
      simp_all
    · 
      intro k hk
      simp only [Set.mem_singleton_iff] at hk ⊢
      rw [hk]

      intro N
      use max N 3
      constructor
      · 
        exact le_max_left N 3
      · 
        have h₁ : a (max N 3) % 100 = 87 := by
          have h₂ : max N 3 ≥ 3 := by
            apply le_max_right
          have h₃ : a (max N 3) % 100 = 87 := h_a_ge_3 (max N 3) h₂
          exact h₃

        have h₂ : (87 : ℕ) < 100 := by norm_num
        simp_all [Fin.val_mk]
        <;> omega

  exact h_main
