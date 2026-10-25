import Mathlib
import Aesop
open BigOperators Classical ENNReal Equiv EuclideanGeometry Filter Finset Fintype Function Lex List MeasureTheory Nat ProbabilityTheory Real SimpleGraph Real Nat Topology Rat
set_option maxHeartbeats 0
theorem putnam_1985_a3 : ∃ (putnam_1985_a3_solution : ℝ → ℝ), ∀ (d : ℝ), ∀ (a : ℕ → ℕ → ℝ), ((∀ (m : ℕ), a m (0 : ℕ) = d / (2 : ℝ) ^ m) ∧ (∀ (m j : ℕ), a m (j + (1 : ℕ)) = a m j ^ (2 : ℕ) + (2 : ℝ) * a m j)) → (Tendsto (fun (n : ℕ) => a n n) atTop (𝓝 (putnam_1985_a3_solution d))) := by
  use (fun d : ℝ => Real.exp d - 1 : ℝ → ℝ)
  intro d a h
  have h₁ : ∀ (m j : ℕ), a m j + 1 = (a m 0 + 1) ^ (2 : ℕ) ^ j := by
    intro m j
    have h₂ : ∀ (j : ℕ), a m j + 1 = (a m 0 + 1) ^ (2 : ℕ) ^ j := by
      intro j
      induction j with
      | zero =>
        norm_num [pow_zero]
        <;>
        (try ring_nf) <;>
        (try simp_all) <;>
        (try norm_num) <;>
        (try linarith)
        <;>
        (try
          {
            have h₃ := h.1 m
            have h₄ := h.1 0
            norm_num at h₃ h₄ ⊢
            <;>
            linarith
          })
      | succ j ih =>
        have h₃ := h.2 m j
        have h₄ : a m (j + 1) + 1 = (a m j + 1) ^ 2 := by
          calc
            a m (j + 1) + 1 = (a m j ^ 2 + 2 * a m j) + 1 := by
              rw [h₃]
              <;> ring_nf
            _ = (a m j + 1) ^ 2 := by ring
        calc
          a m (j + 1) + 1 = (a m j + 1) ^ 2 := by rw [h₄]
          _ = ((a m 0 + 1) ^ (2 : ℕ) ^ j) ^ 2 := by rw [ih]
          _ = (a m 0 + 1) ^ ((2 : ℕ) ^ j * 2) := by
            rw [← pow_mul]
            <;> ring_nf
          _ = (a m 0 + 1) ^ (2 : ℕ) ^ (j + 1) := by
            have h₅ : (2 : ℕ) ^ j * 2 = (2 : ℕ) ^ (j + 1) := by
              calc
                (2 : ℕ) ^ j * 2 = (2 : ℕ) ^ j * 2 ^ 1 := by norm_num
                _ = 2 ^ (j + 1) := by
                  rw [← pow_add]
                  <;> ring_nf
            rw [h₅]
    exact h₂ j
  have h₂ : ∀ (n : ℕ), a n n + 1 = (d / (2 : ℝ) ^ n + 1) ^ (2 : ℕ) ^ n := by
    intro n
    have h₃ : a n n + 1 = (a n 0 + 1) ^ (2 : ℕ) ^ n := h₁ n n
    have h₄ : a n 0 = d / (2 : ℝ) ^ n := h.1 n
    rw [h₃, h₄]
    <;>
    (try ring_nf) <;>
    (try simp_all) <;>
    (try norm_num) <;>
    (try linarith)
    <;>
    (try
      {
        have h₅ := h.1 0
        have h₆ := h.1 1
        norm_num at h₅ h₆ ⊢
        <;>
        linarith
      })

  have h₃ : Tendsto (fun (n : ℕ) => (d / (2 : ℝ) ^ n + 1 : ℝ) ^ (2 : ℕ) ^ n) atTop (𝓝 (Real.exp d)) := by
    have h₄ : Tendsto (fun (n : ℕ) => (1 + d / (2 ^ n : ℝ)) ^ (2 ^ n : ℕ)) atTop (𝓝 (Real.exp d)) := by
      have h₅ : Tendsto (fun n : ℕ => (1 + d / (n : ℝ)) ^ n) atTop (𝓝 (Real.exp d)) := by

        apply tendsto_one_plus_div_pow_exp

      have h₆ : Tendsto (fun n : ℕ => (1 + d / (2 ^ n : ℝ)) ^ (2 ^ n : ℕ)) atTop (𝓝 (Real.exp d)) := by

        have h₇ : Tendsto (fun n : ℕ => (2 : ℕ) ^ n) atTop atTop := by

          exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num)

        have h₈ : Tendsto (fun n : ℕ => (1 + d / (n : ℝ)) ^ n) atTop (𝓝 (Real.exp d)) := h₅

        have h₉ : Tendsto (fun n : ℕ => (1 + d / (2 ^ n : ℝ)) ^ (2 ^ n : ℕ)) atTop (𝓝 (Real.exp d)) := by

          have h₁₀ : (fun n : ℕ => (1 + d / (2 ^ n : ℝ)) ^ (2 ^ n : ℕ)) = (fun n : ℕ => (1 + d / (n : ℝ)) ^ n) ∘ (fun n : ℕ => 2 ^ n) := by
            funext n
            <;> simp [Nat.cast_pow]
            <;> field_simp [Nat.cast_pow]
            <;> ring_nf
            <;> norm_cast
            <;> simp [pow_mul]
            <;> field_simp [pow_mul]
            <;> ring_nf
            <;> norm_cast
          rw [h₁₀]

          have h₁₁ : Tendsto (fun n : ℕ => (2 : ℕ) ^ n) atTop atTop := h₇
          have h₁₂ : Tendsto (fun n : ℕ => (1 + d / (n : ℝ)) ^ n) atTop (𝓝 (Real.exp d)) := h₈

          exact h₁₂.comp h₁₁
        exact h₉
      exact h₆

    have h₅ : (fun (n : ℕ) => (d / (2 : ℝ) ^ n + 1 : ℝ) ^ (2 : ℕ) ^ n) = (fun (n : ℕ) => (1 + d / (2 ^ n : ℝ)) ^ (2 ^ n : ℕ)) := by
      funext n
      have h₆ : (d / (2 : ℝ) ^ n + 1 : ℝ) = (1 + d / (2 ^ n : ℝ)) := by
        ring_nf
        <;> field_simp [pow_ne_zero]
        <;> ring_nf
        <;> norm_cast
        <;> field_simp [pow_ne_zero]
        <;> ring_nf
        <;> norm_cast
      rw [h₆]
      <;> norm_cast
      <;> simp [pow_mul]
      <;> field_simp [pow_mul]
      <;> ring_nf
      <;> norm_cast
    rw [h₅]
    exact h₄

  have h₄ : Tendsto (fun (n : ℕ) => a n n) atTop (𝓝 (Real.exp d - 1)) := by
    have h₅ : Tendsto (fun (n : ℕ) => a n n + 1) atTop (𝓝 (Real.exp d)) := by
      have h₅₁ : (fun (n : ℕ) => a n n + 1) = (fun (n : ℕ) => (d / (2 : ℝ) ^ n + 1 : ℝ) ^ (2 : ℕ) ^ n) := by
        funext n
        rw [h₂]
        <;> simp [add_assoc]
      rw [h₅₁]
      exact h₃
    have h₅₂ : Tendsto (fun (n : ℕ) => a n n) atTop (𝓝 (Real.exp d - 1)) := by
      have h₅₃ : Tendsto (fun (n : ℕ) => a n n + 1) atTop (𝓝 (Real.exp d)) := h₅
      have h₅₄ : Tendsto (fun (n : ℕ) => (a n n + 1 : ℝ) - 1) atTop (𝓝 (Real.exp d - 1)) := by
        have h₅₅ : Tendsto (fun (n : ℕ) => (a n n + 1 : ℝ) - 1) atTop (𝓝 (Real.exp d - 1)) := by
          convert h₅₃.sub tendsto_const_nhds using 1
          <;> simp [sub_eq_add_neg]
          <;> ring_nf
          <;> simp_all [add_assoc]
          <;> norm_num
          <;> linarith
        exact h₅₅
      have h₅₆ : (fun (n : ℕ) => (a n n + 1 : ℝ) - 1) = (fun (n : ℕ) => a n n) := by
        funext n
        ring_nf
        <;> simp [add_assoc]
        <;> norm_num
        <;> linarith
      rw [h₅₆] at h₅₄
      exact h₅₄
    exact h₅₂

  simpa using h₄
