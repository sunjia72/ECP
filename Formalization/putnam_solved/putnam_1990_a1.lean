import Mathlib
import Aesop
open BigOperators Classical ENNReal Equiv EuclideanGeometry Filter Finset Fintype Function Lex List MeasureTheory Nat ProbabilityTheory Real SimpleGraph Real Nat Topology Rat
set_option maxHeartbeats 0
theorem putnam_1990_a1 : ∃ (putnam_1990_a1_solution : (ℕ → ℤ) × (ℕ → ℤ)), ∀ (T : ℕ → ℤ), ((T (0 : ℕ) = (2 : ℤ) ∧ T (1 : ℕ) = (3 : ℤ) ∧ T (2 : ℕ) = (6 : ℤ)) ∧ (∀ (n : ℕ), T (n + (3 : ℕ)) = ((↑n : ℤ) + (7 : ℤ)) * T (n + (2 : ℕ)) - (4 : ℤ) * ((↑n : ℤ) + (3 : ℤ)) * T (n + (1 : ℕ)) + ((4 : ℤ) * (↑n : ℤ) + (4 : ℤ)) * T n)) → (T = putnam_1990_a1_solution.1 + putnam_1990_a1_solution.2) := by
  use ((fun n : ℕ => (Nat.factorial n : ℤ), fun n : ℕ => (2 : ℤ) ^ n) : (ℕ → ℤ) × (ℕ → ℤ))
  intro T hT
  have h_main : ∀ n : ℕ, T n = (Nat.factorial n : ℤ) + (2 : ℤ) ^ n := by
    have h₁ : T 0 = (2 : ℤ) := hT.1.1
    have h₂ : T 1 = (3 : ℤ) := hT.1.2.1
    have h₃ : T 2 = (6 : ℤ) := hT.1.2.2
    have h₄ : ∀ (n : ℕ), T (n + 3) = ((n : ℤ) + 7) * T (n + 2) - 4 * ((n : ℤ) + 3) * T (n + 1) + (4 * (n : ℤ) + 4) * T n := by
      intro n
      have h₅ := hT.2 n
      simpa [add_assoc] using h₅
    have h₅ : ∀ n : ℕ, T n = (Nat.factorial n : ℤ) + (2 : ℤ) ^ n := by
      intro n
      have h₆ : T n = (Nat.factorial n : ℤ) + (2 : ℤ) ^ n := by
        induction n using Nat.strong_induction_on with
        | h n ih =>
          match n with
          | 0 =>
            norm_num [Nat.factorial] at h₁ ⊢
            <;> simp_all [h₁]
            <;> norm_num
          | 1 =>
            norm_num [Nat.factorial] at h₂ ⊢
            <;> simp_all [h₂]
            <;> norm_num
          | 2 =>
            norm_num [Nat.factorial] at h₃ ⊢
            <;> simp_all [h₃]
            <;> norm_num
          | k + 3 =>
            have h₇ := h₄ k
            have h₈ := ih k (by omega)
            have h₉ := ih (k + 1) (by omega)
            have h₁₀ := ih (k + 2) (by omega)
            simp [Nat.factorial, pow_add, pow_one, mul_add, mul_comm, mul_left_comm, mul_assoc] at h₇ h₈ h₉ h₁₀ ⊢
            <;>
            (try ring_nf at h₇ h₈ h₉ h₁₀ ⊢) <;>
            (try norm_cast at h₇ h₈ h₉ h₁₀ ⊢) <;>
            (try simp_all [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat]) <;>
            (try ring_nf at h₇ h₈ h₉ h₁₀ ⊢) <;>
            (try norm_num at h₇ h₈ h₉ h₁₀ ⊢) <;>
            (try linarith) <;>
            (try nlinarith) <;>
            (try
              {
                simp_all [Nat.factorial, pow_add, pow_one, mul_add, mul_comm, mul_left_comm, mul_assoc]
                <;> ring_nf at *
                <;> norm_cast at *
                <;> nlinarith
              })
            <;>
            (try
              {
                simp_all [Nat.factorial, pow_add, pow_one, mul_add, mul_comm, mul_left_comm, mul_assoc]
                <;> ring_nf at *
                <;> norm_cast at *
                <;> linarith
              })
      exact h₆
    exact h₅

  have h_final : T = ((fun n : ℕ => (Nat.factorial n : ℤ), fun n : ℕ => (2 : ℤ) ^ n) : (ℕ → ℤ) × (ℕ → ℤ)).1 + ((fun n : ℕ => (Nat.factorial n : ℤ), fun n : ℕ => (2 : ℤ) ^ n) : (ℕ → ℤ) × (ℕ → ℤ)).2 := by
    funext n
    have h₁ : T n = (Nat.factorial n : ℤ) + (2 : ℤ) ^ n := h_main n
    simp [h₁, Pi.add_apply]
    <;> norm_cast
    <;> simp [Nat.factorial]
    <;> ring_nf
    <;> norm_num
    <;> simp_all [Nat.factorial]
    <;> ring_nf at *
    <;> norm_cast at *
    <;> linarith

  exact h_final
