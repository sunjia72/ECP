import Mathlib
import Aesop
open BigOperators Classical ENNReal Equiv EuclideanGeometry Filter Finset Fintype Function Lex List MeasureTheory Nat ProbabilityTheory Real SimpleGraph Real Nat Topology Rat
set_option maxHeartbeats 0
theorem P2026HMMT_4 : ∃ (P2026HMMT_4_answer : ℂ), ∀ (a b c : ℂ), ((a ≠ b ∧ a ≠ c ∧ b ≠ c) ∧ (a ^ (2 : ℕ) + a * b + b ^ (2 : ℕ) = (3 : ℂ) * (a + b)) ∧ (a ^ (2 : ℕ) + a * c + c ^ (2 : ℕ) = (3 : ℂ) * (a + c)) ∧ (b ^ (2 : ℕ) + b * c + c ^ (2 : ℕ) = (5 : ℂ) * (b + c) + (1 : ℂ))) → (a = P2026HMMT_4_answer) := by
  use (((7 : ℂ) / 2) : ℂ)
  intro a b c h
  have h₁ : a + b + c = 3 := by
    have h₂ : a ≠ b := h.1.1
    have h₃ : a ≠ c := h.1.2.1
    have h₄ : b ≠ c := h.1.2.2
    have h₅ : a ^ 2 + a * b + b ^ 2 = 3 * (a + b) := h.2.1
    have h₆ : a ^ 2 + a * c + c ^ 2 = 3 * (a + c) := h.2.2.1
    have h₇ : (a ^ 2 + a * b + b ^ 2) - (a ^ 2 + a * c + c ^ 2) = 3 * (a + b) - 3 * (a + c) := by
      rw [h₅, h₆]
    have h₈ : (a ^ 2 + a * b + b ^ 2) - (a ^ 2 + a * c + c ^ 2) = a * b + b ^ 2 - a * c - c ^ 2 := by
      ring_nf
      <;> simp [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two]
      <;> norm_num
      <;>
      (try
        {
          simp_all [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two]
          <;> norm_num
          <;>
          (try ring_nf at *)
          <;>
          (try simp_all [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two])
          <;>
          (try norm_num)
          <;>
          (try linarith)
        })
      <;>
      (try ring_nf)
      <;>
      (try simp_all [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two])
      <;>
      (try norm_num)
      <;>
      (try linarith)
    have h₉ : 3 * (a + b) - 3 * (a + c) = 3 * (b - c) := by
      ring_nf
      <;> simp [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two]
      <;> norm_num
      <;>
      (try
        {
          simp_all [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two]
          <;> norm_num
          <;>
          (try ring_nf at *)
          <;>
          (try simp_all [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two])
          <;>
          (try norm_num)
          <;>
          (try linarith)
        })
      <;>
      (try ring_nf)
      <;>
      (try simp_all [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two])
      <;>
      (try norm_num)
      <;>
      (try linarith)
    have h₁₀ : a * b + b ^ 2 - a * c - c ^ 2 = 3 * (b - c) := by
      rw [h₈] at h₇
      rw [h₉] at h₇
      exact h₇
    have h₁₁ : a * (b - c) + (b - c) * (b + c) = 3 * (b - c) := by
      have h₁₂ : a * b + b ^ 2 - a * c - c ^ 2 = a * (b - c) + (b - c) * (b + c) := by
        ring_nf
        <;> simp [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two]
        <;> norm_num
        <;>
        (try
          {
            simp_all [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two]
            <;> norm_num
            <;>
            (try ring_nf at *)
            <;>
            (try simp_all [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two])
            <;>
            (try norm_num)
            <;>
            (try linarith)
          })
        <;>
        (try ring_nf)
        <;>
        (try simp_all [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two])
        <;>
        (try norm_num)
        <;>
        (try linarith)
      rw [h₁₂] at h₁₀
      exact h₁₀
    have h₁₂ : a * (b - c) + (b - c) * (b + c) - 3 * (b - c) = 0 := by
      rw [h₁₁]
      ring_nf
      <;> simp [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two]
      <;> norm_num
      <;>
      (try
        {
          simp_all [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two]
          <;> norm_num
          <;>
          (try ring_nf at *)
          <;>
          (try simp_all [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two])
          <;>
          (try norm_num)
          <;>
          (try linarith)
        })
      <;>
      (try ring_nf)
      <;>
      (try simp_all [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two])
      <;>
      (try norm_num)
      <;>
      (try linarith)
    have h₁₃ : (b - c) * (a + b + c - 3) = 0 := by
      calc
        (b - c) * (a + b + c - 3) = (b - c) * (a + (b + c) - 3) := by ring_nf
        _ = a * (b - c) + (b - c) * (b + c) - 3 * (b - c) := by
          ring_nf
          <;> simp [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two]
          <;> norm_num
          <;>
          (try
            {
              simp_all [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two]
              <;> norm_num
              <;>
              (try ring_nf at *)
              <;>
              (try simp_all [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two])
              <;>
              (try norm_num)
              <;>
              (try linarith)
            })
          <;>
          (try ring_nf)
          <;>
          (try simp_all [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two])
          <;>
          (try norm_num)
          <;>
          (try linarith)
        _ = 0 := by rw [h₁₂]
    have h₁₄ : b - c ≠ 0 := by
      intro h₁₅
      apply h₄
      rw [sub_eq_zero] at h₁₅
      exact h₁₅
    have h₁₅ : a + b + c - 3 = 0 := by
      apply mul_left_cancel₀ h₁₄
      rw [h₁₃]
      <;> simp [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two]
      <;> norm_num
    have h₁₆ : a + b + c = 3 := by
      have h₁₇ : a + b + c - 3 = 0 := h₁₅
      have h₁₈ : a + b + c = 3 := by
        rw [sub_eq_zero] at h₁₇
        exact h₁₇
      exact h₁₈
    exact h₁₆

  have h₂ : a ^ 2 + b ^ 2 + a * b - a - 3 * b - 7 = 0 := by
    have h₃ : a ^ 2 + a * b + b ^ 2 = 3 * (a + b) := h.2.1
    have h₄ : b ^ 2 + b * c + c ^ 2 = 5 * (b + c) + 1 := h.2.2.2
    have h₅ : a + b + c = 3 := h₁
    have h₆ : c = 3 - a - b := by
      have h₇ : a + b + c = 3 := h₁
      have h₈ : c = 3 - a - b := by
        rw [add_assoc] at h₇
        linear_combination h₇
      exact h₈
    have h₇ : b ^ 2 + b * c + c ^ 2 = 5 * (b + c) + 1 := h.2.2.2
    rw [h₆] at h₇
    have h₈ : b ^ 2 + b * (3 - a - b) + (3 - a - b) ^ 2 = 5 * (b + (3 - a - b)) + 1 := by
      simpa [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two] using h₇
    have h₉ : a ^ 2 + b ^ 2 + a * b - a - 3 * b - 7 = 0 := by
      have h₁₀ := h₈
      simp [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two] at h₁₀ ⊢
      norm_num at h₁₀ ⊢
      constructor <;>
      (try ring_nf at h₁₀ ⊢) <;>
      (try simp_all [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two]) <;>
      (try norm_num at * ) <;>
      (try nlinarith) <;>
      (try
        {
          nlinarith [sq_nonneg (a.re - 7 / 2), sq_nonneg (a.im), sq_nonneg (b.re - 7 / 2),
            sq_nonneg (b.im), sq_nonneg (a.re - b.re), sq_nonneg (a.im - b.im)]
        })
      <;>
      (try
        {
          nlinarith [sq_nonneg (a.re - 7 / 2), sq_nonneg (a.im), sq_nonneg (b.re - 7 / 2),
            sq_nonneg (b.im), sq_nonneg (a.re - b.re), sq_nonneg (a.im - b.im)]
        })
    exact h₉

  have h₃ : a = (7 : ℂ) / 2 := by
    have h₄ : a ^ 2 + a * b + b ^ 2 = 3 * (a + b) := h.2.1
    have h₅ : a ^ 2 + b ^ 2 + a * b - a - 3 * b - 7 = 0 := h₂
    have h₆ : a ^ 2 + a * b + b ^ 2 = 3 * a + 3 * b := by
      calc
        a ^ 2 + a * b + b ^ 2 = 3 * (a + b) := by rw [h₄]
        _ = 3 * a + 3 * b := by ring
    have h₇ : a ^ 2 + b ^ 2 + a * b - a - 3 * b - 7 = 0 := h₂
    have h₈ : (3 : ℂ) * a + 3 * b - a - 3 * b - 7 = 0 := by
      calc
        (3 : ℂ) * a + 3 * b - a - 3 * b - 7 = (a ^ 2 + a * b + b ^ 2) - a - 3 * b - 7 := by
          rw [h₆]
          <;> ring_nf
          <;> simp [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two]
          <;> norm_num
          <;>
          (try
            {
              simp_all [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two]
              <;> norm_num
              <;>
              (try ring_nf at *)
              <;>
              (try simp_all [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two])
              <;>
              (try norm_num)
              <;>
              (try linarith)
            })
          <;>
          (try ring_nf)
          <;>
          (try simp_all [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two])
          <;>
          (try norm_num)
          <;>
          (try linarith)
        _ = 0 := by
          calc
            (a ^ 2 + a * b + b ^ 2) - a - 3 * b - 7 = (a ^ 2 + b ^ 2 + a * b - a - 3 * b - 7) := by ring_nf
            _ = 0 := by
              rw [h₇]
              <;> simp [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two]
              <;> norm_num
    have h₉ : (2 : ℂ) * a - 7 = 0 := by
      calc
        (2 : ℂ) * a - 7 = (3 : ℂ) * a + 3 * b - a - 3 * b - 7 := by
          ring_nf
          <;> simp [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two]
          <;> norm_num
          <;>
          (try
            {
              simp_all [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two]
              <;> norm_num
              <;>
              (try ring_nf at *)
              <;>
              (try simp_all [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two])
              <;>
              (try norm_num)
              <;>
              (try linarith)
            })
          <;>
          (try ring_nf)
          <;>
          (try simp_all [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two])
          <;>
          (try norm_num)
          <;>
          (try linarith)
        _ = 0 := by
          rw [h₈]
          <;> simp [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two]
          <;> norm_num
    have h₁₀ : a = (7 : ℂ) / 2 := by
      have h₁₁ : (2 : ℂ) * a - 7 = 0 := h₉
      have h₁₂ : (2 : ℂ) * a = 7 := by
        rw [sub_eq_zero] at h₁₁
        exact h₁₁
      have h₁₃ : a = (7 : ℂ) / 2 := by
        calc
          a = (2 : ℂ) * a / 2 := by
            field_simp [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two]
            <;> ring_nf
            <;> simp [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two]
            <;> norm_num
            <;>
            (try
              {
                simp_all [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two]
                <;> norm_num
                <;>
                (try ring_nf at *)
                <;>
                (try simp_all [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two])
                <;>
                (try norm_num)
                <;>
                (try linarith)
              })
            <;>
            (try ring_nf)
            <;>
            (try simp_all [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two])
            <;>
            (try norm_num)
            <;>
            (try linarith)
          _ = 7 / 2 := by
            rw [h₁₂]
            <;> field_simp [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two]
            <;> ring_nf
            <;> simp [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two]
            <;> norm_num
            <;>
            (try
              {
                simp_all [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two]
                <;> norm_num
                <;>
                (try ring_nf at *)
                <;>
                (try simp_all [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two])
                <;>
                (try norm_num)
                <;>
                (try linarith)
              })
            <;>
            (try ring_nf)
            <;>
            (try simp_all [Complex.ext_iff, pow_two, Complex.ext_iff, pow_two])
            <;>
            (try norm_num)
            <;>
            (try linarith)
      exact h₁₃
    exact h₁₀

  exact h₃
