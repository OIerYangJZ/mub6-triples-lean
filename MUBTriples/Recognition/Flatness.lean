import MUBTriples.KnownTriples

/-!
# Flatness of a `3 × 3` circulant and the amplitude bounds

For `d : Fin 3 → ℂ` put `S d = Σ |dₜ|²` and `Γ d = Σₜ d̄ₜ dₜ₊₁` (the cyclic
autocorrelation).  Then the circulant `F₃ᴴ diag(d) F₃` is flat (all entries of modulus
`√6`) iff `S d = 6` and `Γ d = 0` (`flat_iff`).

Amplitude bounds (SM Eq. `tc-amplitude-bounds`, consequence "no `αₜ, βₜ` vanishes"):
for unit `u, v`, `|uₜ ± vₜ|² ≤ 4`; if `u + v` is flat then no `uₜ + vₜ` vanishes
(`flat_ne_zero`): a zero entry would force, through `Γ = 0`, a second zero entry and then
`|third|² = 6 > 4`.  This is a shorter route than the paper's discriminant bound
`q ≤ 6√3 - 9`, which is not needed for the nonvanishing.
-/

open Matrix Hadamard6

namespace MUBTriples

/-- `Σₜ |dₜ|²`. -/
noncomputable def sqSum (d : I3 → ℂ) : ℝ := ∑ t, Complex.normSq (d t)

/-- Cyclic autocorrelation `d̄₀ d₁ + d̄₁ d₂ + d̄₂ d₀`. -/
def autoc (d : I3 → ℂ) : ℂ := star (d 0) * d 1 + star (d 1) * d 2 + star (d 2) * d 0

lemma sqSum_eq (d : I3 → ℂ) :
    sqSum d = Complex.normSq (d 0) + Complex.normSq (d 1) + Complex.normSq (d 2) := by
  simp [sqSum, Fin.sum_univ_three]

/-- The three Fourier sums `D_k = d₀ + d₁ ω^k + d₂ ω^{2k}`. -/
noncomputable def fsum (d : I3 → ℂ) (k : ℕ) : ℂ := d 0 + d 1 * ω ^ k + d 2 * ω ^ (2 * k)

lemma normSq_eq_mul_star (z : ℂ) : (Complex.normSq z : ℂ) = z * star z := by
  rw [show star z = (starRingEnd ℂ) z from rfl, Complex.mul_conj]

lemma two_re (w : ℂ) : (2 : ℂ) * (w.re : ℂ) = w + star w := by
  rw [show star w = (starRingEnd ℂ) w from rfl, Complex.add_conj]; push_cast; ring

lemma fsum_normSq (d : I3 → ℂ) (k : ℕ) (hk : k < 3) :
    Complex.normSq (fsum d k) = sqSum d + 2 * (ω ^ k * autoc d).re := by
  apply Complex.ofReal_injective
  push_cast
  rw [two_re, normSq_eq_mul_star, sqSum_eq]
  push_cast
  simp only [normSq_eq_mul_star, fsum, autoc, star_add, star_mul', star_pow, star_ω, star_star]
  interval_cases k <;>
    ring_nf <;> simp only [ω_pow_reduce, Nat.reduceLeDiff, Nat.reduceSub] <;> ring_nf <;>
    simp only [ω_pow_reduce, Nat.reduceLeDiff, Nat.reduceSub] <;> ring_nf

lemma fsum_mod (d : I3 → ℂ) (n : ℕ) : fsum d n = fsum d (n % 3) := by
  unfold fsum
  rw [ω_pow_mod n, ω_pow_mod (2 * n), ω_pow_mod (2 * (n % 3))]
  congr 3
  simp [Nat.mul_mod, Nat.mod_mod]

lemma circ_eq_fsum (d : I3 → ℂ) (s s' : I3) : circ d s s' = fsum d (2 * s.val + s'.val) := by
  rw [circ_apply, Fin.sum_univ_three]
  simp only [fsum, Fin.val_zero, Fin.val_one, Fin.val_two, zero_mul, mul_zero, add_zero, pow_zero,
    mul_one, one_mul]
  congr 2
  ring_nf

lemma normSq_circ (d : I3 → ℂ) (s s' : I3) :
    Complex.normSq (circ d s s') =
      sqSum d + 2 * (ω ^ ((2 * s.val + s'.val) % 3) * autoc d).re := by
  rw [circ_eq_fsum, fsum_mod, fsum_normSq _ _ (Nat.mod_lt _ (by norm_num))]

lemma ω_sq_re : (ω ^ 2).re = -(1 / 2) := by
  rw [ω_sq]; simp; norm_num

lemma ω_sq_im : (ω ^ 2).im = -(Real.sqrt 3 / 2) := by
  rw [ω_sq]; simp

/-- **Flatness criterion.** -/
theorem flat_iff (d : I3 → ℂ) : Flat d ↔ sqSum d = 6 ∧ autoc d = 0 := by
  constructor
  · intro h
    have h0 := h 0 0
    have h1 := h 0 1
    have h2 := h 0 2
    rw [normSq_circ] at h0 h1 h2
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, mul_zero, zero_add, Nat.zero_mod,
      Nat.one_mod, Nat.reduceMod, pow_zero, one_mul, pow_one] at h0 h1 h2
    rw [Complex.mul_re, ω_re, ω_im] at h1
    rw [Complex.mul_re, ω_sq_re, ω_sq_im] at h2
    have hS : sqSum d = 6 := by linarith
    have hre : (autoc d).re = 0 := by linarith
    have him : (autoc d).im = 0 := by
      have hs3 : Real.sqrt 3 ≠ 0 := by positivity
      have : Real.sqrt 3 * (autoc d).im = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hs3
      · exact h
    exact ⟨hS, Complex.ext hre him⟩
  · rintro ⟨hS, hΓ⟩ s s'
    rw [normSq_circ, hS, hΓ]; simp

/-! ### Amplitude bounds -/

lemma normSq_add_le_four {a b : ℂ} (ha : Complex.normSq a = 1) (hb : Complex.normSq b = 1) :
    Complex.normSq (a + b) ≤ 4 := by
  have h1 := Complex.normSq_add a b
  have h2 := Complex.normSq_sub a b
  have h3 := Complex.normSq_nonneg (a - b)
  linarith

lemma normSq_sub_le_four {a b : ℂ} (ha : Complex.normSq a = 1) (hb : Complex.normSq b = 1) :
    Complex.normSq (a - b) ≤ 4 := by
  have h1 := Complex.normSq_add a b
  have h2 := Complex.normSq_sub a b
  have h3 := Complex.normSq_nonneg (a + b)
  linarith

lemma normSq_add_add_sub {a b : ℂ} (ha : Complex.normSq a = 1) (hb : Complex.normSq b = 1) :
    Complex.normSq (a + b) + Complex.normSq (a - b) = 4 := by
  have h1 := Complex.normSq_add a b
  have h2 := Complex.normSq_sub a b
  linarith

/-- A flat vector with entries of modulus at most `2` has no zero entry. -/
theorem flat_ne_zero {d : I3 → ℂ} (hd : Flat d) (hle : ∀ t, Complex.normSq (d t) ≤ 4) (t : I3) :
    d t ≠ 0 := by
  obtain ⟨hS, hΓ⟩ := (flat_iff d).1 hd
  rw [sqSum_eq] at hS
  unfold autoc at hΓ
  have l0 := hle 0
  have l1 := hle 1
  have l2 := hle 2
  intro hz
  fin_cases t
  · simp only [Fin.zero_eta] at hz
    rw [hz] at hΓ hS
    simp only [star_zero, zero_mul, mul_zero, zero_add, add_zero, map_zero] at hΓ hS
    rcases mul_eq_zero.1 hΓ with h | h
    · rw [star_eq_zero] at h; rw [h] at hS; simp at hS; linarith
    · rw [h] at hS; simp at hS; linarith
  · simp only [Fin.mk_one] at hz
    rw [hz] at hΓ hS
    simp only [star_zero, zero_mul, mul_zero, zero_add, add_zero, map_zero] at hΓ hS
    rcases mul_eq_zero.1 hΓ with h | h
    · rw [star_eq_zero] at h; rw [h] at hS; simp at hS; linarith
    · rw [h] at hS; simp at hS; linarith
  · simp only [Fin.reduceFinMk] at hz
    rw [hz] at hΓ hS
    simp only [star_zero, zero_mul, mul_zero, zero_add, add_zero, map_zero] at hΓ hS
    rcases mul_eq_zero.1 hΓ with h | h
    · rw [star_eq_zero] at h; rw [h] at hS; simp at hS; linarith
    · rw [h] at hS; simp at hS; linarith

end MUBTriples
