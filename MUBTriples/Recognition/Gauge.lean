import MUBTriples.Recognition.Flatness

/-!
# Gauge moves of the symmetric normal form

Column permutations/phases inside each basis and common monomial row operations are
triple equivalences.  On the normal form `{I₆, symH x/√6, symK y u v/√6}`:

* `symH_mul_colOp`: rephasing (`λ`) and cyclically shifting (`j`) the second column orbit of
  `H` gives `x ↦ λ ω^{tj} x`;
* `symK_mul_colOp`: rephasing/shifting the two column orbits of `K` gives
  `u, v ↦ λ₀ ω^{t j₀} (u, v)` and `y ↦ λ₁ λ̄₀ ω^{t j₁} ω^{2 t j₀} y`.
-/

open Matrix Hadamard6

namespace MUBTriples

lemma tripleEquiv_std_colH {H K N : Mat6} (hN : IsMonomial N) :
    TripleEquiv (std H K) (std (H * N) K) := by
  refine ⟨1, 1, ![1, N, 1], isUnitary_one, fun k => ?_, fun k => ?_⟩
  · fin_cases k
    exacts [isMonomial_one, hN, isMonomial_one]
  · fin_cases k
    · show (1 : Mat6) = 1 * 1 * 1; simp
    · show s6 • (H * N) = 1 * (s6 • H) * N; rw [Matrix.one_mul, Matrix.smul_mul]
    · show s6 • K = 1 * (s6 • K) * 1; simp

lemma tripleEquiv_std_colK {H K N : Mat6} (hN : IsMonomial N) :
    TripleEquiv (std H K) (std H (K * N)) := by
  refine ⟨1, 1, ![1, 1, N], isUnitary_one, fun k => ?_, fun k => ?_⟩
  · fin_cases k
    exacts [isMonomial_one, isMonomial_one, hN]
  · fin_cases k
    · show (1 : Mat6) = 1 * 1 * 1; simp
    · show s6 • H = 1 * (s6 • H) * 1; simp
    · show s6 • (K * N) = 1 * (s6 • K) * N; rw [Matrix.one_mul, Matrix.smul_mul]

lemma tripleEquiv_std_row {H K R : Mat6} (hR : IsMonomial R) :
    TripleEquiv (std H K) (std (R * H) (R * K)) := by
  refine ⟨R, 1, ![Rᴴ, 1, 1], hR.isUnitary, fun k => ?_, fun k => ?_⟩
  · fin_cases k
    exacts [hR.conjTranspose, isMonomial_one, isMonomial_one]
  · fin_cases k
    · show (1 : Mat6) = R * 1 * Rᴴ; rw [Matrix.mul_one, hR.isUnitary.1]
    · show s6 • (R * H) = R * (s6 • H) * 1; rw [Matrix.mul_one, Matrix.mul_smul]
    · show s6 • (R * K) = R * (s6 • K) * 1; rw [Matrix.mul_one, Matrix.mul_smul]

lemma ω_pow_mul_add (t s j : I3) :
    ω ^ (t.val * (s + j).val) = ω ^ (t.val * s.val) * ω ^ (t.val * j.val) := by
  fin_cases t <;> fin_cases s <;> fin_cases j <;> simp [ω_pow_reduce, ← pow_add] <;>
    (ring_nf; try simp [ω_cube])

lemma ω_pow_three_mul (n : ℕ) : ω ^ (3 * n) = 1 := by rw [pow_mul, ω_cube, one_pow]

/-- The column operation on the second `H`-orbit: shift by `j` and phase `λ`. -/
noncomputable def colOpH (j : I3) (lam : ℂ) : Mat6 :=
  monomial (Equiv.sumCongr 1 (Equiv.addRight j)) (Sum.elim (fun _ => 1) (fun _ => lam))

lemma isMonomial_colOpH (j : I3) {lam : ℂ} (h : Complex.normSq lam = 1) :
    IsMonomial (colOpH j lam) :=
  ⟨_, _, fun i => by rcases i with i | i <;> simp [h], rfl⟩

lemma symH_mul_colOpH (x : I3 → ℂ) (j : I3) (lam : ℂ) :
    symH x * colOpH j lam = symH (fun t => lam * ω ^ (t.val * j.val) * x t) := by
  ext i k
  rw [colOpH, mul_monomial_apply]
  rcases i with i | i <;> rcases k with k | k <;>
    simp [symH, diagonal_mul, ω_pow_mul_add] <;> ring

/-- The column operation on `K`: shifts `j₀, j₁` and phases `λ₀, λ₁` on the two orbits. -/
noncomputable def colOpK (j₀ j₁ : I3) (l₀ l₁ : ℂ) : Mat6 :=
  monomial (Equiv.sumCongr (Equiv.addRight j₀) (Equiv.addRight j₁))
    (Sum.elim (fun _ => l₀) (fun _ => l₁))

lemma isMonomial_colOpK (j₀ j₁ : I3) {l₀ l₁ : ℂ} (h₀ : Complex.normSq l₀ = 1)
    (h₁ : Complex.normSq l₁ = 1) : IsMonomial (colOpK j₀ j₁ l₀ l₁) :=
  ⟨_, _, fun i => by rcases i with i | i <;> simp [h₀, h₁], rfl⟩

lemma symK_mul_colOpK (y u v : I3 → ℂ) (j₀ j₁ : I3) {l₀ : ℂ} (l₁ : ℂ)
    (h₀ : Complex.normSq l₀ = 1) :
    symK y u v * colOpK j₀ j₁ l₀ l₁ =
      symK (fun t => l₁ * star l₀ * ω ^ (t.val * j₁.val) * ω ^ (2 * (t.val * j₀.val)) * y t)
        (fun t => l₀ * ω ^ (t.val * j₀.val) * u t) (fun t => l₀ * ω ^ (t.val * j₀.val) * v t) := by
  have hl := mul_star_self_of_normSq h₀
  have h3 : ∀ t : I3, ω ^ (t.val * j₀.val) * ω ^ (2 * (t.val * j₀.val)) = 1 := by
    intro t; rw [← pow_add, show t.val * j₀.val + 2 * (t.val * j₀.val) = 3 * (t.val * j₀.val) by ring,
      ω_pow_three_mul]
  have key : ∀ (t : I3) (a : ℂ), (l₀ * ω ^ (t.val * j₀.val) * a) *
      (l₁ * star l₀ * ω ^ (t.val * j₁.val) * ω ^ (2 * (t.val * j₀.val)) * y t) =
      l₁ * ω ^ (t.val * j₁.val) * (a * y t) := by
    intro t a
    have h := h3 t
    linear_combination (l₁ * ω ^ (t.val * j₁.val) * a * y t) *
      (ω ^ (t.val * j₀.val) * ω ^ (2 * (t.val * j₀.val)) * hl + h)
  ext i k
  rw [colOpK, mul_monomial_apply]
  rcases i with i | i <;> rcases k with k | k
  · simp only [symK, fromBlocks_apply₁₁, diagonal_mul, F3_apply, Equiv.sumCongr_apply,
      Sum.map_inl, Equiv.coe_addRight, Sum.elim_inl, ω_pow_mul_add]; ring
  · simp only [symK, fromBlocks_apply₁₂, diagonal_mul, F3_apply, Equiv.sumCongr_apply,
      Sum.map_inr, Equiv.coe_addRight, Sum.elim_inr, ω_pow_mul_add, Pi.mul_apply]
    rw [key]; ring
  · simp only [symK, fromBlocks_apply₂₁, diagonal_mul, F3_apply, Equiv.sumCongr_apply,
      Sum.map_inl, Equiv.coe_addRight, Sum.elim_inl, ω_pow_mul_add]; ring
  · simp only [symK, fromBlocks_apply₂₂, diagonal_mul, F3_apply, Equiv.sumCongr_apply,
      Sum.map_inr, Equiv.coe_addRight, Sum.elim_inr, ω_pow_mul_add, Pi.mul_apply,
      Matrix.neg_apply]
    rw [key]; ring

end MUBTriples
