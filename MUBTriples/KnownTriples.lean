import MUBTriples.Statement

/-!
# Sanity lemmas for the known triples

* `isolatedTriple_isMUBTriple`: the isolated Fourier triple is a MUB triple.
* `familyTriple_isMUBTriple_iff`: for unit diagonals `D, R, S`, the explicit block
  form of the continuous family is a MUB triple iff the two circulants
  `F₃ᴴ (R + S) F₃` and `F₃ᴴ D (R̄ - S̄) F₃` are flat (all entries of modulus `√6`).
* `hasOrder3Symmetry_sym`: every triple in the symmetric normal form has the
  order-three symmetry `T = diag(1, ω, ω², 1, ω, ω²)`; in particular the isolated
  triple and every family member do.
-/

open Matrix Hadamard6

namespace MUBTriples

lemma circ_apply (d : I3 → ℂ) (s s' : I3) :
    circ d s s' = ∑ t, d t * ω ^ (2 * (t.val * s.val) + t.val * s'.val) := by
  rw [circ, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, conjTranspose_apply, F3_apply, star_ω_pow, pow_add]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  ring

lemma circ_smul (c : ℂ) (d : I3 → ℂ) : circ (c • d) = c • circ d := by
  simp only [circ, diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]

lemma circ_neg (d : I3 → ℂ) : circ (-d) = -circ d := by
  have : -d = (-1 : ℂ) • d := by funext t; simp
  rw [this, circ_smul]; simp

lemma circ_star (d : I3 → ℂ) (s s' : I3) : circ (star d) s s' = star (circ d s' s) := by
  have : (circ d)ᴴ = circ (star d) := by
    simp only [circ, conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose,
      Matrix.mul_assoc]
  rw [← this, conjTranspose_apply]

lemma flat_neg_iff (d : I3 → ℂ) : Flat (-d) ↔ Flat d := by
  simp only [Flat, circ_neg, Matrix.neg_apply, Complex.normSq_neg]

lemma flat_star_iff (d : I3 → ℂ) : Flat (star d) ↔ Flat d := by
  simp only [Flat, circ_star, normSq_star]
  exact ⟨fun h s s' => h s' s, fun h s s' => h s' s⟩

lemma flat_smul_of_normSq {c : ℂ} {d : I3 → ℂ} (hc : Complex.normSq c = 2)
    (hd : ∀ s s', Complex.normSq (circ d s s') = 3) : Flat (c • d) := by
  intro s s'
  rw [circ_smul, Matrix.smul_apply, smul_eq_mul, Complex.normSq_mul, hc, hd]; norm_num

/-! ### The isolated triple -/

/-- The diagonal of `diag(1, ω², ω²)`. -/
noncomputable def isoVec : I3 → ℂ := ![1, ω ^ 2, ω ^ 2]

lemma unitVec_isoVec : UnitVec isoVec := by
  intro t; fin_cases t <;> simp [isoVec, normSq_ω_pow]

lemma circ_isoVec (s s' : I3) : Complex.normSq (circ isoVec s s') = 3 := by
  rw [circ_apply]
  fin_cases s <;> fin_cases s' <;> simp [isoVec, Fin.sum_univ_three, ← pow_add, ω_pow_reduce] <;>
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, pow_two] <;> ring_nf <;>
  simp [sqrt3_pow_three, sqrt3_pow_four, sqrt3_pow_five, sqrt3_pow_six] <;> ring_nf

lemma isoK_eq : isoK = symK 1 isoVec (Complex.I • isoVec) := by
  unfold isoK symK isoG
  rw [mul_one, mul_one, diagonal_smul, Matrix.smul_mul]
  rfl

theorem isolatedTriple_isMUBTriple : IsMUBTriple isolatedTriple := by
  have hI : UnitVec (Complex.I • isoVec) := by
    intro t; simp [Complex.normSq_mul, unitVec_isoVec t]
  rw [isolatedTriple, isoK_eq, isMUBTriple_sym_iff unitVec_one unitVec_one unitVec_isoVec hI]
  have e1 : isoVec + Complex.I • isoVec = (1 + Complex.I) • isoVec := by
    rw [add_smul, one_smul]
  have e2 : isoVec - Complex.I • isoVec = (1 - Complex.I) • isoVec := by
    rw [sub_smul, one_smul]
  have n1 : Complex.normSq (1 + Complex.I) = 2 := by
    rw [Complex.normSq_apply]; simp; norm_num
  have n2 : Complex.normSq (1 - Complex.I) = 2 := by
    rw [Complex.normSq_apply]; simp; norm_num
  simp only [star_one, one_mul, mul_one, e1, e2]
  exact ⟨flat_smul_of_normSq n1 circ_isoVec, flat_smul_of_normSq n2 circ_isoVec,
    flat_smul_of_normSq n2 circ_isoVec, flat_smul_of_normSq n1 circ_isoVec⟩

/-! ### The continuous family -/

lemma diagonal_neg' (f : I3 → ℂ) : diagonal (-f) = -diagonal f := by
  rw [diagonal_neg]; rfl

lemma famK_eq_symK {d r s : I3 → ℂ} (hr : UnitVec r) (hs : UnitVec s) :
    famK d r s = symK (-(d * star r * star s)) r s := by
  unfold famK symK
  have e1 : r * -(d * star r * star s) = -(d * star s) := by
    funext t
    simp only [Pi.mul_apply, Pi.neg_apply, Pi.star_apply]
    have := mul_star_self_of_normSq (hr t)
    linear_combination (-(d t * star (s t))) * this
  have e2 : -(diagonal (s * -(d * star r * star s)) * F3) = diagonal (d * star r) * F3 := by
    have : s * -(d * star r * star s) = -(d * star r) := by
      funext t
      simp only [Pi.mul_apply, Pi.neg_apply, Pi.star_apply]
      have := mul_star_self_of_normSq (hs t)
      linear_combination (-(d t * star (r t))) * this
    rw [this, diagonal_neg', neg_mul, neg_neg]
  rw [e1, e2, diagonal_neg', neg_mul]

/-- **Family criterion.**  For unit diagonals, the explicit continuous-family triple is a
MUB triple iff `F₃ᴴ (R+S) F₃` and `F₃ᴴ D (R̄ - S̄) F₃` are flat. -/
theorem familyTriple_isMUBTriple_iff {d r s : I3 → ℂ} (hd : UnitVec d) (hr : UnitVec r)
    (hs : UnitVec s) :
    IsMUBTriple (familyTriple d r s) ↔ Flat (r + s) ∧ Flat (d * (star r - star s)) := by
  have hy : UnitVec (-(d * star r * star s)) := by
    intro t; simp [Complex.normSq_mul, hd t, hr t, hs t]
  rw [familyTriple, famK_eq_symK hr hs, isMUBTriple_sym_iff hd hy hr hs]
  have e2 : (r - s) * -(d * star r * star s) = d * (star r - star s) := by
    funext t
    simp only [Pi.mul_apply, Pi.neg_apply, Pi.star_apply, Pi.sub_apply]
    have h1 := mul_star_self_of_normSq (hr t)
    have h2 := mul_star_self_of_normSq (hs t)
    linear_combination (-(d t * star (s t))) * h1 + (d t * star (r t)) * h2
  have e3 : star d * (r - s) = star (d * (star r - star s)) := by
    funext t; simp [mul_sub]
  have e4 : star d * (r + s) * -(d * star r * star s) = -star (r + s) := by
    funext t
    simp only [Pi.mul_apply, Pi.neg_apply, Pi.star_apply, Pi.add_apply, star_add]
    have h0 := star_mul_self_of_normSq (hd t)
    have h1 := mul_star_self_of_normSq (hr t)
    have h2 := mul_star_self_of_normSq (hs t)
    linear_combination (-(r t * star (r t) * star (s t)) - s t * star (r t) * star (s t)) * h0
      - star (s t) * h1 - star (r t) * h2
  rw [e2, e3, e4, flat_neg_iff, flat_star_iff, flat_star_iff]
  constructor
  · rintro ⟨h1, h2, -, -⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2, h2, h1⟩

/-! ### The symmetry of the normal form -/

/-- `t`-coordinate of a row index `(a, t)`. -/
def tIdx : I6 → I3
  | Sum.inl t => t
  | Sum.inr t => t

/-- `T = diag(1, ω, ω², 1, ω, ω²)`. -/
noncomputable def Tsym : Mat6 := diagonal fun i => ω ^ (tIdx i).val

lemma ω_pow_mul_succ (t s : I3) : ω ^ (t.val * (s + 1).val) = ω ^ t.val * ω ^ (t.val * s.val) := by
  fin_cases t <;> fin_cases s <;> simp [ω_pow_reduce] <;> ring_nf <;> simp [ω_pow_reduce]

lemma Tsym_mul_symH (x : I3 → ℂ) : Tsym * symH x = symH x * monomial cyc 1 := by
  ext i j
  rw [mul_monomial_apply, Tsym, diagonal_mul]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [symH, cyc, diagonal_mul, ω_pow_mul_succ, tIdx] <;> ring

lemma Tsym_mul_symK (y u v : I3 → ℂ) : Tsym * symK y u v = symK y u v * monomial cyc 1 := by
  ext i j
  rw [mul_monomial_apply, Tsym, diagonal_mul]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [symK, cyc, diagonal_mul, ω_pow_mul_succ, tIdx] <;> ring

lemma Tsym_pow_three : Tsym ^ 3 = 1 := by
  rw [Tsym, diagonal_pow]
  have : (fun i : I6 => ω ^ (tIdx i).val) ^ 3 = fun _ => 1 := by
    funext i
    show (ω ^ (tIdx i).val) ^ 3 = 1
    rw [← pow_mul, mul_comm, pow_mul, ω_cube, one_pow]
  rw [this]; rfl

lemma Tsym_isUnitary : IsUnitary Tsym := by
  refine IsUnitary.of_mul_eq_one ?_
  rw [Tsym, diagonal_conjTranspose, diagonal_mul_diagonal]
  have : (fun i : I6 => (star fun i : I6 => ω ^ (tIdx i).val) i * ω ^ (tIdx i).val) =
      fun _ => 1 := by
    funext i; exact star_mul_self_of_normSq (normSq_ω_pow _)
  rw [this]; rfl

/-- Every triple in the symmetric normal form has the order-three symmetry
`T = diag(1, ω, ω², 1, ω, ω²)` with anchor `I₆`. -/
theorem hasOrder3Symmetry_sym (x y u v : I3 → ℂ) :
    HasOrder3Symmetry (std (symH x) (symK y u v)) := by
  refine ⟨Tsym, 0, Tsym_isUnitary, Tsym_pow_three, ⟨fun i => ω ^ (tIdx i).val, ?_⟩, ?_⟩
  · simp [Tsym]
  · intro k hk
    refine ⟨cyc, 1, isDoubleThreeCycle_cyc, ?_⟩
    fin_cases k
    · exact absurd rfl hk
    · change Tsym * (s6 • symH x) = (s6 • symH x) * monomial cyc 1
      rw [Matrix.mul_smul, Tsym_mul_symH, Matrix.smul_mul]
    · change Tsym * (s6 • symK y u v) = (s6 • symK y u v) * monomial cyc 1
      rw [Matrix.mul_smul, Tsym_mul_symK, Matrix.smul_mul]

theorem hasOrder3Symmetry_isolatedTriple : HasOrder3Symmetry isolatedTriple := by
  rw [isolatedTriple, isoK_eq]; exact hasOrder3Symmetry_sym _ _ _ _

theorem hasOrder3Symmetry_familyTriple {d r s : I3 → ℂ} (hr : UnitVec r) (hs : UnitVec s) :
    HasOrder3Symmetry (familyTriple d r s) := by
  rw [familyTriple, famK_eq_symK hr hs]; exact hasOrder3Symmetry_sym _ _ _ _

end MUBTriples
