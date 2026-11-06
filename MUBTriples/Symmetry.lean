import MUBTriples.NormalForm

/-!
# The order-three symmetry of a triple

Paper (main text, Eq. `triple-symmetry`; SM §"Basis exclusions and symmetry"):
"a unitary `T` with `T³ = I₆` that fixes each vector of one basis up to a phase
and permutes the vectors of each of the other two in two cycles of three".

* "fixes each vector of the anchor basis `U m` up to a phase":
  `T * U m = U m * diagonal d`;
* "permutes the vectors of basis `U k` in two cycles of three" (with phases):
  `T * U k = U k * monomial σ c` where `σ` is conjugate to the standard
  double three-cycle `cyc : (b, s) ↦ (b, s + 1)` of `Fin 3 ⊕ Fin 3`.

The eigenvalue statement of the paper (`1, ω, ω²` each twice) is a consequence
and is not part of the definition.

We prove that the property is invariant under triple equivalence and under
entrywise complex conjugation, and that every triple in the symmetric normal
form `{I₆, symH x/√6, symK y u v/√6}` has it, with
`T = diag(1, ω, ω², 1, ω, ω²)`.
-/

open Matrix Hadamard6

namespace MUBTriples

/-- The standard double three-cycle `(b, s) ↦ (b, s + 1)`. -/
def cyc : Equiv.Perm I6 := Equiv.sumCongr (finRotate 3) (finRotate 3)

/-- `σ` consists of two disjoint three-cycles (it is conjugate to `cyc`). -/
def IsDoubleThreeCycle (σ : Equiv.Perm I6) : Prop :=
  ∃ e : Equiv.Perm I6, ∀ x, σ (e x) = e (cyc x)

/-- `T` is an order-three symmetry of the triple `U` with anchor basis `U m`. -/
def IsOrder3Symmetry (T : Mat6) (U : Triple) (m : Fin 3) : Prop :=
  IsUnitary T ∧ T ^ 3 = 1 ∧
    (∃ d : I6 → ℂ, T * U m = U m * diagonal d) ∧
    ∀ k, k ≠ m → ∃ (σ : Equiv.Perm I6) (c : I6 → ℂ),
      IsDoubleThreeCycle σ ∧ T * U k = U k * monomial σ c

/-- The triple has an order-three symmetry of the type used in the paper. -/
def HasOrder3Symmetry (U : Triple) : Prop := ∃ T m, IsOrder3Symmetry T U m

/-! ### Monomial algebra -/

lemma diagonal_mul_monomial (d : I6 → ℂ) (τ : Equiv.Perm I6) (e : I6 → ℂ) :
    diagonal d * monomial τ e = monomial τ (fun j => d (τ j) * e j) := by
  ext i j
  rw [diagonal_mul]
  by_cases h : i = τ j
  · rw [monomial_apply, monomial_apply, if_pos h, if_pos h, h]
  · rw [monomial_apply, monomial_apply, if_neg h, if_neg h, mul_zero]

lemma monomial_one_eq_diagonal (c : I6 → ℂ) : monomial 1 c = diagonal c := by
  ext i j
  by_cases h : i = j
  · subst h; simp
  · rw [monomial_apply, if_neg (by simpa using h), diagonal_apply_ne _ h]

lemma conjM_monomial (σ : Equiv.Perm I6) (c : I6 → ℂ) :
    conjM (monomial σ c) = monomial σ (fun j => star (c j)) := by
  ext i j
  simp only [conjM, Matrix.map_apply, monomial_apply]
  split_ifs <;> simp

lemma conjM_diagonal (d : I6 → ℂ) : conjM (diagonal d) = diagonal (fun j => star (d j)) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [conjM]
  · simp [conjM, diagonal_apply_ne _ h]

lemma conjM_pow (A : Mat6) (n : ℕ) : conjM (A ^ n) = conjM A ^ n := by
  induction n with
  | zero => simp [conjM_one]
  | succ n ih => rw [pow_succ, conjM_mul, ih, pow_succ]

lemma IsDoubleThreeCycle.conj {σ : Equiv.Perm I6} (h : IsDoubleThreeCycle σ)
    (τ : Equiv.Perm I6) : IsDoubleThreeCycle (τ⁻¹ * σ * τ) := by
  obtain ⟨e, he⟩ := h
  refine ⟨τ⁻¹ * e, fun x => ?_⟩
  simp only [Equiv.Perm.mul_apply]
  rw [show τ (τ⁻¹ (e x)) = e x by simp, he]

lemma isDoubleThreeCycle_cyc : IsDoubleThreeCycle cyc := ⟨1, fun _ => rfl⟩

/-- Conjugating a monomial by a monomial. -/
lemma monomial_conj_monomial (σ τ : Equiv.Perm I6) (c e : I6 → ℂ) :
    ∃ c', (monomial τ e)ᴴ * monomial σ c * monomial τ e = monomial (τ⁻¹ * σ * τ) c' := by
  rw [monomial_conjTranspose, monomial_mul_monomial, monomial_mul_monomial]
  exact ⟨_, rfl⟩

lemma conj_diagonal_monomial (d : I6 → ℂ) (τ : Equiv.Perm I6) (e : I6 → ℂ) :
    ∃ d', (monomial τ e)ᴴ * diagonal d * monomial τ e = diagonal d' := by
  rw [Matrix.mul_assoc, diagonal_mul_monomial, monomial_conjTranspose, monomial_mul_monomial,
    inv_mul_cancel, monomial_one_eq_diagonal]
  exact ⟨_, rfl⟩

lemma pow_three_conj {W T : Mat6} (hW : Wᴴ * W = 1) : (W * T * Wᴴ) ^ 3 = W * T ^ 3 * Wᴴ := by
  have e : ∀ A B : Mat6, (W * A * Wᴴ) * (W * B * Wᴴ) = W * (A * B) * Wᴴ := by
    intro A B
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Wᴴ W, hW, Matrix.one_mul]
  rw [pow_succ, pow_two, e, e, pow_succ, pow_two]

/-! ### Invariance -/

theorem hasOrder3Symmetry_of_tripleEquiv {U V : Triple} (h : TripleEquiv U V)
    (hU : HasOrder3Symmetry U) : HasOrder3Symmetry V := by
  obtain ⟨W, π, M, hW, hM, hV⟩ := h
  obtain ⟨T, m, hTu, hT3, ⟨d, hd⟩, hk⟩ := hU
  have hVk : ∀ k, W * T * Wᴴ * V k = W * (T * U (π k)) * M k := by
    intro k
    rw [hV k]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Wᴴ W, hW.2, Matrix.one_mul]
  have hback : ∀ k (X : Mat6), W * (U (π k) * X) * M k = V k * ((M k)ᴴ * X * M k) := by
    intro k X
    rw [hV k]
    have hMu := (hM k).isUnitary
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (M k) (M k)ᴴ, hMu.1, Matrix.one_mul]
  refine ⟨W * T * Wᴴ, π⁻¹ m, ⟨(hW.mul hTu).mul hW.conjTranspose, ?_, ?_, ?_⟩⟩
  · rw [pow_three_conj hW.2, hT3, Matrix.mul_one, hW.1]
  · obtain ⟨σ, c, -, hMeq⟩ := hM (π⁻¹ m)
    obtain ⟨d', hd'⟩ := conj_diagonal_monomial d σ c
    refine ⟨d', ?_⟩
    rw [hVk, show π (π⁻¹ m) = m by simp, hd]
    have := hback (π⁻¹ m) (diagonal d)
    rw [show π (π⁻¹ m) = m by simp] at this
    rw [this, hMeq, hd']
  · intro k hkm
    have hπk : π k ≠ m := by
      intro h; apply hkm; rw [← h]; simp
    obtain ⟨σ, c, hσ, hσeq⟩ := hk (π k) hπk
    obtain ⟨τ, e, -, hMeq⟩ := hM k
    obtain ⟨c', hc'⟩ := monomial_conj_monomial σ τ c e
    refine ⟨τ⁻¹ * σ * τ, c', hσ.conj τ, ?_⟩
    rw [hVk, hσeq, hback, hMeq, hc']

theorem hasOrder3Symmetry_conj {U : Triple} (hU : HasOrder3Symmetry U) :
    HasOrder3Symmetry (conjTriple U) := by
  obtain ⟨T, m, hTu, hT3, ⟨d, hd⟩, hk⟩ := hU
  refine ⟨conjM T, m, hTu.conjM, ?_, ⟨fun j => star (d j), ?_⟩, ?_⟩
  · rw [← conjM_pow, hT3, conjM_one]
  · simp only [conjTriple]; rw [← conjM_mul, hd, conjM_mul, conjM_diagonal]
  · intro k hkm
    obtain ⟨σ, c, hσ, hσeq⟩ := hk k hkm
    refine ⟨σ, fun j => star (c j), hσ, ?_⟩
    simp only [conjTriple]; rw [← conjM_mul, hσeq, conjM_mul, conjM_monomial]

theorem hasOrder3Symmetry_iff_of_tripleEquiv {U V : Triple} (h : TripleEquiv U V) :
    HasOrder3Symmetry U ↔ HasOrder3Symmetry V :=
  ⟨hasOrder3Symmetry_of_tripleEquiv h, hasOrder3Symmetry_of_tripleEquiv (tripleEquiv_symm h)⟩

end MUBTriples
