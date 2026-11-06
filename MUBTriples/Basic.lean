import Mathlib
import Hadamard6.TaoOrbit

/-!
# Mutually unbiased triples in `ℂ⁶`: basic definitions

We reuse the matrix model of the order-six Hadamard classification
(`Hadamard6.Mat6`, indexed by `Fin 3 ⊕ Fin 3`, and `Hadamard6.IsHadamard`).
The definitions `IsUnitary` and `Unbiased` are verbatim the ones of the
quartet formalization `NoFourMUBs.Basic` (https://github.com/JoeyT1994/NoFourMUBS,
MIT License, Copyright (c) 2026 Joseph Tindall and Mateo Cárdenes Wuttig; see `LICENSE`),
which is not a dependency of this project, so they are restated here.

An orthonormal basis of `ℂ⁶` is recorded as the columns of a unitary matrix.
A *triple* is a function `Fin 3 → Mat6`.

## Equivalence of triples

`TripleEquiv U V` means: there are a common unitary `W`, a permutation `π`
of the three bases and, for every basis, a monomial matrix `M k`
(a permutation of the columns together with unit column phases) with
`V k = W * U (π k) * M k`.  This is exactly the equivalence of the paper
(arXiv 2611.06917, main text §"Covering", and SM §"Patterns and the triple
equations"): "a common ambient unitary, independent column phases and
permutations, and permutation of the three bases".
**Complex conjugation is not part of this equivalence.**
-/

open Matrix Hadamard6

namespace MUBTriples

/-- The columns of `U` form an orthonormal basis. -/
def IsUnitary (U : Mat6) : Prop := U * Uᴴ = 1 ∧ Uᴴ * U = 1

/-- Two orthonormal bases (columns of `U`, `V`) are mutually unbiased. -/
def Unbiased (U V : Mat6) : Prop := ∀ i j, Complex.normSq ((Uᴴ * V) i j) = 1 / 6

/-- An ordered triple of bases. -/
abbrev Triple := Fin 3 → Mat6

/-- Three pairwise mutually unbiased orthonormal bases of `ℂ⁶`. -/
def IsMUBTriple (U : Triple) : Prop :=
  (∀ k, IsUnitary (U k)) ∧ ∀ k l, k ≠ l → Unbiased (U k) (U l)

/-- The monomial matrix with permutation `σ` and column phases `c`:
right multiplication `U * monomial σ c` has `j`-th column `c j • (column σ j of U)`. -/
def monomial (σ : Equiv.Perm I6) (c : I6 → ℂ) : Mat6 :=
  Matrix.of fun i j => if i = σ j then c j else 0

/-- A monomial matrix with unit phases: permutation and rephasing of columns. -/
def IsMonomial (M : Mat6) : Prop :=
  ∃ (σ : Equiv.Perm I6) (c : I6 → ℂ), (∀ j, Complex.normSq (c j) = 1) ∧ M = monomial σ c

/-- Equivalence of triples of bases: common unitary, independent column
permutations and phases in each basis, and permutation of the bases.
Conjugation is *not* included. -/
def TripleEquiv (U V : Triple) : Prop :=
  ∃ (W : Mat6) (π : Equiv.Perm (Fin 3)) (M : Fin 3 → Mat6),
    IsUnitary W ∧ (∀ k, IsMonomial (M k)) ∧ ∀ k, V k = W * U (π k) * M k

/-- Entrywise complex conjugation. -/
def conjM (A : Mat6) : Mat6 := A.map (starRingEnd ℂ)

/-- Entrywise conjugation of every basis of a triple. -/
def conjTriple (U : Triple) : Triple := fun k => conjM (U k)

/-- `1/√6` as a complex number. -/
noncomputable def s6 : ℂ := ((Real.sqrt 6 : ℝ) : ℂ)⁻¹

/-- The standard form `{I₆, H/√6, K/√6}` of a triple. -/
noncomputable def std (H K : Mat6) : Triple := ![1, s6 • H, s6 • K]

/-! ### Elementary lemmas -/

lemma star_mul_self_of_normSq {z : ℂ} (h : Complex.normSq z = 1) : star z * z = 1 := by
  have := Complex.normSq_eq_conj_mul_self (z := z)
  rw [h] at this; exact_mod_cast this.symm

lemma mul_star_self_of_normSq {z : ℂ} (h : Complex.normSq z = 1) : z * star z = 1 := by
  rw [mul_comm]; exact star_mul_self_of_normSq h

lemma normSq_star (z : ℂ) : Complex.normSq (star z) = Complex.normSq z := Complex.normSq_conj z

lemma unbiased_symm {U V : Mat6} (h : Unbiased U V) : Unbiased V U := by
  intro i j
  have e : (Vᴴ * U) i j = star ((Uᴴ * V) j i) := by
    rw [← conjTranspose_apply, conjTranspose_mul, conjTranspose_conjTranspose]
  rw [e, normSq_star]; exact h j i

lemma IsUnitary.of_mul_eq_one {U : Mat6} (h : Uᴴ * U = 1) : IsUnitary U :=
  ⟨mul_eq_one_comm.mp h, h⟩

lemma isUnitary_one : IsUnitary (1 : Mat6) := ⟨by simp, by simp⟩

lemma IsUnitary.mul {U V : Mat6} (hU : IsUnitary U) (hV : IsUnitary V) : IsUnitary (U * V) := by
  refine IsUnitary.of_mul_eq_one ?_
  rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU.2, Matrix.one_mul, hV.2]

lemma IsUnitary.conjTranspose {U : Mat6} (hU : IsUnitary U) : IsUnitary Uᴴ :=
  ⟨by rw [conjTranspose_conjTranspose]; exact hU.2, by rw [conjTranspose_conjTranspose]; exact hU.1⟩

/-! ### Monomial matrices -/

@[simp] lemma monomial_apply (σ : Equiv.Perm I6) (c : I6 → ℂ) (i j : I6) :
    monomial σ c i j = if i = σ j then c j else 0 := rfl

lemma mul_monomial_apply (U : Mat6) (σ : Equiv.Perm I6) (c : I6 → ℂ) (i j : I6) :
    (U * monomial σ c) i j = U i (σ j) * c j := by
  simp only [Matrix.mul_apply, monomial_apply, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']; simp

lemma monomial_mul_monomial (σ τ : Equiv.Perm I6) (c d : I6 → ℂ) :
    monomial σ c * monomial τ d = monomial (σ * τ) (fun j => c (τ j) * d j) := by
  ext i j
  rw [mul_monomial_apply]
  by_cases h : i = σ (τ j)
  · rw [monomial_apply, monomial_apply, if_pos h, if_pos (by simpa using h)]
  · rw [monomial_apply, monomial_apply, if_neg h, if_neg (by simpa using h)]; simp

lemma monomial_conjTranspose (σ : Equiv.Perm I6) (c : I6 → ℂ) :
    (monomial σ c)ᴴ = monomial σ⁻¹ (fun j => star (c (σ⁻¹ j))) := by
  ext i j
  simp only [conjTranspose_apply, monomial_apply]
  by_cases h : j = σ i
  · subst h; simp
  · have h' : ¬ i = σ⁻¹ j := by
      intro h''; apply h; rw [h'']; simp
    rw [if_neg h, if_neg h']; simp

lemma monomial_one : monomial 1 (fun _ => 1) = (1 : Mat6) := by
  ext i j; by_cases h : i = j
  · subst h; simp
  · rw [monomial_apply, if_neg (by simpa using h), Matrix.one_apply_ne h]

lemma isMonomial_one : IsMonomial (1 : Mat6) :=
  ⟨1, fun _ => 1, fun _ => by simp, monomial_one.symm⟩

lemma IsMonomial.mul {M N : Mat6} (hM : IsMonomial M) (hN : IsMonomial N) : IsMonomial (M * N) := by
  obtain ⟨σ, c, hc, rfl⟩ := hM
  obtain ⟨τ, d, hd, rfl⟩ := hN
  refine ⟨σ * τ, _, fun j => ?_, monomial_mul_monomial σ τ c d⟩
  simp [Complex.normSq_mul, hc, hd]

lemma IsMonomial.conjTranspose {M : Mat6} (hM : IsMonomial M) : IsMonomial Mᴴ := by
  obtain ⟨σ, c, hc, rfl⟩ := hM
  exact ⟨σ⁻¹, _, fun j => by simp [hc], monomial_conjTranspose σ c⟩

lemma IsMonomial.isUnitary {M : Mat6} (hM : IsMonomial M) : IsUnitary M := by
  obtain ⟨σ, c, hc, rfl⟩ := hM
  refine IsUnitary.of_mul_eq_one ?_
  rw [monomial_conjTranspose, monomial_mul_monomial]
  have : (fun j => star (c (σ⁻¹ (σ j))) * c j) = fun _ => (1 : ℂ) := by
    funext j; rw [show σ⁻¹ (σ j) = j by simp]; exact star_mul_self_of_normSq (hc j)
  rw [this, inv_mul_cancel, monomial_one]

/-! ### Triple equivalence is an equivalence relation -/

theorem tripleEquiv_refl (U : Triple) : TripleEquiv U U :=
  ⟨1, 1, fun _ => 1, isUnitary_one, fun _ => isMonomial_one, fun k => by simp⟩

theorem tripleEquiv_trans {U V X : Triple} (h₁ : TripleEquiv U V) (h₂ : TripleEquiv V X) :
    TripleEquiv U X := by
  obtain ⟨W, π, M, hW, hM, hV⟩ := h₁
  obtain ⟨W', π', M', hW', hM', hX⟩ := h₂
  refine ⟨W' * W, π * π', fun k => M (π' k) * M' k, hW'.mul hW,
    fun k => (hM _).mul (hM' k), fun k => ?_⟩
  rw [hX k, hV (π' k)]
  simp only [Equiv.Perm.mul_apply, Matrix.mul_assoc]

theorem tripleEquiv_symm {U V : Triple} (h : TripleEquiv U V) : TripleEquiv V U := by
  obtain ⟨W, π, M, hW, hM, hV⟩ := h
  refine ⟨Wᴴ, π⁻¹, fun k => (M (π⁻¹ k))ᴴ, hW.conjTranspose,
    fun k => (hM _).conjTranspose, fun k => ?_⟩
  rw [hV (π⁻¹ k)]
  have hk : π (π⁻¹ k) = k := by simp
  rw [hk]
  have hMk := (hM (π⁻¹ k)).isUnitary
  rw [Matrix.mul_assoc, Matrix.mul_assoc, hMk.1, Matrix.mul_one, ← Matrix.mul_assoc, hW.2,
    Matrix.one_mul]

/-! ### Invariance of the MUB property -/

lemma frame_change {W U V : Mat6} (hW : W * Wᴴ = 1) :
    (Wᴴ * U)ᴴ * (Wᴴ * V) = Uᴴ * V := by
  rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc W, hW,
    Matrix.one_mul]

lemma gram_frame {W U V : Mat6} (hW : Wᴴ * W = 1) :
    (W * U)ᴴ * (W * V) = Uᴴ * V := by
  rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Wᴴ, hW, Matrix.one_mul]

lemma unbiased_mul_monomial {U V M N : Mat6} (hM : IsMonomial M) (hN : IsMonomial N)
    (h : Unbiased U V) : Unbiased (U * M) (V * N) := by
  obtain ⟨σ, c, hc, rfl⟩ := hM
  obtain ⟨τ, d, hd, rfl⟩ := hN
  intro i j
  have e : ((U * monomial σ c)ᴴ * (V * monomial τ d)) i j =
      star (c i) * d j * (Uᴴ * V) (σ i) (τ j) := by
    rw [Matrix.mul_apply]
    simp only [conjTranspose_apply, mul_monomial_apply]
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    simp only [star_mul', conjTranspose_apply]; ring
  rw [e]
  simp only [Complex.normSq_mul, normSq_star, hc, hd, one_mul]
  exact h _ _

theorem isMUBTriple_of_tripleEquiv {U V : Triple} (h : TripleEquiv U V) (hU : IsMUBTriple U) :
    IsMUBTriple V := by
  obtain ⟨W, π, M, hW, hM, hV⟩ := h
  refine ⟨fun k => ?_, fun k l hkl => ?_⟩
  · rw [hV k]; exact (hW.mul (hU.1 _)).mul (hM k).isUnitary
  · intro i j
    rw [hV k, hV l, Matrix.mul_assoc W, Matrix.mul_assoc W, gram_frame hW.2]
    exact unbiased_mul_monomial (hM k) (hM l)
      (hU.2 _ _ (fun h => hkl (π.injective h))) i j

end MUBTriples

namespace MUBTriples

/-! ### Conjugation -/

lemma conjM_mul (A B : Mat6) : conjM (A * B) = conjM A * conjM B := by
  ext i j; simp [conjM, Matrix.mul_apply, map_sum]

lemma conjM_conjTranspose (A : Mat6) : conjM Aᴴ = (conjM A)ᴴ := by
  ext i j; simp [conjM]

lemma conjM_one : conjM (1 : Mat6) = 1 := by
  ext i j; by_cases h : i = j
  · subst h; simp [conjM]
  · simp [conjM, Matrix.one_apply_ne h]

lemma conjM_smul (c : ℂ) (A : Mat6) : conjM (c • A) = (starRingEnd ℂ c) • conjM A := by
  ext i j; simp [conjM]

lemma conjM_conjM (A : Mat6) : conjM (conjM A) = A := by
  ext i j; simp [conjM]

lemma IsUnitary.conjM {U : Mat6} (h : IsUnitary U) : IsUnitary (conjM U) := by
  refine ⟨?_, ?_⟩
  · rw [← conjM_conjTranspose, ← conjM_mul, h.1, conjM_one]
  · rw [← conjM_conjTranspose, ← conjM_mul, h.2, conjM_one]

lemma Unbiased.conjM {U V : Mat6} (h : Unbiased U V) : Unbiased (conjM U) (conjM V) := by
  intro i j
  rw [← conjM_conjTranspose, ← conjM_mul]
  simpa [MUBTriples.conjM, Complex.normSq_conj] using h i j

theorem IsMUBTriple.conj {U : Triple} (h : IsMUBTriple U) : IsMUBTriple (conjTriple U) :=
  ⟨fun k => (h.1 k).conjM, fun k l hkl => (h.2 k l hkl).conjM⟩

lemma conjTriple_conjTriple (U : Triple) : conjTriple (conjTriple U) = U := by
  funext k; exact conjM_conjM (U k)

/-! ### The standard form `{I₆, H/√6, K/√6}` -/

lemma s6_star : star s6 = s6 := by simp [s6, Complex.conj_ofReal]

lemma s6_mul_s6 : s6 * s6 = (6 : ℂ)⁻¹ := by
  have h6 : (((Real.sqrt 6 : ℝ) : ℂ)) * (((Real.sqrt 6 : ℝ) : ℂ)) = 6 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  simp only [s6]; rw [← mul_inv, h6]

lemma normSq_s6 : Complex.normSq s6 = 1 / 6 := by
  rw [s6, Complex.normSq_inv, Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num)]
  norm_num

lemma s6_ne_zero : s6 ≠ 0 := by
  intro h; have := normSq_s6; rw [h] at this; simp at this

@[simp] lemma std_zero (H K : Mat6) : std H K 0 = 1 := rfl
@[simp] lemma std_one (H K : Mat6) : std H K 1 = s6 • H := rfl
@[simp] lemma std_two (H K : Mat6) : std H K 2 = s6 • K := rfl

lemma isUnitary_s6_smul_iff (H : Mat6) :
    IsUnitary (s6 • H) ↔ H * Hᴴ = (6 : ℂ) • (1 : Mat6) := by
  have e1 : (s6 • H) * (s6 • H)ᴴ = (6 : ℂ)⁻¹ • (H * Hᴴ) := by
    rw [conjTranspose_smul, s6_star, Matrix.smul_mul, Matrix.mul_smul, smul_smul, s6_mul_s6]
  constructor
  · intro h
    have := h.1; rw [e1] at this
    have h' := congrArg (fun A => (6 : ℂ) • A) this
    simp only [smul_smul] at h'
    rw [show (6 : ℂ) * 6⁻¹ = 1 by norm_num, one_smul] at h'
    exact h'
  · intro h
    have h1 : (s6 • H) * (s6 • H)ᴴ = 1 := by
      rw [e1, h, smul_smul]; norm_num
    exact ⟨h1, mul_eq_one_comm.mp h1⟩

lemma unbiased_one_s6_smul_iff (H : Mat6) :
    Unbiased 1 (s6 • H) ↔ EntrywiseUnit H := by
  have e : ∀ i j, Complex.normSq (((1 : Mat6)ᴴ * (s6 • H)) i j) =
      (1 / 6) * Complex.normSq (H i j) := by
    intro i j
    rw [conjTranspose_one, Matrix.one_mul, Matrix.smul_apply, smul_eq_mul,
      Complex.normSq_mul, normSq_s6]
  constructor
  · intro h i j
    have := h i j; rw [e] at this; linarith
  · intro h i j; rw [e, h i j]; norm_num

lemma unbiased_s6_smul_iff (H K : Mat6) :
    Unbiased (s6 • H) (s6 • K) ↔ ∀ i j, Complex.normSq ((Hᴴ * K) i j) = 6 := by
  have e : ∀ i j, Complex.normSq (((s6 • H)ᴴ * (s6 • K)) i j) =
      (1 / 36) * Complex.normSq ((Hᴴ * K) i j) := by
    intro i j
    rw [conjTranspose_smul, s6_star, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.smul_apply, smul_eq_mul, Complex.normSq_mul, Complex.normSq_mul, normSq_s6]
    norm_num
  constructor
  · intro h i j
    have := h i j; rw [e] at this; linarith
  · intro h i j; rw [e, h i j]; norm_num

/-- `{I₆, H/√6, K/√6}` is a MUB triple iff `H`, `K` and `Hᴴ K/√6` are complex Hadamard
(the last condition written as `|(Hᴴ K)ᵢⱼ|² = 6`). -/
theorem isMUBTriple_std_iff (H K : Mat6) :
    IsMUBTriple (std H K) ↔
      Hadamard6.IsHadamard H ∧ Hadamard6.IsHadamard K ∧ ∀ i j, Complex.normSq ((Hᴴ * K) i j) = 6 := by
  constructor
  · intro h
    have h01 := h.2 0 1 (by decide)
    have h02 := h.2 0 2 (by decide)
    have h12 := h.2 1 2 (by decide)
    simp only [std_zero, std_one, std_two] at h01 h02 h12
    exact ⟨⟨(unbiased_one_s6_smul_iff H).1 h01, (isUnitary_s6_smul_iff H).1 (h.1 1)⟩,
      ⟨(unbiased_one_s6_smul_iff K).1 h02, (isUnitary_s6_smul_iff K).1 (h.1 2)⟩,
      (unbiased_s6_smul_iff H K).1 h12⟩
  · rintro ⟨hH, hK, hHK⟩
    have u0 : IsUnitary (std H K 0) := isUnitary_one
    have u1 : IsUnitary (std H K 1) := (isUnitary_s6_smul_iff H).2 hH.2
    have u2 : IsUnitary (std H K 2) := (isUnitary_s6_smul_iff K).2 hK.2
    have b01 : Unbiased (std H K 0) (std H K 1) := (unbiased_one_s6_smul_iff H).2 hH.1
    have b02 : Unbiased (std H K 0) (std H K 2) := (unbiased_one_s6_smul_iff K).2 hK.1
    have b12 : Unbiased (std H K 1) (std H K 2) := (unbiased_s6_smul_iff H K).2 hHK
    refine ⟨fun k => ?_, fun k l hkl => ?_⟩
    · fin_cases k
      exacts [u0, u1, u2]
    · fin_cases k <;> fin_cases l
      all_goals first
        | exact absurd rfl hkl
        | exact b01 | exact b02 | exact b12
        | exact unbiased_symm b01 | exact unbiased_symm b02 | exact unbiased_symm b12

/-! ### `√6` -/

/-- `√6` as a complex number. -/
noncomputable def t6 : ℂ := ((Real.sqrt 6 : ℝ) : ℂ)

lemma t6_star : star t6 = t6 := by simp [t6, Complex.conj_ofReal]

lemma s6_mul_t6 : s6 * t6 = 1 := by
  simp only [s6, t6]
  exact inv_mul_cancel₀ (by
    have : (0 : ℝ) < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
    exact_mod_cast this.ne')

lemma t6_mul_t6 : t6 * t6 = 6 := by
  simp only [t6]; rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num


lemma monomial_mul_apply (μ : Equiv.Perm I6) (m : I6 → ℂ) (X : Mat6) (i j : I6) :
    (monomial μ m * X) i j = m (μ⁻¹ i) * X (μ⁻¹ i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (μ⁻¹ i)]
  · rw [monomial_apply, if_pos (by simp)]
  · intro x _ hx
    rw [monomial_apply, if_neg, zero_mul]
    intro h; apply hx; rw [h]; simp
  · intro h; exact absurd (Finset.mem_univ _) h


end MUBTriples
