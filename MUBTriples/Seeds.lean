import MUBTriples.Recognition.Isolated

/-!
# Seeds of the continuous family (SM §"Seeds of all mutually unbiased triples")

Paper: arXiv 2611.06917v1, SM §"Seeds of all mutually unbiased triples" (Eqs.
`triple-parameter-domain`, `triple-blocks-from-seed`, `triple-diagonal-factors`), with the
canonical lift of SM Eqs. `tc-fourier-blocks`, `tc-canonical-lift` and Methods Eq.
`methods-explicit-continuous-bases`.

For seed parameters `θ₁, θ₂ ∈ ℝ` and `ℓ ∈ ℤ` (the paper uses `ℓ = 1, 2, 3`):

* `β = (θ₂ - 2θ₁ + 2π(ℓ-1))/3`, `γ = -(θ₁ + θ₂ + 2π(ℓ-1))/3`,
  `σ = e^{-iβ} + e^{i(β-γ)} + e^{iγ}` (`seedβ`, `seedγ`, `seedσ`);
* the domain `|σ|⁴ + 18|σ|² + 8 Re(σ³) - 27 ≤ 0` (`domainPoly`, `InDomain`);
* `ρ₁, ρ₂, ρ₃` the roots of `t³ + σt² - σ̄t - 1` in any order (`IsRootTriple σ ρ`, with
  `ρ 0, ρ 1, ρ 2` for `ρ₁, ρ₂, ρ₃`);
* the circulants `A` with first row `(1, e^{iβ}, e^{iγ})` and `B` with first row
  `(1, ρ₁⁻¹, ρ₃)` (`circM`, `seedA`, `seedB`) and `H = [[A, B], [B†, -A†]]` (`seedH`);
* `λₖ = (F̂₃ A F̂₃†)ₖₖ/√6`, `μₖ = (F̂₃ B F̂₃†)ₖₖ/√6` (`fcoef`), `D = iε λμ/|λμ|`,
  `R = λ + Dμ̄`, `S = λ - Dμ̄` with signs `εₖ = ±1` (`seedD`, `seedR`, `seedS`, `ε : I3 → ℤˣ`);
* the triple of Methods Eq. `methods-explicit-continuous-bases` (`seedTriple`).

## Main results

* `seedTriple_spec` / `seedTriple_isFamilyMember`: for parameters in the domain and every root
  ordering and choice of signs, the roots have unit modulus, `λₖ μₖ ≠ 0`, `D, R, S` are unit,
  the triple is a MUB triple of the explicit family form (`IsFamilyMember`), its transition
  is `√6 U₂† U₃ = H`, and `H` is complex Hadamard.  The abstract version for any unit first
  rows with cancelling autocorrelations is `construct_spec`.
* `exists_isRootTriple`, `domainPoly_eq_disc` (the domain polynomial is the discriminant of
  the cubic), `IsRootTriple.normSq_of_domain` (domain ⇒ all roots unimodular, proved, not
  assumed), `domainPoly_nonpos_of_unit` (converse), `domainPoly_nonpos_iff`.
* `inDomain_iff`: the domain is *exactly* the set of `(θ₁, θ₂, ℓ)` for which some circulant
  `B` (first entry `1`) makes `[[A, B], [B†, -A†]]` Hadamard, and exactly where all roots of
  the cubic are unimodular ("the allowed parameter pairs are exactly those satisfying ...").
* `seedOf_seedTriple_corner`: the upper-left corner of `√6 U₂† U₃` has the seed
  `(θ₁, θ₂, θ₁ - θ₂, θ₁)`; `seedOf_corner142`: rows `(1, 4, 2)`, columns `(1, 2, 3)` of `√6 U₃†`
  have the seed `(θ'₁, θ'₂, -2π/3, 2π/3)` with `e^{iθ'ₖ} = Rₖₖ Sₖₖ D₁₁ / (R₁₁ S₁₁ Dₖₖ)`.
* `familyMember_tripleEquiv_seedTriple`: conversely every `IsFamilyMember` triple is
  equivalent (by column phases only) to a seed triple with `ℓ = 1`; hence
  `exists_familyMember_iff_seed`: being equivalent to a family member is the same as being
  equivalent to a seed triple with parameters in the domain.

Nothing is assumed: the existence and unimodularity of the cubic roots under the domain
inequality are proved (algebraic closure of `ℂ` for existence; the self-inversive symmetry
`ρ ↦ 1/ρ̄` and the sign of the discriminant for unimodularity).
-/

open Matrix Hadamard6

namespace MUBTriples

/-! ### Circulants given by their first row -/

/-- The circulant `3 × 3` matrix with first row `a`: `(circM a) r s = a (s - r)`, i.e.
`[[a₀, a₁, a₂], [a₂, a₀, a₁], [a₁, a₂, a₀]]` (the pattern of SM Eq. `triple-blocks-from-seed`). -/
def circM (a : I3 → ℂ) : Mat3 := Matrix.of fun r s => a (s - r)

@[simp] lemma circM_apply (a : I3 → ℂ) (r s : I3) : circM a r s = a (s - r) := rfl

/-- `Σₑ aₑ ω^{-k e}` (written with `ω^{2ke}`). -/
noncomputable def fourierRow (a : I3 → ℂ) (k : I3) : ℂ := ∑ e : I3, a e * ω ^ (2 * (k.val * e.val))

/-- The normalized Fourier matrix `F̂₃ = F₃/√3`. -/
noncomputable def F3n : Mat3 := (((Real.sqrt 3 : ℝ) : ℂ)⁻¹) • F3

/-- The Fourier coefficient of SM Eq. `triple-diagonal-factors`:
`λₖ = (F̂₃ A F̂₃†)ₖₖ / √6`. -/
noncomputable def fcoef (A : Mat3) (k : I3) : ℂ := (F3n * A * F3nᴴ) k k / t6

lemma I3_neg_one : (-1 : I3) = 2 := rfl
lemma I3_neg_two : (-2 : I3) = 1 := rfl

lemma circ_fourierRow (a : I3 → ℂ) : circ (fourierRow a) = (3 : ℂ) • circM a := by
  ext s s'
  rw [circ_apply, Matrix.smul_apply, smul_eq_mul, circM_apply]
  simp only [fourierRow, Fin.sum_univ_three]
  fin_cases s <;> fin_cases s' <;> simp [I3_neg_one, I3_neg_two] <;> ω_norm

lemma sqrt3_inv_mul_self :
    (((Real.sqrt 3 : ℝ) : ℂ)⁻¹) * (((Real.sqrt 3 : ℝ) : ℂ)⁻¹) = (3 : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

lemma F3n_conjTranspose : F3nᴴ = (((Real.sqrt 3 : ℝ) : ℂ)⁻¹) • F3ᴴ := by
  rw [F3n, conjTranspose_smul]
  congr 1
  simp [Complex.conj_ofReal]

/-- `F̂₃` diagonalizes the circulants: `F̂₃ (F₃ᴴ diag(x) F₃) F̂₃ᴴ = 3 diag(x)`. -/
lemma F3n_circ (x : I3 → ℂ) : F3n * circ x * F3nᴴ = (3 : ℂ) • diagonal x := by
  rw [F3n_conjTranspose, F3n, circ, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, sqrt3_inv_mul_self]
  have : F3 * (F3ᴴ * diagonal x * F3) * F3ᴴ = (9 : ℂ) • diagonal x := by
    calc F3 * (F3ᴴ * diagonal x * F3) * F3ᴴ = (F3 * F3ᴴ) * diagonal x * (F3 * F3ᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = (9 : ℂ) • diagonal x := by
          rw [F3_mul_conjTranspose, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
            Matrix.mul_one, smul_smul]; norm_num
  rw [this, smul_smul]; norm_num

lemma fcoef_smul_circ (c : ℂ) (x : I3 → ℂ) (k : I3) :
    fcoef (c • circ x) k = c * 3 * x k * s6 := by
  rw [fcoef, Matrix.mul_smul, Matrix.smul_mul, F3n_circ, smul_smul, Matrix.smul_apply,
    diagonal_apply_eq, smul_eq_mul, div_eq_mul_inv]
  rfl

lemma circM_eq (a : I3 → ℂ) : circM a = (3 : ℂ)⁻¹ • circ (fourierRow a) := by
  rw [circ_fourierRow, smul_smul]; norm_num

/-- `λₖ = Σₑ aₑ ω^{-ke} / √6`. -/
lemma fcoef_circM (a : I3 → ℂ) (k : I3) : fcoef (circM a) k = s6 * fourierRow a k := by
  rw [circM_eq, fcoef_smul_circ]; field_simp

lemma six_mul_s6 : 6 * s6 = t6 := by
  linear_combination t6 * s6_mul_t6 - s6 * t6_mul_t6

/-- `F₃ᴴ diag(2λ) F₃ = √6 A` for the circulant `A = circM a`. -/
lemma circ_two_fcoef (a : I3 → ℂ) :
    circ (fun k => 2 * fcoef (circM a) k) = t6 • circM a := by
  have : (fun k => 2 * fcoef (circM a) k) = (2 * s6) • fourierRow a := by
    funext k; rw [fcoef_circM]; simp; ring
  rw [this, circ_smul, circ_fourierRow, smul_smul, ← six_mul_s6]; ring_nf

lemma fourierRow_eq_fsum (a : I3 → ℂ) (k : I3) : fourierRow a k = fsum a (2 * k.val) := by
  simp only [fourierRow, fsum, Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, mul_zero, pow_zero, mul_one]
  ring_nf

lemma normSq_fcoef_circM (a : I3 → ℂ) (k : I3) :
    Complex.normSq (fcoef (circM a) k) =
      (sqSum a + 2 * (ω ^ ((2 * k.val) % 3) * autoc a).re) / 6 := by
  rw [fcoef_circM, Complex.normSq_mul, normSq_s6, fourierRow_eq_fsum, fsum_mod,
    fsum_normSq _ _ (Nat.mod_lt _ (by norm_num))]
  ring

lemma sqSum_of_unitVec {a : I3 → ℂ} (ha : UnitVec a) : sqSum a = 3 := by
  rw [sqSum_eq, ha 0, ha 1, ha 2]; norm_num

/-- `|λₖ|² + |μₖ|² = 1` when the autocorrelations cancel (unitarity of `[[A, B], [B†, -A†]]`). -/
lemma normSq_fcoef_add {a b : I3 → ℂ} (ha : UnitVec a) (hb : UnitVec b)
    (hab : autoc a + autoc b = 0) (k : I3) :
    Complex.normSq (fcoef (circM a) k) + Complex.normSq (fcoef (circM b) k) = 1 := by
  rw [normSq_fcoef_circM, normSq_fcoef_circM, sqSum_of_unitVec ha, sqSum_of_unitVec hb]
  have : (ω ^ ((2 * k.val) % 3) * autoc a).re + (ω ^ ((2 * k.val) % 3) * autoc b).re = 0 := by
    rw [← Complex.add_re, ← mul_add, hab, mul_zero, Complex.zero_re]
  linarith

lemma flat_two_fcoef {a : I3 → ℂ} (ha : UnitVec a) : Flat (fun k => 2 * fcoef (circM a) k) := by
  intro s s'
  rw [circ_two_fcoef, Matrix.smul_apply, smul_eq_mul, Complex.normSq_mul, normSq_t6, circM_apply,
    ha]
  norm_num

lemma fcoef_ne_zero {a b : I3 → ℂ} (ha : UnitVec a) (hb : UnitVec b)
    (hab : autoc a + autoc b = 0) (k : I3) : fcoef (circM a) k ≠ 0 := by
  have h := flat_ne_zero (flat_two_fcoef ha) (fun t => by
    have := normSq_fcoef_add ha hb hab t
    have := Complex.normSq_nonneg (fcoef (circM b) t)
    simp only [Complex.normSq_mul]
    norm_num
    linarith) k
  intro h0; apply h; simp [h0]

/-! ### The diagonal factors `D, R, S` (SM Eq. `triple-diagonal-factors`) -/

/-- The transition `H = [[A, B], [B†, -A†]]` of SM Eq. `triple-blocks-from-seed`. -/
def seedH (A B : Mat3) : Mat6 := fromBlocks A B Bᴴ (-Aᴴ)

/-- `D_kk = i εₖ λₖ μₖ / |λₖ μₖ|`, with `λₖ, μₖ` the Fourier coefficients of `A, B`. -/
noncomputable def seedD (A B : Mat3) (ε : I3 → ℤˣ) (k : I3) : ℂ :=
  Complex.I * (((ε k : ℤ) : ℂ)) * (fcoef A k * fcoef B k) /
    ((‖fcoef A k * fcoef B k‖ : ℝ) : ℂ)

/-- `R_kk = λₖ + D_kk μ̄ₖ`. -/
noncomputable def seedR (A B : Mat3) (ε : I3 → ℤˣ) (k : I3) : ℂ :=
  fcoef A k + seedD A B ε k * star (fcoef B k)

/-- `S_kk = λₖ - D_kk μ̄ₖ`. -/
noncomputable def seedS (A B : Mat3) (ε : I3 → ℤˣ) (k : I3) : ℂ :=
  fcoef A k - seedD A B ε k * star (fcoef B k)

/-- The triple obtained by substituting `D, R, S` in Methods Eq.
`methods-explicit-continuous-bases`. -/
noncomputable def constructTriple (A B : Mat3) (ε : I3 → ℤˣ) : Triple :=
  familyTriple (seedD A B ε) (seedR A B ε) (seedS A B ε)

lemma normSq_units_int (u : ℤˣ) : Complex.normSq (((u : ℤ) : ℂ)) = 1 := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]

lemma intCast_units_eq_ofReal (u : ℤˣ) : (((u : ℤ) : ℂ)) = ((((u : ℤ) : ℝ)) : ℂ) := by
  push_cast; rfl

lemma normSq_div_norm {z : ℂ} (hz : z ≠ 0) : Complex.normSq (z / ((‖z‖ : ℝ) : ℂ)) = 1 := by
  have h : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
  rw [Complex.normSq_div, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq]
  field_simp

lemma normSq_seedD {A B : Mat3} (ε : I3 → ℤˣ) {k : I3} (h : fcoef A k * fcoef B k ≠ 0) :
    Complex.normSq (seedD A B ε k) = 1 := by
  rw [seedD, mul_div_assoc, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_I,
    normSq_units_int, normSq_div_norm h]
  norm_num

/-- The cross term `λ · conj(D μ̄)` is purely imaginary. -/
lemma re_cross (l m : ℂ) (c : ℝ) :
    (l * star (Complex.I * (c : ℂ) * (l * m) / ((‖l * m‖ : ℝ) : ℂ) * star m)).re = 0 := by
  have e : l * star (Complex.I * (c : ℂ) * (l * m) / ((‖l * m‖ : ℝ) : ℂ) * star m) =
      Complex.I * (((-(c * Complex.normSq (l * m) / ‖l * m‖)) : ℝ) : ℂ) := by
    have h1 : l * star (Complex.I * (c : ℂ) * (l * m) / ((‖l * m‖ : ℝ) : ℂ) * star m) =
        -(Complex.I * (c : ℂ) * ((starRingEnd ℂ) (l * m) * (l * m)) / ((‖l * m‖ : ℝ) : ℂ)) := by
      simp only [star_mul', star_div₀, Complex.star_def, Complex.conj_I,
        Complex.conj_ofReal, map_mul, Complex.conj_conj]
      ring
    rw [h1, ← Complex.normSq_eq_conj_mul_self]
    push_cast
    ring
  rw [e, Complex.I_mul_re, Complex.ofReal_im, neg_zero]

lemma normSq_seedR {A B : Mat3} (ε : I3 → ℤˣ) {k : I3} (h : fcoef A k * fcoef B k ≠ 0) :
    Complex.normSq (seedR A B ε k) =
      Complex.normSq (fcoef A k) + Complex.normSq (fcoef B k) := by
  have hD := normSq_seedD ε h
  have hre := re_cross (fcoef A k) (fcoef B k) ((ε k : ℤ) : ℝ)
  rw [← intCast_units_eq_ofReal] at hre
  rw [seedR, Complex.normSq_add, Complex.normSq_mul, hD, normSq_star]
  rw [show (starRingEnd ℂ) (seedD A B ε k * star (fcoef B k)) =
    star (seedD A B ε k * star (fcoef B k)) from rfl]
  rw [seedD, hre]; ring

lemma normSq_seedS {A B : Mat3} (ε : I3 → ℤˣ) {k : I3} (h : fcoef A k * fcoef B k ≠ 0) :
    Complex.normSq (seedS A B ε k) =
      Complex.normSq (fcoef A k) + Complex.normSq (fcoef B k) := by
  have hD := normSq_seedD ε h
  have hre := re_cross (fcoef A k) (fcoef B k) ((ε k : ℤ) : ℝ)
  rw [← intCast_units_eq_ofReal] at hre
  rw [seedS, Complex.normSq_sub, Complex.normSq_mul, hD, normSq_star]
  rw [show (starRingEnd ℂ) (seedD A B ε k * star (fcoef B k)) =
    star (seedD A B ε k * star (fcoef B k)) from rfl]
  rw [seedD, hre]; ring

/-! ### The construction gives a family member with transition `H` -/

lemma circ_conjTranspose (d : I3 → ℂ) : (circ d)ᴴ = circ (star d) := by
  simp only [circ, conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose,
    Matrix.mul_assoc]

lemma t6_s6_s6 : t6 * s6 * s6 = s6 := by
  rw [mul_comm t6 s6, s6_mul_t6, one_mul]

/-- The transition `√6 U₂† U₃` of an explicit family triple, as four circulant blocks. -/
theorem familyTriple_transition {d r s : I3 → ℂ} (hd : UnitVec d) (hr : UnitVec r)
    (hs : UnitVec s) :
    t6 • ((familyTriple d r s 1)ᴴ * familyTriple d r s 2) =
      s6 • fromBlocks (circ (r + s)) (circ (d * (star r - star s)))
        (circ (star (d * (star r - star s)))) (circ (-star (r + s))) := by
  rw [familyTriple, std_one, std_two, conjTranspose_smul, s6_star, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, smul_smul, t6_s6_s6, famK_eq_symK hr hs,
    symH_conjTranspose_mul_symK]
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
  rw [e2, e3, e4]

lemma seedR_add_seedS (A B : Mat3) (ε : I3 → ℤˣ) :
    seedR A B ε + seedS A B ε = fun k => 2 * fcoef A k := by
  funext k; simp only [Pi.add_apply, seedR, seedS]; ring

lemma seedD_mul_sub {A B : Mat3} (ε : I3 → ℤˣ) (hD : UnitVec (seedD A B ε)) :
    seedD A B ε * (star (seedR A B ε) - star (seedS A B ε)) = fun k => 2 * fcoef B k := by
  funext k
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.star_apply, seedR, seedS, star_add, star_sub,
    star_mul', star_star]
  have := mul_star_self_of_normSq (hD k)
  linear_combination (2 * fcoef B k) * this

lemma star_two_mul (f : I3 → ℂ) : star (fun k => 2 * f k) = fun k => 2 * star (f k) := by
  funext k; simp

/-- **The seed construction, abstract form** (SM Eq. `triple-diagonal-factors`).  Let `a, b` be
unit first rows of circulants `A = circM a`, `B = circM b` whose autocorrelations cancel
(`Σ b_{s+1} b̄_s = -Σ a_{s+1} ā_s`, the unitarity of `[[A, B], [B†, -A†]]`).  Then for every
choice of signs `ε`:
the Fourier coefficients `λₖ, μₖ` do not vanish, `D, R, S` have unit entries, the triple
of Methods Eq. `methods-explicit-continuous-bases` is a MUB triple (a family member), its
transition is `√6 U₂† U₃ = H = [[A, B], [B†, -A†]]`, and `H` is a complex Hadamard matrix. -/
theorem construct_spec {a b : I3 → ℂ} (ha : UnitVec a) (hb : UnitVec b)
    (hab : autoc a + autoc b = 0) (ε : I3 → ℤˣ) :
    (∀ k, fcoef (circM a) k ≠ 0 ∧ fcoef (circM b) k ≠ 0) ∧
      UnitVec (seedD (circM a) (circM b) ε) ∧ UnitVec (seedR (circM a) (circM b) ε) ∧
      UnitVec (seedS (circM a) (circM b) ε) ∧
      IsFamilyMember (constructTriple (circM a) (circM b) ε) ∧
      t6 • ((constructTriple (circM a) (circM b) ε 1)ᴴ * constructTriple (circM a) (circM b) ε 2)
        = seedH (circM a) (circM b) ∧
      Hadamard6.IsHadamard (seedH (circM a) (circM b)) := by
  have hba : autoc b + autoc a = 0 := by rw [add_comm]; exact hab
  have hne : ∀ k, fcoef (circM a) k ≠ 0 ∧ fcoef (circM b) k ≠ 0 :=
    fun k => ⟨fcoef_ne_zero ha hb hab k, fcoef_ne_zero hb ha hba k⟩
  have hprod : ∀ k, fcoef (circM a) k * fcoef (circM b) k ≠ 0 :=
    fun k => mul_ne_zero (hne k).1 (hne k).2
  have hD : UnitVec (seedD (circM a) (circM b) ε) := fun k => normSq_seedD ε (hprod k)
  have hR : UnitVec (seedR (circM a) (circM b) ε) := fun k => by
    rw [normSq_seedR ε (hprod k), normSq_fcoef_add ha hb hab k]
  have hS : UnitVec (seedS (circM a) (circM b) ε) := fun k => by
    rw [normSq_seedS ε (hprod k), normSq_fcoef_add ha hb hab k]
  have hRS := seedR_add_seedS (circM a) (circM b) ε
  have hDRS := seedD_mul_sub ε hD
  have hT : IsMUBTriple (constructTriple (circM a) (circM b) ε) := by
    rw [constructTriple, familyTriple_isMUBTriple_iff hD hR hS, hRS, hDRS]
    exact ⟨flat_two_fcoef ha, flat_two_fcoef hb⟩
  have htrans : t6 • ((constructTriple (circM a) (circM b) ε 1)ᴴ *
      constructTriple (circM a) (circM b) ε 2) = seedH (circM a) (circM b) := by
    rw [constructTriple, familyTriple_transition hD hR hS, hRS, hDRS, circ_two_fcoef,
      circ_two_fcoef, star_two_mul, star_two_mul]
    have e1 : circ (fun k => 2 * star (fcoef (circM b) k)) = (t6 • circM b)ᴴ := by
      rw [← circ_two_fcoef, circ_conjTranspose, star_two_mul]
    have e2 : circ (-fun k => 2 * star (fcoef (circM a) k)) = -(t6 • circM a)ᴴ := by
      rw [circ_neg, ← circ_two_fcoef, circ_conjTranspose, star_two_mul]
    rw [e1, e2, seedH, conjTranspose_smul, conjTranspose_smul, t6_star, fromBlocks_smul]
    congr 1 <;> simp only [smul_neg, smul_smul, s6_mul_t6, one_smul]
  refine ⟨hne, hD, hR, hS, ⟨_, _, _, hD, hR, hS, rfl, hT⟩, htrans, ?_⟩
  -- `H = √6 U₂† U₃` is Hadamard
  rw [← htrans]
  set X := (constructTriple (circM a) (circM b) ε 1)ᴴ * constructTriple (circM a) (circM b) ε 2
  have hX : IsUnitary X := (hT.1 1).conjTranspose.mul (hT.1 2)
  refine ⟨fun i j => ?_, ?_⟩
  · rw [Matrix.smul_apply, smul_eq_mul, Complex.normSq_mul, normSq_t6]
    have := hT.2 1 2 (by decide) i j
    rw [this]; norm_num
  · rw [conjTranspose_smul, t6_star, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hX.1,
      t6_mul_t6]

/-! ### The cubic `t³ + σ t² - σ̄ t - 1` and the domain inequality -/

/-- The left side of SM Eq. `triple-parameter-domain`: `|σ|⁴ + 18|σ|² + 8 Re(σ³) - 27`.
It is the discriminant of `t³ + σ t² - σ̄ t - 1` (`domainPoly_eq_disc`). -/
noncomputable def domainPoly (σ : ℂ) : ℝ :=
  Complex.normSq σ ^ 2 + 18 * Complex.normSq σ + 8 * (σ ^ 3).re - 27

/-- `ρ₁, ρ₂, ρ₃` (here `ρ 0, ρ 1, ρ 2`) are the roots of `t³ + σ t² - σ̄ t - 1`, counted with
multiplicity, in some order. -/
def IsRootTriple (σ : ℂ) (ρ : Fin 3 → ℂ) : Prop :=
  ∀ t : ℂ, (t - ρ 0) * (t - ρ 1) * (t - ρ 2) = t ^ 3 + σ * t ^ 2 - star σ * t - 1

namespace IsRootTriple

variable {σ : ℂ} {ρ : Fin 3 → ℂ}

lemma prod (h : IsRootTriple σ ρ) : ρ 0 * ρ 1 * ρ 2 = 1 := by
  linear_combination -(h 0)

lemma sum (h : IsRootTriple σ ρ) : ρ 0 + ρ 1 + ρ 2 = -σ := by
  linear_combination (-1 / 2 : ℂ) * h 1 + (-1 / 2 : ℂ) * h (-1) + h 0

lemma sum2 (h : IsRootTriple σ ρ) : ρ 0 * ρ 1 + ρ 0 * ρ 2 + ρ 1 * ρ 2 = -star σ := by
  linear_combination (1 / 2 : ℂ) * h 1 - (1 / 2 : ℂ) * h (-1)

lemma ne_zero (h : IsRootTriple σ ρ) (k : Fin 3) : ρ k ≠ 0 := by
  intro h0
  have := h.prod
  fin_cases k <;> simp_all

lemma swap01 (h : IsRootTriple σ ρ) : IsRootTriple σ ![ρ 1, ρ 0, ρ 2] := by
  intro t; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [← h t]; ring

lemma swap02 (h : IsRootTriple σ ρ) : IsRootTriple σ ![ρ 2, ρ 1, ρ 0] := by
  intro t; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [← h t]; ring

end IsRootTriple

lemma isRootTriple_of_vieta {σ : ℂ} {ρ : Fin 3 → ℂ} (h1 : ρ 0 + ρ 1 + ρ 2 = -σ)
    (h2 : ρ 0 * ρ 1 + ρ 0 * ρ 2 + ρ 1 * ρ 2 = -star σ) (h3 : ρ 0 * ρ 1 * ρ 2 = 1) :
    IsRootTriple σ ρ := fun t => by
  linear_combination (-t ^ 2) * h1 + t * h2 - h3

/-- The cubic has three roots counted with multiplicity (`ℂ` is algebraically closed). -/
theorem exists_isRootTriple (σ : ℂ) : ∃ ρ : Fin 3 → ℂ, IsRootTriple σ ρ := by
  open Polynomial in
  obtain ⟨r, hr⟩ := Complex.exists_root
    (f := X ^ 3 + C σ * X ^ 2 - C (star σ) * X - 1) (by
      have : (X ^ 3 + C σ * X ^ 2 - C (star σ) * X - 1 : ℂ[X]).degree = 3 := by
        compute_degree!
      rw [this]; norm_num)
  have hr' : r ^ 3 + σ * r ^ 2 - star σ * r - 1 = 0 := by
    simpa [Polynomial.IsRoot] using hr
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_eq_mul_self ((σ + r) ^ 2 - 4 * (r * (σ + r) - star σ))
  refine ⟨![r, (-(σ + r) + δ) / 2, (-(σ + r) - δ) / 2], fun t => ?_⟩
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  linear_combination (t - r) / 4 * hδ - hr'

lemma two_re_pow (σ : ℂ) : (2 : ℂ) * ((σ ^ 3).re : ℂ) = σ ^ 3 + star σ ^ 3 := by
  rw [two_re, star_pow]

lemma domainPoly_cast (σ : ℂ) :
    ((domainPoly σ : ℝ) : ℂ) =
      σ ^ 2 * star σ ^ 2 + 4 * σ ^ 3 + 4 * star σ ^ 3 + 18 * (σ * star σ) - 27 := by
  simp only [domainPoly]
  push_cast
  rw [normSq_eq_mul_star]
  linear_combination 4 * two_re_pow σ

/-- **The domain polynomial is the discriminant** of `t³ + σ t² - σ̄ t - 1`. -/
theorem domainPoly_eq_disc {σ : ℂ} {ρ : Fin 3 → ℂ} (h : IsRootTriple σ ρ) :
    ((domainPoly σ : ℝ) : ℂ) = ((ρ 0 - ρ 1) * (ρ 0 - ρ 2) * (ρ 1 - ρ 2)) ^ 2 := by
  have hs : σ = -(ρ 0 + ρ 1 + ρ 2) := by linear_combination h.sum
  have hs' : star σ = -(ρ 0 * ρ 1 + ρ 0 * ρ 2 + ρ 1 * ρ 2) := by linear_combination h.sum2
  have h3 := h.prod
  rw [domainPoly_cast, hs', hs]
  linear_combination (4 * ρ 0 ^ 3 - 6 * ρ 0 ^ 2 * ρ 1 - 6 * ρ 0 ^ 2 * ρ 2 - 6 * ρ 0 * ρ 1 ^ 2 -
    3 * ρ 0 * ρ 1 * ρ 2 - 6 * ρ 0 * ρ 2 ^ 2 + 4 * ρ 1 ^ 3 - 6 * ρ 1 ^ 2 * ρ 2 -
    6 * ρ 1 * ρ 2 ^ 2 + 4 * ρ 2 ^ 3 + 27) * h3

lemma sq_sub_of_unit {x y : ℂ} (hx : Complex.normSq x = 1) (hy : Complex.normSq y = 1) :
    (x - y) ^ 2 = -(x * y) * ((Complex.normSq (x - y) : ℝ) : ℂ) := by
  rw [normSq_eq_mul_star, star_sub]
  have h1 := mul_star_self_of_normSq hx
  have h2 := mul_star_self_of_normSq hy
  linear_combination (x * y - y ^ 2) * h1 + (x * y - x ^ 2) * h2

/-- If all roots have modulus one, the domain inequality holds:
`domainPoly σ = -|ρ₁ - ρ₂|² |ρ₁ - ρ₃|² |ρ₂ - ρ₃|²`. -/
theorem domainPoly_nonpos_of_unit {σ : ℂ} {ρ : Fin 3 → ℂ} (h : IsRootTriple σ ρ)
    (hu : ∀ k, Complex.normSq (ρ k) = 1) : domainPoly σ ≤ 0 := by
  have e : ((domainPoly σ : ℝ) : ℂ) = ((-(Complex.normSq (ρ 0 - ρ 1) *
      Complex.normSq (ρ 0 - ρ 2) * Complex.normSq (ρ 1 - ρ 2)) : ℝ) : ℂ) := by
    rw [domainPoly_eq_disc h, mul_pow, mul_pow, sq_sub_of_unit (hu 0) (hu 1),
      sq_sub_of_unit (hu 0) (hu 2), sq_sub_of_unit (hu 1) (hu 2)]
    push_cast
    linear_combination (-(ρ 0 * ρ 1 * ρ 2 + 1) * ((Complex.normSq (ρ 0 - ρ 1) : ℂ) *
      (Complex.normSq (ρ 0 - ρ 2) : ℂ) * (Complex.normSq (ρ 1 - ρ 2) : ℂ))) * h.prod
  rw [Complex.ofReal_inj] at e
  rw [e]
  have := Complex.normSq_nonneg (ρ 0 - ρ 1)
  have := Complex.normSq_nonneg (ρ 0 - ρ 2)
  have := Complex.normSq_nonneg (ρ 1 - ρ 2)
  have : 0 ≤ Complex.normSq (ρ 0 - ρ 1) * Complex.normSq (ρ 0 - ρ 2) *
    Complex.normSq (ρ 1 - ρ 2) := by positivity
  linarith

/-- For `|r| ≠ 1`, the roots `r, 1/r̄, r̄/r` have a positive discriminant. -/
lemma disc_pos_of_not_unit {r : ℂ} (hr : r ≠ 0) (hN : Complex.normSq r ≠ 1) :
    ∃ x : ℝ, 0 < x ∧
      ((r - (star r)⁻¹) * (r - star r / r) * ((star r)⁻¹ - star r / r)) ^ 2 = (x : ℂ) := by
  set N := Complex.normSq r with hNdef
  have hN0 : N ≠ 0 := by rw [hNdef]; exact (Complex.normSq_pos.2 hr).ne'
  have hsr : star r ≠ 0 := star_ne_zero.2 hr
  have hNc : (N : ℂ) = r * star r := normSq_eq_mul_star r
  set X : ℝ := 2 * (r ^ 3).re - N ^ 2 - N with hXdef
  have hXc : (X : ℂ) = (r ^ 2 - star r) * (r - star r ^ 2) := by
    rw [hXdef]; push_cast; rw [two_re_pow, hNc]; ring
  have hX : X ≠ 0 := by
    intro h0
    rw [h0, Complex.ofReal_zero, eq_comm, mul_eq_zero] at hXc
    have hNN : N ^ 2 = N := by
      rcases hXc with h | h
      · have := congrArg Complex.normSq (sub_eq_zero.1 h)
        rwa [map_pow, normSq_star] at this
      · have := congrArg Complex.normSq (sub_eq_zero.1 h)
        rw [map_pow, normSq_star] at this
        exact this.symm
    have : N * (N - 1) = 0 := by linear_combination hNN
    rcases mul_eq_zero.1 this with h | h
    · exact hN0 h
    · exact hN (sub_eq_zero.1 h)
  have hP : (r - (star r)⁻¹) * (r - star r / r) * ((star r)⁻¹ - star r / r) =
      (((N - 1) * X / N ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [hXc, hNc]
    field_simp
  refine ⟨((N - 1) * X / N ^ 2) ^ 2, ?_, by rw [hP]; push_cast; ring⟩
  have h1 : N - 1 ≠ 0 := sub_ne_zero.2 hN
  positivity

/-- **Under the domain inequality every root has modulus one** (SM: "Then the roots ... have
unit modulus").  If `|ρ₁| ≠ 1`, then `1/ρ̄₁` is another root (the cubic is self-inversive up to
sign), the third root is `ρ̄₁/ρ₁`, and the discriminant is positive. -/
theorem IsRootTriple.normSq_zero_of_domain {σ : ℂ} {ρ : Fin 3 → ℂ} (h : IsRootTriple σ ρ)
    (hdom : domainPoly σ ≤ 0) : Complex.normSq (ρ 0) = 1 := by
  by_contra hN
  set r := ρ 0 with hrdef
  have hr : r ≠ 0 := h.ne_zero 0
  have hsr : star r ≠ 0 := star_ne_zero.2 hr
  have hcub : r ^ 3 + σ * r ^ 2 - star σ * r - 1 = 0 := by
    have := h r; rw [hrdef, sub_self, zero_mul, zero_mul] at this; exact this.symm
  have hstar : star r ^ 3 + star σ * star r ^ 2 - σ * star r - 1 = 0 := by
    have := congrArg star hcub
    simpa [star_sub, star_add, star_mul', star_pow] using this
  have hcub' : ((star r)⁻¹ - ρ 0) * ((star r)⁻¹ - ρ 1) * ((star r)⁻¹ - ρ 2) = 0 := by
    rw [h]
    field_simp
    linear_combination -hstar
  have hne0 : (star r)⁻¹ ≠ ρ 0 := by
    intro he
    apply hN
    have : r * star r = 1 := (mul_eq_one_iff_eq_inv₀ hsr).2 (hrdef.trans he.symm)
    have h2 := normSq_eq_mul_star r
    rw [this] at h2
    exact_mod_cast h2
  have h3 := h.prod
  obtain ⟨x, hx, hxe⟩ := disc_pos_of_not_unit hr hN
  have hd := domainPoly_eq_disc h
  rcases mul_eq_zero.1 hcub' with h01 | h2
  · rcases mul_eq_zero.1 h01 with h0 | h1
    · exact hne0 (sub_eq_zero.1 h0)
    · -- `ρ₂ = 1/r̄`, `ρ₃ = r̄/r`
      have e1 : ρ 1 = (star r)⁻¹ := (sub_eq_zero.1 h1).symm
      have e2 : ρ 2 = star r / r := by
        rw [← hrdef, e1] at h3
        field_simp at h3 ⊢
        linear_combination h3
      rw [← hrdef, e1, e2, hxe, Complex.ofReal_inj] at hd
      linarith
  · have e2 : ρ 2 = (star r)⁻¹ := (sub_eq_zero.1 h2).symm
    have e1 : ρ 1 = star r / r := by
      rw [← hrdef, e2] at h3
      field_simp at h3 ⊢
      linear_combination h3
    have : ((r - ρ 1) * (r - ρ 2) * (ρ 1 - ρ 2)) ^ 2 = (x : ℂ) := by
      rw [e1, e2, ← hxe]; ring
    rw [← hrdef, this, Complex.ofReal_inj] at hd
    linarith

theorem IsRootTriple.normSq_of_domain {σ : ℂ} {ρ : Fin 3 → ℂ} (h : IsRootTriple σ ρ)
    (hdom : domainPoly σ ≤ 0) (k : Fin 3) : Complex.normSq (ρ k) = 1 := by
  fin_cases k
  · exact h.normSq_zero_of_domain hdom
  · simpa using h.swap01.normSq_zero_of_domain hdom
  · simpa using h.swap02.normSq_zero_of_domain hdom

/-- **The domain inequality characterizes unit roots**: `domainPoly σ ≤ 0` iff the roots of
`t³ + σ t² - σ̄ t - 1` all have modulus one. -/
theorem domainPoly_nonpos_iff (σ : ℂ) :
    domainPoly σ ≤ 0 ↔ ∃ ρ : Fin 3 → ℂ, IsRootTriple σ ρ ∧ ∀ k, Complex.normSq (ρ k) = 1 := by
  constructor
  · intro hdom
    obtain ⟨ρ, hρ⟩ := exists_isRootTriple σ
    exact ⟨ρ, hρ, hρ.normSq_of_domain hdom⟩
  · rintro ⟨ρ, hρ, hu⟩
    exact domainPoly_nonpos_of_unit hρ hu

/-! ### The seed parameters `(θ₁, θ₂)` and `ℓ` -/

/-- `β = (θ₂ - 2θ₁ + 2π(ℓ - 1))/3`. -/
noncomputable def seedβ (θ₁ θ₂ : ℝ) (ℓ : ℤ) : ℝ := (θ₂ - 2 * θ₁ + 2 * Real.pi * (ℓ - 1)) / 3

/-- `γ = -(θ₁ + θ₂ + 2π(ℓ - 1))/3`. -/
noncomputable def seedγ (θ₁ θ₂ : ℝ) (ℓ : ℤ) : ℝ := -(θ₁ + θ₂ + 2 * Real.pi * (ℓ - 1)) / 3

/-- `σ = e^{-iβ} + e^{i(β-γ)} + e^{iγ}`. -/
noncomputable def seedσ (θ₁ θ₂ : ℝ) (ℓ : ℤ) : ℂ :=
  Complex.exp ((-seedβ θ₁ θ₂ ℓ : ℝ) * Complex.I) +
    Complex.exp ((seedβ θ₁ θ₂ ℓ - seedγ θ₁ θ₂ ℓ : ℝ) * Complex.I) +
    Complex.exp ((seedγ θ₁ θ₂ ℓ : ℝ) * Complex.I)

/-- The allowed parameters, SM Eq. `triple-parameter-domain`:
`|σ|⁴ + 18|σ|² + 8 Re(σ³) - 27 ≤ 0`. -/
def InDomain (θ₁ θ₂ : ℝ) (ℓ : ℤ) : Prop := domainPoly (seedσ θ₁ θ₂ ℓ) ≤ 0

/-- First row `(1, e^{iβ}, e^{iγ})` of `A`. -/
noncomputable def seedRowA (θ₁ θ₂ : ℝ) (ℓ : ℤ) : I3 → ℂ :=
  ![1, Complex.exp ((seedβ θ₁ θ₂ ℓ : ℝ) * Complex.I), Complex.exp ((seedγ θ₁ θ₂ ℓ : ℝ) * Complex.I)]

/-- `A = [[1, e^{iβ}, e^{iγ}], [e^{iγ}, 1, e^{iβ}], [e^{iβ}, e^{iγ}, 1]]`. -/
noncomputable def seedA (θ₁ θ₂ : ℝ) (ℓ : ℤ) : Mat3 := circM (seedRowA θ₁ θ₂ ℓ)

/-- First row `(1, ρ₁⁻¹, ρ₃)` of `B`. -/
noncomputable def seedRowB (ρ : Fin 3 → ℂ) : I3 → ℂ := ![1, (ρ 0)⁻¹, ρ 2]

/-- `B = [[1, ρ₁⁻¹, ρ₃], [ρ₃, 1, ρ₁⁻¹], [ρ₁⁻¹, ρ₃, 1]]`. -/
noncomputable def seedB (ρ : Fin 3 → ℂ) : Mat3 := circM (seedRowB ρ)

/-- **The seed construction of SM §"Seeds of all mutually unbiased triples"**: for seed
parameters `θ₁, θ₂`, the branch `ℓ`, an ordering `ρ` of the roots of `t³ + σt² - σ̄t - 1` and
signs `ε`, the triple of Methods Eq. `methods-explicit-continuous-bases` with the diagonal
factors `D, R, S` of SM Eq. `triple-diagonal-factors`. -/
noncomputable def seedTriple (θ₁ θ₂ : ℝ) (ℓ : ℤ) (ρ : Fin 3 → ℂ) (ε : I3 → ℤˣ) : Triple :=
  constructTriple (seedA θ₁ θ₂ ℓ) (seedB ρ) ε

lemma normSq_exp_mul_I (x : ℝ) : Complex.normSq (Complex.exp (x * Complex.I)) = 1 := by
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]; norm_num

lemma star_exp_mul_I (x : ℝ) :
    star (Complex.exp (x * Complex.I)) = Complex.exp ((-x : ℝ) * Complex.I) := by
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal]

lemma exp_mul_I_mul (x y : ℝ) :
    Complex.exp (x * Complex.I) * Complex.exp (y * Complex.I) =
      Complex.exp ((x + y : ℝ) * Complex.I) := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma unitVec_seedRowA (θ₁ θ₂ : ℝ) (ℓ : ℤ) : UnitVec (seedRowA θ₁ θ₂ ℓ) := by
  intro t; fin_cases t <;> simp [seedRowA, normSq_exp_mul_I]

/-- `Σₛ a_{s+1} āₛ = σ̄` for the first row of `A`. -/
lemma autoc_seedRowA (θ₁ θ₂ : ℝ) (ℓ : ℤ) : autoc (seedRowA θ₁ θ₂ ℓ) = star (seedσ θ₁ θ₂ ℓ) := by
  simp only [autoc, seedRowA, seedσ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, star_add, star_exp_mul_I,
    star_one, one_mul, mul_one, exp_mul_I_mul]
  rw [neg_neg]
  ring_nf

/-- `Σₛ b_{s+1} b̄ₛ = -σ̄` for the first row of `B` when `ρ` are unit roots. -/
lemma autoc_seedRowB {σ : ℂ} {ρ : Fin 3 → ℂ} (h : IsRootTriple σ ρ)
    (hu : ∀ k, Complex.normSq (ρ k) = 1) : autoc (seedRowB ρ) = -star σ := by
  have h3 := h.prod
  have e0 : (ρ 0)⁻¹ = ρ 1 * ρ 2 := by
    rw [inv_eq_of_mul_eq_one_right (a := ρ 0) (b := ρ 1 * ρ 2) (by rw [← mul_assoc]; exact h3)]
  have e2 : (ρ 2)⁻¹ = ρ 0 * ρ 1 := by
    rw [inv_eq_of_mul_eq_one_right (a := ρ 2) (b := ρ 0 * ρ 1) (by rw [mul_comm]; exact h3)]
  simp only [autoc, seedRowB, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, star_one, one_mul, mul_one, star_inv₀,
    star_eq_inv_of_normSq (hu 0), star_eq_inv_of_normSq (hu 2), inv_inv]
  rw [e0, e2]
  linear_combination h.sum2

lemma unitVec_seedRowB {ρ : Fin 3 → ℂ} (hu : ∀ k, Complex.normSq (ρ k) = 1) :
    UnitVec (seedRowB ρ) := by
  intro t; fin_cases t <;> simp [seedRowB, hu]

/-- **Main theorem of the seed construction** (SM §"Seeds of all mutually unbiased triples").
For every `(θ₁, θ₂, ℓ)` in the domain `|σ|⁴ + 18|σ|² + 8 Re(σ³) - 27 ≤ 0`, every ordering `ρ`
of the roots of `t³ + σt² - σ̄t - 1` and every choice of signs `ε`:
the roots have unit modulus, the Fourier coefficients `λₖ, μₖ` do not vanish, `D, R, S` have
unit entries, the resulting triple is a MUB triple of the explicit family form
(`IsFamilyMember`), its transition is `√6 U₂† U₃ = H = [[A, B], [B†, -A†]]`, and `H` is a
complex Hadamard matrix. -/
theorem seedTriple_spec {θ₁ θ₂ : ℝ} {ℓ : ℤ} {ρ : Fin 3 → ℂ} (hdom : InDomain θ₁ θ₂ ℓ)
    (hρ : IsRootTriple (seedσ θ₁ θ₂ ℓ) ρ) (ε : I3 → ℤˣ) :
    (∀ k, Complex.normSq (ρ k) = 1) ∧
      (∀ k, fcoef (seedA θ₁ θ₂ ℓ) k ≠ 0 ∧ fcoef (seedB ρ) k ≠ 0) ∧
      UnitVec (seedD (seedA θ₁ θ₂ ℓ) (seedB ρ) ε) ∧ UnitVec (seedR (seedA θ₁ θ₂ ℓ) (seedB ρ) ε) ∧
      UnitVec (seedS (seedA θ₁ θ₂ ℓ) (seedB ρ) ε) ∧
      IsFamilyMember (seedTriple θ₁ θ₂ ℓ ρ ε) ∧
      t6 • ((seedTriple θ₁ θ₂ ℓ ρ ε 1)ᴴ * seedTriple θ₁ θ₂ ℓ ρ ε 2) =
        seedH (seedA θ₁ θ₂ ℓ) (seedB ρ) ∧
      Hadamard6.IsHadamard (seedH (seedA θ₁ θ₂ ℓ) (seedB ρ)) := by
  have hu := hρ.normSq_of_domain hdom
  have hab : autoc (seedRowA θ₁ θ₂ ℓ) + autoc (seedRowB ρ) = 0 := by
    rw [autoc_seedRowA, autoc_seedRowB hρ hu]; ring
  exact ⟨hu, construct_spec (unitVec_seedRowA θ₁ θ₂ ℓ) (unitVec_seedRowB hu) hab ε⟩

/-- Every seed triple in the domain is a member of the continuous family. -/
theorem seedTriple_isFamilyMember {θ₁ θ₂ : ℝ} {ℓ : ℤ} {ρ : Fin 3 → ℂ} (hdom : InDomain θ₁ θ₂ ℓ)
    (hρ : IsRootTriple (seedσ θ₁ θ₂ ℓ) ρ) (ε : I3 → ℤˣ) :
    IsFamilyMember (seedTriple θ₁ θ₂ ℓ ρ ε) :=
  (seedTriple_spec hdom hρ ε).2.2.2.2.2.1

/-- **The domain is not empty**: `(θ₁, θ₂, ℓ) = (2π/3, -2π/3, 1)` gives `σ = 0`. -/
theorem seedσ_center : seedσ (2 * Real.pi / 3) (-(2 * Real.pi / 3)) 1 = 0 ∧
    InDomain (2 * Real.pi / 3) (-(2 * Real.pi / 3)) 1 := by
  have hβ : seedβ (2 * Real.pi / 3) (-(2 * Real.pi / 3)) 1 = -(2 * Real.pi / 3) := by
    simp only [seedβ]; push_cast; ring
  have hγ : seedγ (2 * Real.pi / 3) (-(2 * Real.pi / 3)) 1 = 0 := by
    simp only [seedγ]; push_cast; ring
  have hcos : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three]
  have hσ : seedσ (2 * Real.pi / 3) (-(2 * Real.pi / 3)) 1 = 0 := by
    rw [seedσ, hβ, hγ, neg_neg, sub_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
      Complex.exp_mul_I, Complex.exp_mul_I]
    have hc : Complex.cos (2 * (Real.pi : ℂ) / 3) = -(1 / 2) := by
      rw [show 2 * (Real.pi : ℂ) / 3 = ((2 * Real.pi / 3 : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cos, hcos]
      push_cast; ring
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg, hc]
    ring
  refine ⟨hσ, ?_⟩
  rw [InDomain, hσ, domainPoly]; norm_num

/-- Members of the continuous family exist (non-vacuity of `IsFamilyMember`). -/
theorem exists_familyMember : ∃ V, IsFamilyMember V := by
  obtain ⟨ρ, hρ⟩ := exists_isRootTriple (seedσ (2 * Real.pi / 3) (-(2 * Real.pi / 3)) 1)
  exact ⟨_, seedTriple_isFamilyMember seedσ_center.2 hρ (fun _ => 1)⟩

/-! ### Seeds read off the corners -/

/-- Dephased entry `E_{rs} = A_{rs} A_{00} / (A_{r0} A_{0s})` of a `3 × 3` corner. -/
noncomputable def dephase (A : Mat3) (r s : I3) : ℂ := A r s * A 0 0 / (A r 0 * A 0 s)

/-- The four-phase seed `(E₁₁, E₁₂, E₂₁, E₂₂)` of a corner (as unit complex numbers). -/
noncomputable def seedOf (A : Mat3) : Fin 4 → ℂ :=
  ![dephase A 1 1, dephase A 1 2, dephase A 2 1, dephase A 2 2]

lemma exp_mul_I_ne_zero (x : ℝ) : Complex.exp (x * Complex.I) ≠ 0 := Complex.exp_ne_zero _

/-- **The upper-left corner of `H` has the prescribed seed** `(θ₁, θ₂, θ₁ - θ₂, θ₁)`. -/
theorem seedOf_seedA (θ₁ θ₂ : ℝ) (ℓ : ℤ) :
    seedOf (seedA θ₁ θ₂ ℓ) = ![Complex.exp (θ₁ * Complex.I), Complex.exp (θ₂ * Complex.I),
      Complex.exp ((θ₁ - θ₂ : ℝ) * Complex.I), Complex.exp (θ₁ * Complex.I)] := by
  have hβ := exp_mul_I_ne_zero (seedβ θ₁ θ₂ ℓ)
  have hγ := exp_mul_I_ne_zero (seedγ θ₁ θ₂ ℓ)
  -- the three needed exponent identities
  have k1 : Complex.exp (θ₁ * Complex.I) * (Complex.exp ((seedγ θ₁ θ₂ ℓ : ℝ) * Complex.I) *
      Complex.exp ((seedβ θ₁ θ₂ ℓ : ℝ) * Complex.I)) = 1 := by
    rw [exp_mul_I_mul, exp_mul_I_mul, ← Complex.exp_zero]
    congr 1; simp only [seedβ, seedγ]; push_cast; ring
  have per : ∀ (x : ℝ) (n : ℤ), Complex.exp ((x + 2 * Real.pi * n : ℝ) * Complex.I) =
      Complex.exp (x * Complex.I) := by
    intro x n
    rw [← mul_one (Complex.exp (x * Complex.I)), ← Complex.exp_int_mul_two_pi_mul_I n,
      ← Complex.exp_add]
    congr 1; push_cast; ring
  have k2 : Complex.exp (θ₂ * Complex.I) * (Complex.exp ((seedγ θ₁ θ₂ ℓ : ℝ) * Complex.I) *
      Complex.exp ((seedγ θ₁ θ₂ ℓ : ℝ) * Complex.I)) =
      Complex.exp ((seedβ θ₁ θ₂ ℓ : ℝ) * Complex.I) := by
    rw [exp_mul_I_mul, exp_mul_I_mul, ← per _ (ℓ - 1)]
    congr 2; simp only [seedβ, seedγ]; push_cast; ring
  have k3 : Complex.exp ((θ₁ - θ₂ : ℝ) * Complex.I) * (Complex.exp ((seedβ θ₁ θ₂ ℓ : ℝ) *
      Complex.I) * Complex.exp ((seedβ θ₁ θ₂ ℓ : ℝ) * Complex.I)) =
      Complex.exp ((seedγ θ₁ θ₂ ℓ : ℝ) * Complex.I) := by
    rw [exp_mul_I_mul, exp_mul_I_mul, ← per _ (-(ℓ - 1))]
    congr 2; simp only [seedβ, seedγ]; push_cast; ring
  have ev : ∀ r c : I3, seedA θ₁ θ₂ ℓ r c = seedRowA θ₁ θ₂ ℓ (c - r) := fun _ _ => rfl
  have a0 : seedRowA θ₁ θ₂ ℓ 0 = 1 := rfl
  have a1 : seedRowA θ₁ θ₂ ℓ 1 = Complex.exp ((seedβ θ₁ θ₂ ℓ : ℝ) * Complex.I) := rfl
  have a2 : seedRowA θ₁ θ₂ ℓ 2 = Complex.exp ((seedγ θ₁ θ₂ ℓ : ℝ) * Complex.I) := rfl
  funext i
  fin_cases i <;>
    simp only [seedOf, dephase, ev, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Matrix.cons_val_three, sub_self, sub_zero, zero_sub, I3_neg_one,
      I3_neg_two, show (2 : I3) - 1 = 1 from rfl, show (1 : I3) - 2 = 2 from rfl, a0, a1, a2,
      mul_one]
  · rw [div_eq_iff (mul_ne_zero hγ hβ)]; linear_combination -k1
  · rw [div_eq_iff (mul_ne_zero hγ hγ)]; linear_combination -k2
  · rw [div_eq_iff (mul_ne_zero hβ hβ)]; linear_combination -k3
  · rw [div_eq_iff (mul_ne_zero hβ hγ)]; linear_combination -k1

/-- The transition `√6 U₂† U₃` of a seed triple has upper-left corner with seed
`(θ₁, θ₂, θ₁ - θ₂, θ₁)` (SM: "whose upper-left corner has the prescribed seed"). -/
theorem seedOf_seedTriple_corner {θ₁ θ₂ : ℝ} {ℓ : ℤ} {ρ : Fin 3 → ℂ} (hdom : InDomain θ₁ θ₂ ℓ)
    (hρ : IsRootTriple (seedσ θ₁ θ₂ ℓ) ρ) (ε : I3 → ℤˣ) :
    seedOf (t6 • ((seedTriple θ₁ θ₂ ℓ ρ ε 1)ᴴ * seedTriple θ₁ θ₂ ℓ ρ ε 2)).toBlocks₁₁ =
      ![Complex.exp (θ₁ * Complex.I), Complex.exp (θ₂ * Complex.I),
        Complex.exp ((θ₁ - θ₂ : ℝ) * Complex.I), Complex.exp (θ₁ * Complex.I)] := by
  rw [(seedTriple_spec hdom hρ ε).2.2.2.2.2.2.1, seedH, toBlocks_fromBlocks₁₁, seedOf_seedA]

/-- Rows `(1, 4, 2)` and columns `(1, 2, 3)` of a `6 × 6` matrix. -/
def corner142 (M : Mat6) : Mat3 :=
  Matrix.of fun i j => M (![Sum.inl 0, Sum.inr 0, Sum.inl 1] i) (Sum.inl j)

/-- **The second specified corner** (SM: "The second specified corner has seed
`(θ'₁, θ'₂, -2π/3, 2π/3)`"): rows `(1, 4, 2)` and columns `(1, 2, 3)` of `√6 U₃†` have
seed `(R₂₂S₂₂D₁₁/(R₁₁S₁₁D₂₂), R₃₃S₃₃D₁₁/(R₁₁S₁₁D₃₃), ω², ω)` for any unit `D, R, S`
(`ω² = e^{-2πi/3}`, `ω = e^{2πi/3}`; `θ'ᵢ` is the argument of the first two entries). -/
theorem seedOf_corner142 {d r s : I3 → ℂ} (hd : UnitVec d) (hr : UnitVec r) (hs : UnitVec s) :
    seedOf (corner142 (t6 • (familyTriple d r s 2)ᴴ)) =
      ![r 1 * s 1 * d 0 / (r 0 * s 0 * d 1), r 2 * s 2 * d 0 / (r 0 * s 0 * d 2), ω ^ 2, ω] := by
  have hc : t6 • (familyTriple d r s 2)ᴴ = (famK d r s)ᴴ := by
    rw [familyTriple, std_two, conjTranspose_smul, s6_star, smul_smul, mul_comm t6 s6, s6_mul_t6,
      one_smul]
  have hd' := fun t => ne_zero_of_normSq (hd t)
  have hr' := fun t => ne_zero_of_normSq (hr t)
  have hs' := fun t => ne_zero_of_normSq (hs t)
  have cd : ∀ t, (starRingEnd ℂ) (d t) = (d t)⁻¹ := fun t => star_eq_inv_of_normSq (hd t)
  have cr : ∀ t, (starRingEnd ℂ) (r t) = (r t)⁻¹ := fun t => star_eq_inv_of_normSq (hr t)
  have cs : ∀ t, (starRingEnd ℂ) (s t) = (s t)⁻¹ := fun t => star_eq_inv_of_normSq (hs t)
  have := hr' 0; have := hr' 1; have := hr' 2; have := hs' 0; have := hs' 1; have := hs' 2
  have := hd' 0; have := hd' 1; have := hd' 2
  rw [hc]
  funext i
  fin_cases i <;>
    simp [seedOf, dephase, corner142, famK, diagonal_mul, cd, cr, cs, conj_ω] <;>
    field_simp <;> ω_norm

/-! ### The allowed parameters are exactly the domain -/

/-- Unitarity of `[[A, B], [B†, -A†]]` forces the autocorrelations to cancel. -/
lemma autoc_add_of_hadamard {a b : I3 → ℂ} (h : Hadamard6.IsHadamard (seedH (circM a) (circM b))) :
    autoc a + autoc b = 0 := by
  have := congrArg (fun M => M (Sum.inl 0) (Sum.inl 1)) h.2
  simp [seedH, Matrix.mul_apply] at this
  rw [Fin.sum_univ_three, Fin.sum_univ_three] at this
  simp only [Fin.isValue, zero_sub, I3_neg_one, show (1 : I3) - 1 = 0 from rfl,
    show (2 : I3) - 1 = 1 from rfl] at this
  simp only [autoc, Complex.star_def]
  linear_combination this

lemma unitVec_of_hadamard_circM {a b : I3 → ℂ}
    (h : Hadamard6.IsHadamard (seedH (circM a) (circM b))) : UnitVec a ∧ UnitVec b := by
  refine ⟨fun e => ?_, fun e => ?_⟩
  · have := h.1 (Sum.inl 0) (Sum.inl e); simpa [seedH] using this
  · have := h.1 (Sum.inl 0) (Sum.inr e); simpa [seedH] using this

/-- From a unit first row `b = (1, b₁, b₂)` with `Σ b_{s+1} b̄ₛ = -σ̄`, the roots
`(b₁⁻¹, b₁ b₂⁻¹, b₂)` of the cubic (unit modulus), and `seedRowB` of them is `b`. -/
lemma rootTriple_of_row {σ : ℂ} {b : I3 → ℂ} (hb : UnitVec b) (hb0 : b 0 = 1)
    (hσ : autoc b = -star σ) :
    IsRootTriple σ ![(b 1)⁻¹, b 1 * (b 2)⁻¹, b 2] ∧
      (∀ k, Complex.normSq (![(b 1)⁻¹, b 1 * (b 2)⁻¹, b 2] k) = 1) ∧
      seedRowB ![(b 1)⁻¹, b 1 * (b 2)⁻¹, b 2] = b := by
  have h1 := ne_zero_of_normSq (hb 1)
  have h2 := ne_zero_of_normSq (hb 2)
  have s1 := star_eq_inv_of_normSq (hb 1)
  have s2 := star_eq_inv_of_normSq (hb 2)
  have hσ' : b 1 + (b 1)⁻¹ * b 2 + (b 2)⁻¹ = -star σ := by
    rw [← hσ]; simp only [autoc, hb0, star_one, one_mul, mul_one, s1, s2]
  refine ⟨isRootTriple_of_vieta ?_ ?_ ?_, fun k => ?_, ?_⟩
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    have := congrArg star hσ'
    simp only [star_add, star_mul', star_inv₀, s1, s2, inv_inv, star_neg, star_star] at this
    linear_combination this
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [← hσ']; field_simp; ring
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    field_simp
  · fin_cases k <;> simp [Complex.normSq_mul, hb 1, hb 2]
  · funext e; fin_cases e <;> simp [seedRowB, hb0]

/-- **The allowed parameters are exactly the domain** (SM: "The allowed parameter pairs are
exactly those satisfying Eq. `triple-parameter-domain`"): `(θ₁, θ₂, ℓ)` satisfies the domain
inequality iff some circulant `B` with first entry `1` makes `[[A, B], [B†, -A†]]` a complex
Hadamard matrix, iff the roots of `t³ + σt² - σ̄t - 1` all have unit modulus. -/
theorem inDomain_iff (θ₁ θ₂ : ℝ) (ℓ : ℤ) :
    (InDomain θ₁ θ₂ ℓ ↔ ∃ ρ : Fin 3 → ℂ, IsRootTriple (seedσ θ₁ θ₂ ℓ) ρ ∧
        ∀ k, Complex.normSq (ρ k) = 1) ∧
      (InDomain θ₁ θ₂ ℓ ↔ ∃ b : I3 → ℂ, b 0 = 1 ∧
        Hadamard6.IsHadamard (seedH (seedA θ₁ θ₂ ℓ) (circM b))) := by
  refine ⟨domainPoly_nonpos_iff _, ⟨fun hdom => ?_, fun ⟨b, hb0, hH⟩ => ?_⟩⟩
  · obtain ⟨ρ, hρ⟩ := exists_isRootTriple (seedσ θ₁ θ₂ ℓ)
    exact ⟨seedRowB ρ, rfl, (seedTriple_spec hdom hρ (fun _ => 1)).2.2.2.2.2.2.2⟩
  · have hab := autoc_add_of_hadamard hH
    have hb := (unitVec_of_hadamard_circM hH).2
    rw [autoc_seedRowA] at hab
    obtain ⟨hρ, hu, -⟩ := rootTriple_of_row hb hb0 (σ := seedσ θ₁ θ₂ ℓ)
      (by linear_combination hab)
    exact domainPoly_nonpos_of_unit hρ hu

/-! ### Every family member is equivalent to a seed triple -/

/-- `F₃ᴴ diag(x) F₃` is the circulant with its own first row. -/
lemma circ_eq_circM (x : I3 → ℂ) : circ x = circM (fun e => circ x 0 e) := by
  ext s s'
  rw [circM_apply, circ_apply, circ_apply]
  simp only [Fin.sum_univ_three]
  fin_cases s <;> fin_cases s' <;> simp [I3_neg_one, I3_neg_two] <;> ω_norm

/-- First row of the unimodular circulant `F₃ᴴ diag(x) F₃ / √6`. -/
noncomputable def rowOf (x : I3 → ℂ) : I3 → ℂ := fun e => s6 * circ x 0 e

lemma circM_rowOf (x : I3 → ℂ) : circM (rowOf x) = s6 • circ x := by
  conv_rhs => rw [circ_eq_circM x]
  ext r c; simp [rowOf]

lemma rowOf_smul (c : ℂ) (x : I3 → ℂ) : rowOf (c • x) = c • rowOf x := by
  funext e; simp only [rowOf, circ_smul, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply]; ring

lemma fcoef_circM_rowOf (x : I3 → ℂ) (k : I3) : fcoef (circM (rowOf x)) k = x k / 2 := by
  rw [circM_rowOf, fcoef_smul_circ]
  have := s6_mul_s6
  linear_combination (3 * x k) * this

/-- The transition `√6 U₂† U₃` of an explicit family triple is `[[A, B], [B†, -A†]]` with the
circulants `A = F₃ᴴ(R + S)F₃/√6`, `B = F₃ᴴ D(R̄ - S̄)F₃/√6`. -/
lemma familyTriple_transition_seedH {d r s : I3 → ℂ} (hd : UnitVec d) (hr : UnitVec r)
    (hs : UnitVec s) :
    t6 • ((familyTriple d r s 1)ᴴ * familyTriple d r s 2) =
      seedH (circM (rowOf (r + s))) (circM (rowOf (d * (star r - star s)))) := by
  rw [familyTriple_transition hd hr hs, seedH, circM_rowOf, circM_rowOf, conjTranspose_smul,
    conjTranspose_smul, s6_star, circ_neg, ← circ_conjTranspose, ← circ_conjTranspose,
    fromBlocks_smul, smul_neg]

/-- The transition between the second and third basis of a MUB triple is Hadamard. -/
lemma transition_isHadamard {U : Triple} (hT : IsMUBTriple U) :
    Hadamard6.IsHadamard (t6 • ((U 1)ᴴ * U 2)) := by
  have hX : IsUnitary ((U 1)ᴴ * U 2) := (hT.1 1).conjTranspose.mul (hT.1 2)
  refine ⟨fun i j => ?_, ?_⟩
  · rw [Matrix.smul_apply, smul_eq_mul, Complex.normSq_mul, normSq_t6, hT.2 1 2 (by decide) i j]
    norm_num
  · rw [conjTranspose_smul, t6_star, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hX.1,
      t6_mul_t6]

/-- Seed angles for a unit first row `(1, a₁, a₂)`: `θ₁ = -β - γ`, `θ₂ = β - 2γ`, `ℓ = 1`. -/
lemma exists_seed_angles {a : I3 → ℂ} (ha : UnitVec a) (ha0 : a 0 = 1) :
    ∃ θ₁ θ₂ : ℝ, seedRowA θ₁ θ₂ 1 = a := by
  have harg : ∀ t, Complex.exp ((Complex.arg (a t) : ℝ) * Complex.I) = a t := by
    intro t
    have h1 : ‖a t‖ = 1 := by
      have := ha t; rw [Complex.normSq_eq_norm_sq] at this
      nlinarith [norm_nonneg (a t)]
    have := Complex.norm_mul_exp_arg_mul_I (a t)
    rwa [h1, Complex.ofReal_one, one_mul] at this
  set β := Complex.arg (a 1)
  set γ := Complex.arg (a 2)
  refine ⟨-β - γ, β - 2 * γ, ?_⟩
  have hβ : seedβ (-β - γ) (β - 2 * γ) 1 = β := by simp only [seedβ]; push_cast; ring
  have hγ : seedγ (-β - γ) (β - 2 * γ) 1 = γ := by simp only [seedγ]; push_cast; ring
  funext e
  fin_cases e
  · simp [seedRowA, ha0]
  · simp only [seedRowA, hβ]; exact harg 1
  · simp only [seedRowA, hγ]; exact harg 2

/-- The phase choice of `D`: for `c ≠ 0` real and `ε = -sign c`, `i ε (d i c/2)/|d i c/2| = d`. -/
lemma phase_choice {d : ℂ} (hd : Complex.normSq d = 1) {c : ℝ} (hc : c ≠ 0) :
    Complex.I * (((if 0 < c then (-1 : ℤˣ) else 1 : ℤˣ) : ℤ) : ℂ) *
        (d * Complex.I * ((c / 2 : ℝ) : ℂ)) / ((‖d * Complex.I * ((c / 2 : ℝ) : ℂ)‖ : ℝ) : ℂ) =
      d := by
  have hnd : ‖d‖ = 1 := by
    have := hd; rw [Complex.normSq_eq_norm_sq] at this; nlinarith [norm_nonneg d]
  rw [norm_mul, norm_mul, hnd, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
  rcases lt_or_gt_of_ne hc with h | h
  · rw [if_neg (not_lt.2 h.le), abs_of_neg (by linarith)]
    have : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    push_cast
    field_simp
    rw [Complex.I_sq]; ring
  · rw [if_pos h, abs_of_pos (by linarith)]
    have : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    push_cast
    field_simp
    rw [Complex.I_sq]; ring

/-- A family triple whose two circulant first rows start with `1` *is* a seed triple. -/
theorem normalized_family_eq_seedTriple {d r s : I3 → ℂ} (hd : UnitVec d) (hr : UnitVec r)
    (hs : UnitVec s) (hT : IsMUBTriple (familyTriple d r s)) (ha0 : rowOf (r + s) 0 = 1)
    (hb0 : rowOf (d * (star r - star s)) 0 = 1) :
    ∃ (θ₁ θ₂ : ℝ) (ρ : Fin 3 → ℂ) (ε : I3 → ℤˣ), InDomain θ₁ θ₂ 1 ∧
      IsRootTriple (seedσ θ₁ θ₂ 1) ρ ∧ familyTriple d r s = seedTriple θ₁ θ₂ 1 ρ ε := by
  have hH0 := transition_isHadamard hT
  rw [familyTriple_transition_seedH hd hr hs] at hH0
  have hlam0 := fcoef_circM_rowOf (r + s)
  have hmu0 := fcoef_circM_rowOf (d * (star r - star s))
  generalize hadef : rowOf (r + s) = a at ha0 hH0 hlam0
  generalize hbdef : rowOf (d * (star r - star s)) = b at hb0 hH0 hmu0
  have hH : Hadamard6.IsHadamard (seedH (circM a) (circM b)) := hH0
  have hab := autoc_add_of_hadamard hH
  obtain ⟨ha, hb⟩ := unitVec_of_hadamard_circM hH
  obtain ⟨θ₁, θ₂, hθ⟩ := exists_seed_angles ha ha0
  have hσ : autoc b = -star (seedσ θ₁ θ₂ 1) := by
    rw [← autoc_seedRowA, hθ]; linear_combination hab
  obtain ⟨hρ, hu, hB⟩ := rootTriple_of_row hb hb0 hσ
  set ρ := ![(b 1)⁻¹, b 1 * (b 2)⁻¹, b 2]
  have hA : seedA θ₁ θ₂ 1 = circM a := by rw [seedA, hθ]
  have hB' : seedB ρ = circM b := by rw [seedB, hB]
  -- the Fourier coefficients
  have hlam : ∀ k, fcoef (circM a) k = (r k + s k) / 2 := fun k => hlam0 k
  have hmu : ∀ k, fcoef (circM b) k = d k * (star (r k) - star (s k)) / 2 := fun k => hmu0 k
  have hba : autoc b + autoc a = 0 := by rw [add_comm]; exact hab
  -- `λμ = d i Im(s r̄)/2`
  have hprod : ∀ k, fcoef (circM a) k * fcoef (circM b) k =
      d k * Complex.I * (((s k * star (r k)).im / 2 : ℝ) : ℂ) := by
    intro k
    rw [hlam, hmu]
    have h1 := mul_star_self_of_normSq (hr k)
    have h2 := mul_star_self_of_normSq (hs k)
    have him : (((s k * star (r k)).im : ℝ) : ℂ) * Complex.I * 2 =
        s k * star (r k) - star (s k * star (r k)) := by
      rw [show star (s k * star (r k)) = (starRingEnd ℂ) (s k * star (r k)) from rfl,
        Complex.sub_conj]; push_cast; ring
    push_cast
    rw [star_mul', star_star] at him
    linear_combination (d k / 4) * h1 - (d k / 4) * h2 + (-(d k / 4)) * him
  have hc : ∀ k, (s k * star (r k)).im ≠ 0 := by
    intro k h0
    have := mul_ne_zero (fcoef_ne_zero ha hb hab k) (fcoef_ne_zero hb ha hba k)
    rw [hprod k, h0, zero_div, Complex.ofReal_zero, mul_zero] at this
    exact this rfl
  set ε : I3 → ℤˣ := fun k => if 0 < (s k * star (r k)).im then -1 else 1 with hεdef
  have hD : seedD (circM a) (circM b) ε = d := by
    funext k
    rw [seedD, hprod k]
    have := phase_choice (hd k) (c := (s k * star (r k)).im) (hc k)
    rwa [hεdef]
  have hR : seedR (circM a) (circM b) ε = r := by
    funext k
    rw [seedR, hD, hlam, hmu]
    have h0 := mul_star_self_of_normSq (hd k)
    simp only [star_div₀, star_mul', star_sub, star_star]
    have : star (2 : ℂ) = 2 := by simp
    rw [this]
    linear_combination ((r k - s k) / 2) * h0
  have hS : seedS (circM a) (circM b) ε = s := by
    funext k
    rw [seedS, hD, hlam, hmu]
    have h0 := mul_star_self_of_normSq (hd k)
    simp only [star_div₀, star_mul', star_sub, star_star]
    have : star (2 : ℂ) = 2 := by simp
    rw [this]
    linear_combination (-(r k - s k) / 2) * h0
  refine ⟨θ₁, θ₂, ρ, ε, domainPoly_nonpos_of_unit hρ hu, hρ, ?_⟩
  rw [seedTriple, hA, hB', constructTriple, hD, hR, hS]

/-- Rescaling: `(D, R, S) ↦ (l κ² D, κ R, κ S)` is a triple equivalence (column phases on the
second orbit of `U₂` and on both orbits of `U₃`). -/
theorem familyTriple_rescale (d r s : I3 → ℂ) {κ l : ℂ} (hκ : Complex.normSq κ = 1)
    (hl : Complex.normSq l = 1) :
    TripleEquiv (familyTriple d r s)
      (familyTriple (fun t => l * κ ^ 2 * d t) (fun t => κ * r t) (fun t => κ * s t)) := by
  have hκκ := mul_star_self_of_normSq hκ
  have hlκ : Complex.normSq (l * κ ^ 2) = 1 := by
    rw [Complex.normSq_mul, map_pow, hκ, hl]; norm_num
  have hκl : Complex.normSq (κ * l) = 1 := by rw [Complex.normSq_mul, hκ, hl]; norm_num
  have hE1 := tripleEquiv_std_colH (H := symH d) (K := famK d r s) (isMonomial_colOpH 0 hlκ)
  rw [symH_mul_colOpH] at hE1
  have hE2 := tripleEquiv_std_colK
    (H := symH (fun t => l * κ ^ 2 * ω ^ (t.val * (0 : I3).val) * d t)) (K := famK d r s)
    (isMonomial_colOpK 0 0 hκ hκl)
  have hK : famK d r s * colOpK 0 0 κ (κ * l) =
      famK (fun t => l * κ ^ 2 * d t) (fun t => κ * r t) (fun t => κ * s t) := by
    ext i j
    rw [colOpK, mul_monomial_apply]
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [famK, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
        fromBlocks_apply₂₂, Matrix.neg_apply, diagonal_mul, F3_apply, Pi.mul_apply,
        Pi.star_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.coe_addRight,
        add_zero, Sum.elim_inl, Sum.elim_inr, star_mul']
    · ring
    · linear_combination (κ * l * d i * star (s i) * ω ^ (i.val * j.val)) * hκκ
    · ring
    · linear_combination (-(κ * l * d i * star (r i) * ω ^ (i.val * j.val))) * hκκ
  rw [hK] at hE2
  have hx : (fun t : I3 => l * κ ^ 2 * ω ^ (t.val * (0 : I3).val) * d t) =
      fun t => l * κ ^ 2 * d t := by funext t; simp
  rw [hx] at hE1 hE2
  exact tripleEquiv_trans hE1 hE2

lemma rescale_y (d r s : I3 → ℂ) {κ : ℂ} (hκ : Complex.normSq κ = 1) (l : ℂ) :
    ((fun t => l * κ ^ 2 * d t) * (star (fun t => κ * r t) - star fun t => κ * s t)) =
      (l * κ) • (d * (star r - star s)) := by
  have hκκ := mul_star_self_of_normSq hκ
  funext t
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul']
  linear_combination (l * κ * d t * (star (r t) - star (s t))) * hκκ

/-- **Every family member is equivalent to a seed triple** (identification of `IsFamilyMember`
with the paper's `(θ₁, θ₂)` parametrization, converse direction): after the rescaling
`(D, R, S) ↦ (l κ² D, κ R, κ S)` the two circulant first rows start with `1`, and then the
explicit family triple *is* the seed triple for `ℓ = 1`, suitable `θ₁, θ₂`, the root ordering
`ρ = (b₁⁻¹, b₁ b₂⁻¹, b₂)` and the signs `εₖ = -sign Im(Sₖ R̄ₖ)`. -/
theorem familyMember_tripleEquiv_seedTriple {V : Triple} (hV : IsFamilyMember V) :
    ∃ (θ₁ θ₂ : ℝ) (ρ : Fin 3 → ℂ) (ε : I3 → ℤˣ), InDomain θ₁ θ₂ 1 ∧
      IsRootTriple (seedσ θ₁ θ₂ 1) ρ ∧ TripleEquiv V (seedTriple θ₁ θ₂ 1 ρ ε) := by
  obtain ⟨d, r, s, hd, hr, hs, rfl, hT⟩ := hV
  have hH := transition_isHadamard hT
  rw [familyTriple_transition_seedH hd hr hs] at hH
  obtain ⟨ha, hb⟩ := unitVec_of_hadamard_circM hH
  set a0 := rowOf (r + s) 0 with ha0def
  set b0 := rowOf (d * (star r - star s)) 0 with hb0def
  have hκ : Complex.normSq (star a0) = 1 := by rw [normSq_star]; exact ha 0
  have hl : Complex.normSq (star (star a0 * b0)) = 1 := by
    rw [normSq_star, Complex.normSq_mul, hκ, hb 0, one_mul]
  have hE := familyTriple_rescale d r s hκ hl
  have hT' := isMUBTriple_of_tripleEquiv hE hT
  have hκκ := mul_star_self_of_normSq hκ
  have hd' : UnitVec (fun t => star (star a0 * b0) * star a0 ^ 2 * d t) := by
    intro t; rw [Complex.normSq_mul, Complex.normSq_mul, hl, map_pow, hκ, hd t]; norm_num
  have hr' : UnitVec (fun t => star a0 * r t) := by
    intro t; rw [Complex.normSq_mul, hκ, hr t, one_mul]
  have hs' : UnitVec (fun t => star a0 * s t) := by
    intro t; rw [Complex.normSq_mul, hκ, hs t, one_mul]
  have ha0 : rowOf ((fun t => star a0 * r t) + fun t => star a0 * s t) 0 = 1 := by
    have : ((fun t => star a0 * r t) + fun t => star a0 * s t) = star a0 • (r + s) := by
      funext t; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [this, rowOf_smul, Pi.smul_apply, smul_eq_mul, ← ha0def]
    exact star_mul_self_of_normSq (ha 0)
  have hb0 : rowOf ((fun t => star (star a0 * b0) * star a0 ^ 2 * d t) *
      (star (fun t => star a0 * r t) - star fun t => star a0 * s t)) 0 = 1 := by
    rw [rescale_y d r s hκ, rowOf_smul, Pi.smul_apply, smul_eq_mul, ← hb0def]
    have := star_mul_self_of_normSq hl
    rw [star_star] at this
    linear_combination this
  obtain ⟨θ₁, θ₂, ρ, ε, hdom, hρ, heq⟩ :=
    normalized_family_eq_seedTriple hd' hr' hs' hT' ha0 hb0
  exact ⟨θ₁, θ₂, ρ, ε, hdom, hρ, heq ▸ hE⟩

/-- **The continuous family equals the image of the seed construction**, up to equivalence:
a triple is equivalent to a member of the explicit family (`IsFamilyMember`) iff it is
equivalent to a seed triple with parameters in the domain. -/
theorem exists_familyMember_iff_seed (U : Triple) :
    (∃ V, IsFamilyMember V ∧ TripleEquiv U V) ↔
      ∃ (θ₁ θ₂ : ℝ) (ℓ : ℤ) (ρ : Fin 3 → ℂ) (ε : I3 → ℤˣ), InDomain θ₁ θ₂ ℓ ∧
        IsRootTriple (seedσ θ₁ θ₂ ℓ) ρ ∧ TripleEquiv U (seedTriple θ₁ θ₂ ℓ ρ ε) := by
  constructor
  · rintro ⟨V, hV, hUV⟩
    obtain ⟨θ₁, θ₂, ρ, ε, hdom, hρ, hE⟩ := familyMember_tripleEquiv_seedTriple hV
    exact ⟨θ₁, θ₂, 1, ρ, ε, hdom, hρ, tripleEquiv_trans hUV hE⟩
  · rintro ⟨θ₁, θ₂, ℓ, ρ, ε, hdom, hρ, hE⟩
    exact ⟨_, seedTriple_isFamilyMember hdom hρ ε, hE⟩

end MUBTriples
