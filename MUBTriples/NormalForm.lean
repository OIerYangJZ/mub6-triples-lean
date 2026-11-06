import MUBTriples.Basic

/-!
# The cubic root of unity, the `3 × 3` Fourier matrix and the symmetric normal form

`ω = e^{2πi/3}` and the *unnormalized* Fourier matrix `F3 i j = ω^(i j)`.

The symmetric normal form (SM Eq. `tc-cyclic-coordinates`) is written with
rows ordered `(a, t) ↦ Sum.elim` (`a = 0 ↦ inl t`, `a = 1 ↦ inr t`) and columns
`(b, s)` likewise, so that `H_{ta,sb} = ω^{ts} (-1)^{ab} x_t^b` becomes

`symH x = [[F3, X F3], [F3, -X F3]]`,

and `K_{ta,sb} = ω^{ts} (-1)^{ab} y_t^b (u_t or v_t)` becomes

`symK y u v = [[U F3, U Y F3], [V F3, -V Y F3]]`

(capital letters = diagonal matrices).  With this ordering the order-three
symmetry is `T = diag(1, ω, ω², 1, ω, ω²)`.
-/

open Matrix Hadamard6

namespace MUBTriples

/-! ### `ω` -/

/-- The primitive cubic root of unity `e^{2πi/3}` (same as `Hadamard6.standardOmega`). -/
noncomputable def ω : ℂ := ⟨-(1 / 2 : ℝ), Real.sqrt 3 / 2⟩

lemma sqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

lemma sqrt3_pow_three : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by
  rw [pow_succ, sqrt3_sq]
lemma sqrt3_pow_four : Real.sqrt 3 ^ 4 = 9 := by
  rw [show 4 = 2 * 2 by rfl, pow_mul, sqrt3_sq]; norm_num
lemma sqrt3_pow_five : Real.sqrt 3 ^ 5 = 9 * Real.sqrt 3 := by
  rw [pow_succ, sqrt3_pow_four]
lemma sqrt3_pow_six : Real.sqrt 3 ^ 6 = 27 := by
  rw [show 6 = 2 * 3 by rfl, pow_mul, sqrt3_sq]; norm_num

@[simp] lemma ω_re : ω.re = -(1 / 2) := rfl
@[simp] lemma ω_im : ω.im = Real.sqrt 3 / 2 := rfl

lemma ω_sq_add : ω ^ 2 + ω + 1 = 0 := by
  apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im] <;> nlinarith [sqrt3_sq]

lemma ω_sq : ω ^ 2 = -1 - ω := by linear_combination ω_sq_add

lemma ω_cube : ω ^ 3 = 1 := by linear_combination (ω - 1) * ω_sq_add

lemma normSq_ω : Complex.normSq ω = 1 := by
  rw [Complex.normSq_apply]; simp; nlinarith [sqrt3_sq]

lemma star_ω : star ω = ω ^ 2 := by
  apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im] <;> nlinarith [sqrt3_sq]

lemma ω_ne_zero : ω ≠ 0 := by
  intro h; have := normSq_ω; rw [h] at this; simp at this

lemma ω_pow_mod (n : ℕ) : ω ^ n = ω ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, ω_cube, one_pow, one_mul]

lemma normSq_ω_pow (n : ℕ) : Complex.normSq (ω ^ n) = 1 := by
  rw [map_pow, normSq_ω, one_pow]

lemma ω_pow_reduce (n : ℕ) (h : 3 ≤ n) : ω ^ n = ω ^ (n - 3) := by
  conv_lhs => rw [show n = (n - 3) + 3 by omega, pow_add, ω_cube, mul_one]

lemma star_ω_pow (n : ℕ) : star (ω ^ n) = ω ^ (2 * n) := by
  rw [star_pow, star_ω, ← pow_mul]

/-- `|a + b ω|² = a² - a b + b²` for real `a, b`. -/
lemma normSq_add_mul_ω (a b : ℝ) :
    Complex.normSq ((a : ℂ) + (b : ℂ) * ω) = a ^ 2 - a * b + b ^ 2 := by
  rw [Complex.normSq_apply]; simp; nlinarith [sqrt3_sq]

/-! ### The Fourier matrix `F3` -/

/-- The unnormalized `3 × 3` Fourier matrix `F3 i j = ω^(i j)`. -/
noncomputable def F3 : Mat3 := Matrix.of fun i j => ω ^ (i.val * j.val)

@[simp] lemma F3_apply (i j : I3) : F3 i j = ω ^ (i.val * j.val) := rfl

lemma F3_mul_conjTranspose : F3 * F3ᴴ = (3 : ℂ) • (1 : Mat3) := by
  ext i j
  simp only [Matrix.mul_apply, conjTranspose_apply, F3_apply, star_ω_pow, ← pow_add,
    Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;>
    simp [ω_pow_reduce] <;>
    first | linear_combination ω_sq_add | norm_num

lemma conjTranspose_F3_mul : F3ᴴ * F3 = (3 : ℂ) • (1 : Mat3) := by
  have h : ((3 : ℂ)⁻¹ • F3ᴴ) * F3 = 1 := by
    rw [mul_eq_one_comm, Matrix.mul_smul, F3_mul_conjTranspose, smul_smul]; norm_num
  have h2 : F3ᴴ * F3 = (3 : ℂ) • (((3 : ℂ)⁻¹ • F3ᴴ) * F3) := by
    rw [Matrix.smul_mul, smul_smul]; norm_num
  rw [h2, h]

/-- `circ d = F3ᴴ * diag d * F3`, a circulant matrix (`(circ d) s s' = Σₜ dₜ ω^{t(s'-s)}`). -/
noncomputable def circ (d : I3 → ℂ) : Mat3 := F3ᴴ * diagonal d * F3

/-- Flatness of the circulant `F3ᴴ diag(d) F3`: every entry has modulus `√6`. -/
def Flat (d : I3 → ℂ) : Prop := ∀ s s', Complex.normSq (circ d s s') = 6

/-- Unit-modulus vectors. -/
def UnitVec (x : I3 → ℂ) : Prop := ∀ t, Complex.normSq (x t) = 1

lemma diagonal_mul_star {x : I3 → ℂ} (hx : UnitVec x) :
    diagonal x * diagonal (star x) = (1 : Mat3) := by
  rw [diagonal_mul_diagonal]
  have : (fun t => x t * star x t) = fun _ => (1 : ℂ) := by
    funext t; exact mul_star_self_of_normSq (hx t)
  rw [this]; rfl

lemma diagonal_star_mul {x : I3 → ℂ} (hx : UnitVec x) :
    diagonal (star x) * diagonal x = (1 : Mat3) := by
  rw [diagonal_mul_diagonal]
  have : (fun t => star x t * x t) = fun _ => (1 : ℂ) := by
    funext t; exact star_mul_self_of_normSq (hx t)
  rw [this]; rfl

lemma diagF3_gram {x : I3 → ℂ} (hx : UnitVec x) :
    (diagonal x * F3) * (diagonal x * F3)ᴴ = (3 : ℂ) • (1 : Mat3) := by
  rw [conjTranspose_mul, diagonal_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc F3,
    F3_mul_conjTranspose, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
    diagonal_mul_star hx]

lemma diagF3_entry {x : I3 → ℂ} (hx : UnitVec x) (i j : I3) :
    Complex.normSq ((diagonal x * F3) i j) = 1 := by
  rw [diagonal_mul, F3_apply, Complex.normSq_mul, hx i, normSq_ω_pow, one_mul]

/-! ### The symmetric normal form -/

/-- `symH x = [[F3, X F3], [F3, -X F3]]`. -/
noncomputable def symH (x : I3 → ℂ) : Mat6 :=
  fromBlocks F3 (diagonal x * F3) F3 (-(diagonal x * F3))

/-- `symK y u v = [[U F3, U Y F3], [V F3, -V Y F3]]`. -/
noncomputable def symK (y u v : I3 → ℂ) : Mat6 :=
  fromBlocks (diagonal u * F3) (diagonal (u * y) * F3) (diagonal v * F3)
    (-(diagonal (v * y) * F3))

lemma UnitVec.mul {x y : I3 → ℂ} (hx : UnitVec x) (hy : UnitVec y) : UnitVec (x * y) := by
  intro t; simp [Complex.normSq_mul, hx t, hy t]

lemma UnitVec.star {x : I3 → ℂ} (hx : UnitVec x) : UnitVec (star x) := by
  intro t; simp [hx t]

lemma unitVec_one : UnitVec (1 : I3 → ℂ) := by intro t; simp

lemma block_gram_6 (A B : Mat3) (hA : A * Aᴴ = (3 : ℂ) • 1) (hB : B * Bᴴ = (3 : ℂ) • 1)
    (C D : Mat3) (hC : C * Cᴴ = (3 : ℂ) • 1) (hD : D * Dᴴ = (3 : ℂ) • 1)
    (hAC : A * Cᴴ + B * Dᴴ = 0) :
    fromBlocks A B C D * (fromBlocks A B C D)ᴴ = (6 : ℂ) • (1 : Mat6) := by
  have hCA : C * Aᴴ + D * Bᴴ = 0 := by
    have := congrArg conjTranspose hAC
    simpa [conjTranspose_add, conjTranspose_mul] using this
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, hA, hB, hC, hD, hAC, hCA,
    ← fromBlocks_one, fromBlocks_smul]
  congr 1 <;> first | (rw [← add_smul]; norm_num) | simp

theorem symH_isHadamard {x : I3 → ℂ} (hx : UnitVec x) : Hadamard6.IsHadamard (symH x) := by
  refine ⟨?_, ?_⟩
  · intro i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [symH, hx _, normSq_ω_pow, Complex.normSq_neg]
  · unfold symH
    have h1 := diagF3_gram hx
    have h2 : (-(diagonal x * F3)) * (-(diagonal x * F3))ᴴ = (3 : ℂ) • (1 : Mat3) := by
      rw [conjTranspose_neg, neg_mul_neg, h1]
    refine block_gram_6 _ _ F3_mul_conjTranspose h1 _ _ F3_mul_conjTranspose h2 ?_
    rw [conjTranspose_neg, mul_neg, F3_mul_conjTranspose, h1, add_neg_cancel]

theorem symK_isHadamard {y u v : I3 → ℂ} (hy : UnitVec y) (hu : UnitVec u) (hv : UnitVec v) :
    Hadamard6.IsHadamard (symK y u v) := by
  have huy := hu.mul hy
  have hvy := hv.mul hy
  refine ⟨?_, ?_⟩
  · intro i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [symK, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
        fromBlocks_apply₂₂, Matrix.neg_apply, Complex.normSq_neg]
    exacts [diagF3_entry hu i j, diagF3_entry huy i j, diagF3_entry hv i j,
      diagF3_entry hvy i j]
  · unfold symK
    have h4 : (-(diagonal (v * y) * F3)) * (-(diagonal (v * y) * F3))ᴴ =
        (3 : ℂ) • (1 : Mat3) := by
      rw [conjTranspose_neg, neg_mul_neg, diagF3_gram hvy]
    refine block_gram_6 _ _ (diagF3_gram hu) (diagF3_gram huy) _ _ (diagF3_gram hv) h4 ?_
    rw [conjTranspose_neg, mul_neg]
    simp only [conjTranspose_mul, diagonal_conjTranspose]
    have e : ∀ a b : I3 → ℂ, diagonal a * F3 * (F3ᴴ * diagonal (star b)) =
        (3 : ℂ) • diagonal (a * star b) := by
      intro a b
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc F3, F3_mul_conjTranspose, Matrix.smul_mul,
        Matrix.one_mul, Matrix.mul_smul, diagonal_mul_diagonal]; rfl
    rw [e, e, ← smul_neg, ← smul_add]
    have : u * star v + -(u * y * star (v * y)) = 0 := by
      funext t
      simp only [Pi.add_apply, Pi.mul_apply, Pi.neg_apply, Pi.star_apply, star_mul',
        Pi.zero_apply]
      have := mul_star_self_of_normSq (hy t)
      linear_combination (-(u t * star (v t))) * this
    rw [diagonal_neg, diagonal_add]
    have this' : (fun i => (u * star v) i + -(u * y * star (v * y)) i) = 0 := this
    rw [this']; simp

/-- The four `3 × 3` blocks of `(symH x)ᴴ * symK y u v` are the circulants of
`u+v`, `(u-v) y`, `x̄ (u-v)` and `x̄ (u+v) y`. -/
theorem symH_conjTranspose_mul_symK (x y u v : I3 → ℂ) :
    (symH x)ᴴ * symK y u v =
      fromBlocks (circ (u + v)) (circ ((u - v) * y)) (circ (star x * (u - v)))
        (circ (star x * (u + v) * y)) := by
  unfold symH symK circ
  rw [fromBlocks_conjTranspose, fromBlocks_multiply]
  congr 1 <;> ext i j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

lemma fromBlocks_normSq_iff (A B C D : Mat3) (r : ℝ) :
    (∀ i j, Complex.normSq (fromBlocks A B C D i j) = r) ↔
      (∀ i j, Complex.normSq (A i j) = r) ∧ (∀ i j, Complex.normSq (B i j) = r) ∧
      (∀ i j, Complex.normSq (C i j) = r) ∧ (∀ i j, Complex.normSq (D i j) = r) := by
  constructor
  · intro h
    exact ⟨fun i j => h (Sum.inl i) (Sum.inl j), fun i j => h (Sum.inl i) (Sum.inr j),
      fun i j => h (Sum.inr i) (Sum.inl j), fun i j => h (Sum.inr i) (Sum.inr j)⟩
  · rintro ⟨hA, hB, hC, hD⟩ i j
    rcases i with i | i <;> rcases j with j | j
    exacts [hA i j, hB i j, hC i j, hD i j]

/-- **Criterion for the symmetric normal form.**  For unit phases, the triple
`{I₆, symH x/√6, symK y u v/√6}` is a MUB triple iff the four circulant blocks of
the transition are flat. -/
theorem isMUBTriple_sym_iff {x y u v : I3 → ℂ} (hx : UnitVec x) (hy : UnitVec y)
    (hu : UnitVec u) (hv : UnitVec v) :
    IsMUBTriple (std (symH x) (symK y u v)) ↔
      Flat (u + v) ∧ Flat ((u - v) * y) ∧ Flat (star x * (u - v)) ∧
        Flat (star x * (u + v) * y) := by
  rw [isMUBTriple_std_iff, symH_conjTranspose_mul_symK, fromBlocks_normSq_iff]
  simp only [Flat]
  constructor
  · rintro ⟨-, -, h⟩; exact h
  · intro h; exact ⟨symH_isHadamard hx, symK_isHadamard hy hu hv, h⟩

end MUBTriples
