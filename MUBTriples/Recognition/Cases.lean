import MUBTriples.Recognition.Gauge

/-!
# Algebraic recognition in the normal form: the independent/dependent case split

For unit phases `x, y, u, v` with `{I₆, symH x/√6, symK y u v/√6}` a MUB triple, put
`p = u + v`, `m = u - v` and

* `Aₜ = p̄ₜ pₜ₊₁`, `Bₜ = conj(mₜ yₜ) mₜ₊₁ yₜ₊₁` (the autocorrelation terms of the two
  upper circulant blocks; SM: `Aₜ = ᾱₜ αₜ₊₁`, `Bₜ = β̄ₜ βₜ₊₁` up to normalization);
* `zₜ = -x̄ₜ yₜ uₜ vₜ` and `wₜ = zₜ z̄ₜ₊₁` (SM: `wₜ = zₜ z̄ₜ₊₁`; for unit `u ≠ v` our `zₜ`
  equals `x̄ₜ yₜ mₜ / m̄ₜ`).

Flatness gives `Σ A = Σ B = 0` and `Σ w A = Σ w B = 0` (SM Eq. `tc-recognition-equations`).

* `family_of_w_const`: if `w` is constant the triple is equivalent to a member of the
  continuous family (orbit shift and scalar phase make `z ≡ 1`, i.e. `y = -x ū v̄`).
* independent case (`A₁B₂ ≠ A₂B₁`): `w` is constant.
* dependent case: `|pₜ|² = 2` for all `t`, `A` and `w` are equilateral, and either `w` is
  constant or `wₜ = w₀ ζᵗ` with `Aₜ = A₀ ζᵗ`, `ζ ∈ {ω, ω²}` (`IsolatedData`).
-/

open Matrix Hadamard6

namespace MUBTriples

/-- `Aₜ = p̄ₜ pₜ₊₁` with `p = u + v`. -/
def Avec (u v : I3 → ℂ) (t : I3) : ℂ := star (u t + v t) * (u (t + 1) + v (t + 1))

/-- `Bₜ = conj(mₜ yₜ) mₜ₊₁ yₜ₊₁` with `m = u - v`. -/
def Bvec (y u v : I3 → ℂ) (t : I3) : ℂ :=
  star ((u t - v t) * y t) * ((u (t + 1) - v (t + 1)) * y (t + 1))

/-- `zₜ = -x̄ₜ yₜ uₜ vₜ`. -/
def zvec (x y u v : I3 → ℂ) (t : I3) : ℂ := -(star (x t) * y t * u t * v t)

/-- `wₜ = zₜ z̄ₜ₊₁`. -/
def wvec (x y u v : I3 → ℂ) (t : I3) : ℂ := zvec x y u v t * star (zvec x y u v (t + 1))

lemma star_eq_inv_of_normSq {z : ℂ} (h : Complex.normSq z = 1) : star z = z⁻¹ := by
  have hz : z ≠ 0 := by intro h0; rw [h0] at h; simp at h
  exact eq_inv_of_mul_eq_one_right (mul_star_self_of_normSq h)

lemma ne_zero_of_normSq {z : ℂ} (h : Complex.normSq z = 1) : z ≠ 0 := by
  intro h0; rw [h0] at h; simp at h

lemma autoc_eq_sum (d : I3 → ℂ) : autoc d = ∑ t : I3, star (d t) * d (t + 1) := by
  simp [autoc, Fin.sum_univ_three]

lemma sum_Avec (u v : I3 → ℂ) : ∑ t, Avec u v t = autoc (u + v) := by
  rw [autoc_eq_sum]; rfl

lemma sum_Bvec (y u v : I3 → ℂ) : ∑ t, Bvec y u v t = autoc ((u - v) * y) := by
  rw [autoc_eq_sum]; rfl

lemma normSq_zvec {x y u v : I3 → ℂ} (hx : UnitVec x) (hy : UnitVec y) (hu : UnitVec u)
    (hv : UnitVec v) (t : I3) : Complex.normSq (zvec x y u v t) = 1 := by
  simp [zvec, Complex.normSq_mul, hx t, hy t, hu t, hv t]

lemma normSq_wvec {x y u v : I3 → ℂ} (hx : UnitVec x) (hy : UnitVec y) (hu : UnitVec u)
    (hv : UnitVec v) (t : I3) : Complex.normSq (wvec x y u v t) = 1 := by
  simp [wvec, Complex.normSq_mul, normSq_zvec hx hy hu hv]

/-- `Σ w A = conj (autoc (x̄ (u+v) y))`. -/
lemma sum_wA {x y u v : I3 → ℂ} (hx : UnitVec x) (hy : UnitVec y) (hu : UnitVec u)
    (hv : UnitVec v) :
    ∑ t, wvec x y u v t * Avec u v t = star (autoc (star x * (u + v) * y)) := by
  rw [autoc_eq_sum, star_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  simp only [wvec, zvec, Avec, Pi.mul_apply, Pi.add_apply, Pi.star_apply, star_mul', star_add,
    star_neg, star_star, star_inv₀, inv_inv, star_eq_inv_of_normSq (hx t), star_eq_inv_of_normSq (hy t),
    star_eq_inv_of_normSq (hu t), star_eq_inv_of_normSq (hv t),
    star_eq_inv_of_normSq (hx (t + 1)), star_eq_inv_of_normSq (hy (t + 1)),
    star_eq_inv_of_normSq (hu (t + 1)), star_eq_inv_of_normSq (hv (t + 1))]
  have := ne_zero_of_normSq (hx t); have := ne_zero_of_normSq (hy t)
  have := ne_zero_of_normSq (hu t); have := ne_zero_of_normSq (hv t)
  have := ne_zero_of_normSq (hx (t + 1)); have := ne_zero_of_normSq (hy (t + 1))
  have := ne_zero_of_normSq (hu (t + 1)); have := ne_zero_of_normSq (hv (t + 1))
  field_simp
  ring

/-- `Σ w B = conj (autoc (x̄ (u-v)))`. -/
lemma sum_wB {x y u v : I3 → ℂ} (hx : UnitVec x) (hy : UnitVec y) (hu : UnitVec u)
    (hv : UnitVec v) :
    ∑ t, wvec x y u v t * Bvec y u v t = star (autoc (star x * (u - v))) := by
  rw [autoc_eq_sum, star_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  simp only [wvec, zvec, Bvec, Pi.mul_apply, Pi.sub_apply, Pi.star_apply, star_mul', star_sub,
    star_neg, star_star, star_inv₀, inv_inv, star_eq_inv_of_normSq (hx t), star_eq_inv_of_normSq (hy t),
    star_eq_inv_of_normSq (hu t), star_eq_inv_of_normSq (hv t),
    star_eq_inv_of_normSq (hx (t + 1)), star_eq_inv_of_normSq (hy (t + 1)),
    star_eq_inv_of_normSq (hu (t + 1)), star_eq_inv_of_normSq (hv (t + 1))]
  have := ne_zero_of_normSq (hx t); have := ne_zero_of_normSq (hy t)
  have := ne_zero_of_normSq (hu t); have := ne_zero_of_normSq (hv t)
  have := ne_zero_of_normSq (hx (t + 1)); have := ne_zero_of_normSq (hy (t + 1))
  have := ne_zero_of_normSq (hu (t + 1)); have := ne_zero_of_normSq (hv (t + 1))
  field_simp
  ring

/-! ### Cube roots and equilateral triples -/

lemma cube_root_cases {c : ℂ} (h : c ^ 3 = 1) : ∃ j : I3, c = ω ^ j.val := by
  have hprod : (c - 1) * (c - ω) * (c - ω ^ 2) = 0 := by
    linear_combination h + (-c ^ 2 + c * ω - ω + 1) * ω_sq_add
  rcases mul_eq_zero.1 hprod with h1 | h2
  · rcases mul_eq_zero.1 h1 with h1 | h1
    · exact ⟨0, by simp [sub_eq_zero.1 h1]⟩
    · exact ⟨1, by simp [sub_eq_zero.1 h1]⟩
  · exact ⟨2, by simp [sub_eq_zero.1 h2]⟩

lemma ω_pow_mul_star (j : ℕ) : ω ^ j * star (ω ^ j) = 1 :=
  mul_star_self_of_normSq (normSq_ω_pow j)

/-- Three complex numbers of equal nonzero modulus summing to zero form an equilateral
triangle. -/
lemma equilateral {a b c : ℂ} {r : ℝ} (ha : Complex.normSq a = r) (hb : Complex.normSq b = r)
    (hc : Complex.normSq c = r) (hr : r ≠ 0) (hsum : a + b + c = 0) :
    (b = a * ω ∧ c = a * ω ^ 2) ∨ (b = a * ω ^ 2 ∧ c = a * ω) := by
  have ha0 : a ≠ 0 := by intro h0; rw [h0] at ha; simp at ha; exact hr ha.symm
  set β := b / a with hβ
  have hb' : b = a * β := by rw [hβ]; field_simp
  have hc' : c = a * (-1 - β) := by
    have : c = -a - b := by linear_combination hsum
    rw [this, hb']; ring
  have hβn : Complex.normSq β = 1 := by
    rw [hβ, Complex.normSq_div, ha, hb]; field_simp
  have hγn : Complex.normSq (-1 - β) = 1 := by
    have := hc; rw [hc', Complex.normSq_mul, ha] at this
    field_simp at this
    nlinarith [this]
  have hre : β.re = -(1 / 2) := by
    rw [Complex.normSq_apply] at hβn hγn
    simp at hγn
    nlinarith
  have him : (β.im - Real.sqrt 3 / 2) * (β.im + Real.sqrt 3 / 2) = 0 := by
    rw [Complex.normSq_apply, hre] at hβn
    nlinarith [sqrt3_sq]
  rcases mul_eq_zero.1 him with h | h
  · have hβω : β = ω := Complex.ext (by rw [hre]; simp) (by simp; linarith)
    left; constructor
    · rw [hb', hβω]
    · rw [hc', hβω, ω_sq]
  · have hβω : β = ω ^ 2 := Complex.ext (by rw [hre, ω_sq_re]) (by rw [ω_sq_im]; linarith)
    right; constructor
    · rw [hb', hβω]
    · rw [hc', hβω, ω_sq]; ring

/-! ### Constant `w`: the continuous family -/

lemma symK_mul_colOpK_orbit1 (y u v : I3 → ℂ) (j : I3) (lam : ℂ) :
    symK y u v * colOpK 0 j 1 lam = symK (fun t => lam * ω ^ (t.val * j.val) * y t) u v := by
  rw [symK_mul_colOpK y u v 0 j lam (by simp)]
  congr 1 <;> funext t <;> simp

/-- **Constant `w` gives the continuous family** (SM: "an orbit shift and scalar phase make
`zₜ = 1`"). -/
theorem family_of_w_const {x y u v : I3 → ℂ} (hx : UnitVec x) (hy : UnitVec y)
    (hu : UnitVec u) (hv : UnitVec v) (hT : IsMUBTriple (std (symH x) (symK y u v)))
    (c : ℂ) (hw : ∀ t, wvec x y u v t = c) :
    ∃ V, IsFamilyMember V ∧ TripleEquiv (std (symH x) (symK y u v)) V := by
  set z := zvec x y u v with hzdef
  have hz : ∀ t, Complex.normSq (z t) = 1 := normSq_zvec hx hy hu hv
  have hzz : ∀ t, star (z t) * z t = 1 := fun t => star_mul_self_of_normSq (hz t)
  have hstep : ∀ t, z (t + 1) = star c * z t := by
    intro t
    rw [← hw t, wvec, ← hzdef, star_mul', star_star]
    linear_combination (z (t + 1)) * (hzz t).symm
  have h1 : z 1 = star c * z 0 := hstep 0
  have h2 : z 2 = star c * z 1 := hstep 1
  have h0 : z 0 = star c * z 2 := hstep 2
  have hz0 : z 0 ≠ 0 := ne_zero_of_normSq (hz 0)
  have hc3 : c ^ 3 = 1 := by
    have : star c ^ 3 = 1 := by
      apply mul_right_cancel₀ hz0
      rw [one_mul]
      calc star c ^ 3 * z 0 = star c * (star c * (star c * z 0)) := by ring
        _ = z 0 := by rw [← h1, ← h2, ← h0]
    have := congrArg star this
    rwa [star_pow, star_star, star_one] at this
  obtain ⟨j, hj⟩ := cube_root_cases hc3
  set lam := star (z 0)
  have hlam : Complex.normSq lam = 1 := by simp [lam, hz 0]
  set y' : I3 → ℂ := fun t => lam * ω ^ (t.val * j.val) * y t with hy'
  -- the new `z` is identically `1`
  have hωc : ω ^ j.val * star c = 1 := by rw [hj]; exact ω_pow_mul_star _
  have hz' : ∀ t, lam * ω ^ (t.val * j.val) * z t = 1 := by
    intro t
    fin_cases t
    · simp only [Fin.zero_eta, Fin.val_zero, zero_mul, pow_zero, mul_one]
      exact hzz 0
    · simp only [Fin.mk_one, Fin.val_one, one_mul]
      rw [h1]
      linear_combination (ω ^ j.val * star c) * hzz 0 + hωc
    · simp only [Fin.reduceFinMk, Fin.val_two]
      rw [h2, h1, show (2 * j.val) = j.val + j.val by ring, pow_add]
      linear_combination (ω ^ j.val * star c * ω ^ j.val * star c) * hzz 0 +
        (ω ^ j.val * star c + 1) * hωc
  have hy'eq : y' = -(x * star u * star v) := by
    funext t
    have e := hz' t
    simp only [hzdef, zvec] at e
    simp only [hy', Pi.neg_apply, Pi.mul_apply, Pi.star_apply]
    have hxt := mul_star_self_of_normSq (hx t)
    have hut := mul_star_self_of_normSq (hu t)
    have hvt := mul_star_self_of_normSq (hv t)
    linear_combination (-(x t * star (u t) * star (v t))) * e -
      (lam * ω ^ (t.val * j.val) * y t) * (hxt + x t * star (x t) * hut +
        x t * star (x t) * u t * star (u t) * hvt)
  have hE : TripleEquiv (std (symH x) (symK y u v)) (familyTriple x u v) := by
    have := tripleEquiv_std_colK (H := symH x) (K := symK y u v)
      (isMonomial_colOpK (l₀ := 1) (l₁ := lam) 0 j (by simp) hlam)
    rw [symK_mul_colOpK_orbit1, ← hy', hy'eq, ← famK_eq_symK hu hv] at this
    exact this
  exact ⟨_, ⟨x, u, v, hx, hu, hv, rfl, isMUBTriple_of_tripleEquiv hE hT⟩, hE⟩

/-! ### The case split -/

/-- The data left in the dependent case when `w` is not constant (SM: `wₜ = ω^j ω^{εt}`). -/
def IsolatedData (x y u v : I3 → ℂ) : Prop :=
  ∃ ζ : ℂ, (ζ = ω ∨ ζ = ω ^ 2) ∧ (∀ t, Complex.normSq (u t + v t) = 2) ∧
    Avec u v 1 = Avec u v 0 * ζ ∧ Avec u v 2 = Avec u v 0 * ζ ^ 2 ∧
    wvec x y u v 1 = wvec x y u v 0 * ζ ∧ wvec x y u v 2 = wvec x y u v 0 * ζ ^ 2

lemma ω_sq_sq : (ω ^ 2) ^ 2 = ω := by
  rw [← pow_mul, ω_pow_reduce 4 (by norm_num)]; simp

lemma normSq_Avec (u v : I3 → ℂ) (t : I3) :
    Complex.normSq (Avec u v t) = Complex.normSq (u t + v t) * Complex.normSq (u (t + 1) + v (t + 1)) := by
  rw [Avec, Complex.normSq_mul, normSq_star]

lemma normSq_Bvec {y : I3 → ℂ} (hy : UnitVec y) (u v : I3 → ℂ) (t : I3) :
    Complex.normSq (Bvec y u v t) = Complex.normSq (u t - v t) * Complex.normSq (u (t + 1) - v (t + 1)) := by
  rw [Bvec, Complex.normSq_mul, normSq_star, Complex.normSq_mul, Complex.normSq_mul, hy t, hy (t + 1)]
  ring

/-- **Recognition in the normal form, up to the isolated data.**  A MUB triple in the
symmetric normal form is equivalent to a member of the continuous family, or it satisfies
`IsolatedData` (dependent case with non-constant `w`). -/
theorem recognition_dichotomy {x y u v : I3 → ℂ} (hx : UnitVec x) (hy : UnitVec y)
    (hu : UnitVec u) (hv : UnitVec v) (hT : IsMUBTriple (std (symH x) (symK y u v))) :
    (∃ V, IsFamilyMember V ∧ TripleEquiv (std (symH x) (symK y u v)) V) ∨
      IsolatedData x y u v := by
  obtain ⟨fp, fm, fxm, fxp⟩ := (isMUBTriple_sym_iff hx hy hu hv).1 hT
  obtain ⟨Sp, hA⟩ := (flat_iff _).1 fp
  obtain ⟨-, hB⟩ := (flat_iff _).1 fm
  obtain ⟨-, hxm⟩ := (flat_iff _).1 fxm
  obtain ⟨-, hxp⟩ := (flat_iff _).1 fxp
  have hwA := sum_wA hx hy hu hv
  have hwB := sum_wB hx hy hu hv
  rw [hxp, star_zero, Fin.sum_univ_three] at hwA
  rw [hxm, star_zero, Fin.sum_univ_three] at hwB
  have hA3 := sum_Avec u v; rw [hA, Fin.sum_univ_three] at hA3
  have hB3 := sum_Bvec y u v; rw [hB, Fin.sum_univ_three] at hB3
  set A := Avec u v
  set B := Bvec y u v
  set w := wvec x y u v
  have hα : (w 1 - w 0) * A 1 + (w 2 - w 0) * A 2 = 0 := by
    linear_combination hwA - w 0 * hA3
  have hβ : (w 1 - w 0) * B 1 + (w 2 - w 0) * B 2 = 0 := by
    linear_combination hwB - w 0 * hB3
  by_cases hind : A 1 * B 2 - A 2 * B 1 = 0
  · -- dependent case
    have hle : ∀ t, Complex.normSq (u t + v t) ≤ 4 := fun t => normSq_add_le_four (hu t) (hv t)
    have hp0 : ∀ t, u t + v t ≠ 0 := flat_ne_zero fp hle
    have hm0 : ∀ t, u t - v t ≠ 0 := by
      intro t h
      have := flat_ne_zero fm (fun t => by
        simp only [Pi.mul_apply, Pi.sub_apply, Complex.normSq_mul, hy t, mul_one]
        exact normSq_sub_le_four (hu t) (hv t)) t
      apply this; simp [h]
    set P : I3 → ℝ := fun t => Complex.normSq (u t + v t) with hP
    have hM : ∀ t, Complex.normSq (u t - v t) = 4 - P t := fun t => by
      have := normSq_add_add_sub (hu t) (hv t); simp only [hP]; linarith
    have hPpos : ∀ t, 0 < P t := fun t => Complex.normSq_pos.2 (hp0 t)
    have hMpos : ∀ t, 0 < 4 - P t := fun t => by rw [← hM]; exact Complex.normSq_pos.2 (hm0 t)
    have hdep2 : A 0 * B 1 - A 1 * B 0 = 0 := by
      linear_combination hind + B 1 * hA3 - A 1 * hB3
    have n12 := congrArg Complex.normSq (sub_eq_zero.1 hind)
    have n01 := congrArg Complex.normSq (sub_eq_zero.1 hdep2)
    simp only [Complex.normSq_mul, A, B, normSq_Avec, normSq_Bvec hy, hM] at n12 n01
    simp only [show (1 : I3) + 1 = 2 by rfl, show (2 : I3) + 1 = 0 by rfl,
      show (0 : I3) + 1 = 1 by rfl] at n12 n01
    have e10 : P 1 = P 0 := by
      have h := hPpos 2; have h' := hMpos 2
      have : P 2 * (4 - P 2) * (P 1 * (4 - P 0) - P 0 * (4 - P 1)) = 0 := by
        simp only [hP] at n12 ⊢; nlinarith [n12]
      rcases mul_eq_zero.1 this with h0 | h0
      · exact absurd h0 (by positivity)
      · nlinarith
    have e20 : P 2 = P 0 := by
      have h := hPpos 1; have h' := hMpos 1
      have : P 1 * (4 - P 1) * (P 0 * (4 - P 2) - P 2 * (4 - P 0)) = 0 := by
        simp only [hP] at n01 ⊢; nlinarith [n01]
      rcases mul_eq_zero.1 this with h0 | h0
      · exact absurd h0 (by positivity)
      · nlinarith
    have hP2 : ∀ t, P t = 2 := by
      have hs : P 0 + P 1 + P 2 = 6 := by rw [sqSum_eq] at Sp; simpa [hP] using Sp
      intro t; fin_cases t <;> simp <;> linarith
    -- `A` is equilateral
    have nA : ∀ t, Complex.normSq (A t) = 4 := by
      intro t; simp only [A, normSq_Avec]
      have h1 := hP2 t; have h2 := hP2 (t + 1); simp only [hP] at h1 h2
      rw [h1, h2]; norm_num
    have hA0 : A 0 ≠ 0 := by intro h; have := nA 0; rw [h] at this; simp at this
    have hwn : ∀ t, Complex.normSq (w t) = 1 := normSq_wvec hx hy hu hv
    obtain ⟨ζ, hζ, hA1, hA2⟩ : ∃ ζ : ℂ, (ζ = ω ∨ ζ = ω ^ 2) ∧ A 1 = A 0 * ζ ∧ A 2 = A 0 * ζ ^ 2 := by
      rcases equilateral (nA 0) (nA 1) (nA 2) (by norm_num) hA3 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨ω, Or.inl rfl, h1, h2⟩
      · exact ⟨ω ^ 2, Or.inr rfl, h1, by rw [h2, ω_sq_sq]⟩
    have hζn : Complex.normSq ζ = 1 := by
      rcases hζ with rfl | rfl <;> simp [normSq_ω_pow, normSq_ω]
    have hsum : w 0 + w 1 * ζ + w 2 * ζ ^ 2 = 0 := by
      apply mul_left_cancel₀ hA0
      linear_combination hwA - w 1 * hA1 - w 2 * hA2
    have n1 : Complex.normSq (w 1 * ζ) = 1 := by rw [Complex.normSq_mul, hwn, hζn, one_mul]
    have n2 : Complex.normSq (w 2 * ζ ^ 2) = 1 := by
      rw [Complex.normSq_mul, hwn, map_pow, hζn, one_pow, one_mul]
    have hPd : ∀ t, Complex.normSq (u t + v t) = 2 := fun t => by
      have := hP2 t; simpa [hP] using this
    have hω2 : ω ^ 2 ≠ 0 := pow_ne_zero 2 ω_ne_zero
    rcases equilateral (hwn 0) n1 n2 one_ne_zero hsum with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
      rcases hζ with rfl | rfl
    · -- `ζ = ω`, `w` constant
      left
      refine family_of_w_const hx hy hu hv hT (w 0) (fun t => ?_)
      fin_cases t
      · rfl
      · exact mul_right_cancel₀ ω_ne_zero e1
      · exact mul_right_cancel₀ hω2 e2
    · -- `ζ = ω²`: isolated data
      right
      refine ⟨ω ^ 2, Or.inr rfl, hPd, hA1, hA2, ?_, ?_⟩
      · apply mul_right_cancel₀ hω2
        rw [e1]; linear_combination (-(w 0 * ω)) * ω_cube
      · apply mul_right_cancel₀ (pow_ne_zero 2 hω2)
        rw [e2, ω_sq_sq]; ring
    · -- `ζ = ω`: isolated data
      right
      refine ⟨ω, Or.inl rfl, hPd, hA1, hA2, ?_, ?_⟩
      · apply mul_right_cancel₀ ω_ne_zero
        rw [e1]; ring
      · apply mul_right_cancel₀ hω2
        rw [e2]; linear_combination (-(w 0 * ω)) * ω_cube
    · -- `ζ = ω²`, `w` constant
      left
      refine family_of_w_const hx hy hu hv hT (w 0) (fun t => ?_)
      fin_cases t
      · rfl
      · exact mul_right_cancel₀ hω2 e1
      · rw [ω_sq_sq] at e2; exact mul_right_cancel₀ ω_ne_zero e2
  · -- independent case: `w` is constant
    left
    have h1 : w 1 - w 0 = 0 := by
      have : (w 1 - w 0) * (A 1 * B 2 - A 2 * B 1) = 0 := by
        linear_combination B 2 * hα - A 2 * hβ
      exact (mul_eq_zero.1 this).resolve_right hind
    have h2 : w 2 - w 0 = 0 := by
      have : (w 2 - w 0) * (A 1 * B 2 - A 2 * B 1) = 0 := by
        linear_combination A 1 * hβ - B 1 * hα
      exact (mul_eq_zero.1 this).resolve_right hind
    refine family_of_w_const hx hy hu hv hT (w 0) (fun t => ?_)
    fin_cases t
    · rfl
    · exact sub_eq_zero.1 h1
    · exact sub_eq_zero.1 h2

end MUBTriples
