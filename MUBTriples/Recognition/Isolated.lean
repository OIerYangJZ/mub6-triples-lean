import MUBTriples.Recognition.Main

/-!
# The isolated case of the recognition (SM: dependent case, `wₜ = ω^j ω^{εt}`)

We prove `IsolatedRecognition`: a normal-form MUB triple with `IsolatedData` is equivalent
to the isolated Fourier triple.  Steps:

1. `vₜ = ±i uₜ`; swapping the two coordinates of the eigenspaces with `vₜ = -i uₜ` gives
   `v = i u` (`swapMat`).
2. A rephasing and shift of the first `K`-orbit gives `u = (1, 1, ζ)`.
3. Flatness and the `w`-pattern force `x` and `y` to be geometric; column operations give
   `x = y = 1`.
4. `ζ = ω` is the isolated triple after a cyclic relabelling; `ζ = ω²` is related to it by
   the common unitary `(F₂ ⊗ F₃)ᴴ/√6` and the exchange of the first two bases
   (SM Eq. `tc-product-equivalence`).
-/

open Matrix Hadamard6

namespace MUBTriples

/-- Normalize a polynomial identity in `ω` modulo `ω² + ω + 1`. -/
macro "ω_norm" : tactic =>
  `(tactic| (
    ring_nf
    try simp only [ω_pow_reduce, Nat.reduceLeDiff, Nat.reduceSub, pow_one]
    try ring_nf
    try simp only [ω_pow_reduce, Nat.reduceLeDiff, Nat.reduceSub, pow_one]
    try simp only [ω_sq]
    try ring_nf))

lemma conj_ω : (starRingEnd ℂ) ω = ω ^ 2 := star_ω

/-! ### Swapping the two coordinates of selected eigenspaces -/

/-- Exchange `(0, t) ↔ (1, t)` for every `t` with `b t`. -/
def swapPerm (b : I3 → Bool) : Equiv.Perm I6 where
  toFun i := match i with
    | Sum.inl t => if b t then Sum.inr t else Sum.inl t
    | Sum.inr t => if b t then Sum.inl t else Sum.inr t
  invFun i := match i with
    | Sum.inl t => if b t then Sum.inr t else Sum.inl t
    | Sum.inr t => if b t then Sum.inl t else Sum.inr t
  left_inv i := by rcases i with t | t <;> by_cases h : b t <;> simp [h]
  right_inv i := by rcases i with t | t <;> by_cases h : b t <;> simp [h]

/-- The row operation `A ↦ (i ↦ A (swapPerm b i))`. -/
noncomputable def swapMat (b : I3 → Bool) : Mat6 := monomial (swapPerm b)⁻¹ (fun _ => 1)

lemma isMonomial_swapMat (b : I3 → Bool) : IsMonomial (swapMat b) :=
  ⟨_, _, fun _ => by simp, rfl⟩

lemma swapMat_mul_apply (b : I3 → Bool) (A : Mat6) (i j : I6) :
    (swapMat b * A) i j = A (swapPerm b i) j := by
  rw [swapMat, monomial_mul_apply]; simp

lemma swapMat_symH (b : I3 → Bool) (x : I3 → ℂ) :
    swapMat b * symH x = symH (fun t => if b t then -x t else x t) := by
  ext i j
  rw [swapMat_mul_apply]
  rcases i with t | t <;> rcases j with s | s <;> by_cases h : b t <;>
    simp [swapPerm, h, symH, diagonal_mul]

lemma swapMat_symK (b : I3 → Bool) (y u v : I3 → ℂ) :
    swapMat b * symK y u v = symK (fun t => if b t then -y t else y t)
      (fun t => if b t then v t else u t) (fun t => if b t then u t else v t) := by
  ext i j
  rw [swapMat_mul_apply]
  rcases i with t | t <;> rcases j with s | s <;> by_cases h : b t <;>
    simp [swapPerm, h, symK, diagonal_mul]

lemma tripleEquiv_swap (b : I3 → Bool) (x y u v : I3 → ℂ) :
    TripleEquiv (std (symH x) (symK y u v))
      (std (symH (fun t => if b t then -x t else x t))
        (symK (fun t => if b t then -y t else y t)
          (fun t => if b t then v t else u t) (fun t => if b t then u t else v t))) := by
  have := tripleEquiv_std_row (H := symH x) (K := symK y u v) (isMonomial_swapMat b)
  rwa [swapMat_symH, swapMat_symK] at this

/-! ### Invariance of the isolated data -/

/-- The `w`-pattern of `IsolatedData`. -/
def WPattern (w : I3 → ℂ) (ζ : ℂ) : Prop := w 1 = w 0 * ζ ∧ w 2 = w 0 * ζ ^ 2

lemma WPattern.smul {w : I3 → ℂ} {ζ : ℂ} (h : WPattern w ζ) (κ : ℂ) :
    WPattern (fun t => κ * w t) ζ := by
  simp only [WPattern] at h ⊢; rw [h.1, h.2]; constructor <;> ring

lemma isolatedData_iff (x y u v : I3 → ℂ) : IsolatedData x y u v ↔
    ∃ ζ : ℂ, (ζ = ω ∨ ζ = ω ^ 2) ∧ (∀ t, Complex.normSq (u t + v t) = 2) ∧
      WPattern (Avec u v) ζ ∧ WPattern (wvec x y u v) ζ := by
  simp only [IsolatedData, WPattern]
  constructor
  · rintro ⟨ζ, h1, h2, h3, h4, h5, h6⟩; exact ⟨ζ, h1, h2, ⟨h3, h4⟩, ⟨h5, h6⟩⟩
  · rintro ⟨ζ, h1, h2, ⟨h3, h4⟩, ⟨h5, h6⟩⟩; exact ⟨ζ, h1, h2, h3, h4, h5, h6⟩

/-- If `z' = κ ω^{tm} z` with `|κ| = 1`, then `w' = ω̄^m w`. -/
lemma wvec_of_zvec {x y u v x' y' u' v' : I3 → ℂ} {κ : ℂ} (hκ : Complex.normSq κ = 1) (m : ℕ)
    (hz : ∀ t, zvec x' y' u' v' t = κ * ω ^ (t.val * m) * zvec x y u v t) :
    ∀ t, wvec x' y' u' v' t = star (ω ^ m) * wvec x y u v t := by
  have hkk := mul_star_self_of_normSq hκ
  have hω : ∀ n : ℕ, ω ^ n * star (ω ^ n) = 1 := fun n => ω_pow_mul_star n
  intro t
  simp only [wvec, hz, star_mul']
  fin_cases t
  · simp only [Fin.zero_eta, Fin.val_zero, zero_mul, pow_zero, mul_one, zero_add, Fin.val_one,
      one_mul]
    linear_combination (star (ω ^ m) * zvec x y u v 0 * star (zvec x y u v 1)) * hkk
  · simp only [Fin.mk_one, show (1 : I3) + 1 = 2 from rfl, Fin.val_one, Fin.val_two, one_mul]
    rw [show 2 * m = m + m by ring, pow_add, star_mul']
    linear_combination (star (ω ^ m) * zvec x y u v 1 * star (zvec x y u v 2)) *
      (ω ^ m * star (ω ^ m) * hkk + hω m)
  · simp only [Fin.reduceFinMk, show (2 : I3) + 1 = 0 from rfl, Fin.val_two, Fin.val_zero,
      zero_mul, pow_zero, star_one, mul_one]
    have h3 : ω ^ (2 * m) = star (ω ^ m) := by
      have : ω ^ (2 * m) * ω ^ m = 1 := by
        rw [← pow_add, show 2 * m + m = 3 * m by ring, pow_mul, ω_cube, one_pow]
      calc ω ^ (2 * m) = ω ^ (2 * m) * (ω ^ m * star (ω ^ m)) := by rw [hω, mul_one]
        _ = star (ω ^ m) := by rw [← mul_assoc, this, one_mul]
    rw [h3]
    linear_combination (star (ω ^ m) * zvec x y u v 2 * star (zvec x y u v 0)) * hkk

/-- Generalized scaling of correlation terms. -/
lemma corr_scale {f f' : I3 → ℂ} {κ : ℂ} (hκ : Complex.normSq κ = 1) (m : ℕ)
    (h : ∀ t, f' t = κ * ω ^ (t.val * m) * f t) :
    ∀ t, f' t * star (f' (t + 1)) = star (ω ^ m) * (f t * star (f (t + 1))) := by
  have := wvec_of_zvec (x := fun _ => -1) (y := f) (u := fun _ => 1) (v := fun _ => 1)
    (x' := fun _ => -1) (y' := f') (u' := fun _ => 1) (v' := fun _ => 1) hκ m
    (fun t => by simp [zvec, h t])
  intro t
  have ht := this t
  simpa [wvec, zvec] using ht

lemma avec_eq_star (u v : I3 → ℂ) (t : I3) :
    Avec u v t = star ((u t + v t) * star (u (t + 1) + v (t + 1))) := by
  simp [Avec, star_mul']

/-! ### Step 1: `v = i u` -/

lemma v_eq_pm_i {u v : ℂ} (hu : Complex.normSq u = 1) (hv : Complex.normSq v = 1)
    (h : Complex.normSq (u + v) = 2) : v = Complex.I * u ∨ v = -(Complex.I * u) := by
  set q := v * star u with hq
  have hqn : Complex.normSq q = 1 := by simp [hq, Complex.normSq_mul, hu, hv]
  have hvq : v = q * u := by
    rw [hq, mul_assoc, star_mul_self_of_normSq hu, mul_one]
  have hre : q.re = 0 := by
    have h1 := Complex.normSq_add u v
    have : (u * (starRingEnd ℂ) v).re = q.re := by
      rw [hq]; simp [Complex.mul_re]; ring
    rw [this] at h1
    linarith
  have him : q.im = 1 ∨ q.im = -1 := by
    rw [Complex.normSq_apply, hre] at hqn
    have : (q.im - 1) * (q.im + 1) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  rcases him with h | h
  · left; rw [hvq]; congr 1; exact Complex.ext (by simp [hre]) (by simp [h])
  · right; rw [hvq, ← neg_mul]; congr 1; exact Complex.ext (by simp [hre]) (by simp [h])

open Classical in
/-- **Step 1.** -/
theorem step_v_eq_i {x y u v : I3 → ℂ} (hx : UnitVec x) (hy : UnitVec y) (hu : UnitVec u)
    (hv : UnitVec v) {ζ : ℂ} (hP : ∀ t, Complex.normSq (u t + v t) = 2)
    (hA : WPattern (Avec u v) ζ) (hw : WPattern (wvec x y u v) ζ) :
    ∃ x' y' u' v' : I3 → ℂ, UnitVec x' ∧ UnitVec y' ∧ UnitVec u' ∧ UnitVec v' ∧
      (∀ t, v' t = Complex.I * u' t) ∧ WPattern (Avec u' v') ζ ∧
      WPattern (wvec x' y' u' v') ζ ∧
      TripleEquiv (std (symH x) (symK y u v)) (std (symH x') (symK y' u' v')) := by
  set b : I3 → Bool := fun t => decide (v t ≠ Complex.I * u t)
  refine ⟨_, _, _, _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, tripleEquiv_swap b x y u v⟩
  · intro t; by_cases h : b t <;> simp [h, hx t]
  · intro t; by_cases h : b t <;> simp [h, hy t]
  · intro t; by_cases h : b t <;> simp [h, hu t, hv t]
  · intro t; by_cases h : b t <;> simp [h, hu t, hv t]
  · intro t
    by_cases h : b t
    · simp only [h, if_true]
      have hb : v t ≠ Complex.I * u t := by simpa [b] using h
      rcases v_eq_pm_i (hu t) (hv t) (hP t) with h' | h'
      · exact absurd h' hb
      · rw [h']; ring_nf; rw [Complex.I_sq]; ring
    · simp only [h, if_false]
      simpa [b] using h
  · have e : Avec (fun t => if b t then v t else u t) (fun t => if b t then u t else v t) =
        Avec u v := by
      funext t; simp only [Avec]
      cases h1 : b t <;> cases h2 : b (t + 1) <;> simp only [h1, h2, ite_true, ite_false,
        Bool.false_eq_true, ↓reduceIte] <;> ring
    rw [e]; exact hA
  · have e : wvec (fun t => if b t then -x t else x t) (fun t => if b t then -y t else y t)
        (fun t => if b t then v t else u t) (fun t => if b t then u t else v t) =
        wvec x y u v := by
      have hz : zvec (fun t => if b t then -x t else x t) (fun t => if b t then -y t else y t)
          (fun t => if b t then v t else u t) (fun t => if b t then u t else v t) =
          zvec x y u v := by
        funext t; simp only [zvec]
        cases h1 : b t <;> simp only [h1, ite_true, ite_false, Bool.false_eq_true, ↓reduceIte,
          star_neg] <;> ring
      funext t; simp only [wvec, hz]
    rw [e]; exact hw

/-! ### Step 2: `u = (1, 1, ζ)` -/

lemma ω_neg_mul (k : I3) : ω ^ (-k).val * ω ^ k.val = 1 := by
  have : (-k).val + k.val = 0 ∨ (-k).val + k.val = 3 := by fin_cases k <;> decide
  rw [← pow_add]
  rcases this with h | h <;> rw [h]
  · simp
  · exact ω_cube

lemma ζ_cube {ζ : ℂ} (hζ : ζ = ω ∨ ζ = ω ^ 2) : ζ ^ 3 = 1 := by
  rcases hζ with rfl | rfl
  · exact ω_cube
  · rw [← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, ω_cube, one_pow]

/-- The canonical `u = (1, 1, ζ)`. -/
def uCan (ζ : ℂ) : I3 → ℂ := ![1, 1, ζ]

/-- **Step 2.** -/
theorem step_u_canonical {x y u v : I3 → ℂ} (hy : UnitVec y) (hu : UnitVec u)
    (hvI : ∀ t, v t = Complex.I * u t) {ζ : ℂ} (hζ : ζ = ω ∨ ζ = ω ^ 2)
    (hA : WPattern (Avec u v) ζ) (hw : WPattern (wvec x y u v) ζ) :
    ∃ y' : I3 → ℂ, UnitVec y' ∧
      WPattern (wvec x y' (uCan ζ) (fun t => Complex.I * uCan ζ t)) ζ ∧
      TripleEquiv (std (symH x) (symK y u v))
        (std (symH x) (symK y' (uCan ζ) (fun t => Complex.I * uCan ζ t))) := by
  have huu : ∀ t, star (u t) * u t = 1 := fun t => star_mul_self_of_normSq (hu t)
  set c : I3 → ℂ := fun t => star (u t) * u (t + 1) with hc
  have hAc : ∀ t, Avec u v t = 2 * c t := by
    intro t; simp only [Avec, hvI, hc, star_add, star_mul', Complex.star_def, Complex.conj_I]
    ring_nf; rw [Complex.I_sq]; ring
  have hc1 : c 1 = c 0 * ζ := by
    have := hA.1; rw [hAc, hAc] at this; linear_combination (1 / 2 : ℂ) * this
  have hc2 : c 2 = c 0 * ζ ^ 2 := by
    have := hA.2; rw [hAc, hAc] at this; linear_combination (1 / 2 : ℂ) * this
  have hprod : c 0 * c 1 * c 2 = 1 := by
    simp only [hc]
    simp only [show (0 : I3) + 1 = 1 from rfl, show (1 : I3) + 1 = 2 from rfl,
      show (2 : I3) + 1 = 0 from rfl]
    linear_combination (star (u 0) * u 0 * star (u 1) * u 1) * huu 2 +
      star (u 0) * u 0 * huu 1 + huu 0
  have hc03 : c 0 ^ 3 = 1 := by
    have h3 := ζ_cube hζ
    rw [hc1, hc2] at hprod
    linear_combination hprod - c 0 ^ 3 * h3
  obtain ⟨k, hk⟩ := cube_root_cases hc03
  set j0 : I3 := -k
  set l0 : ℂ := star (u 0) with hl0
  have hl0n : Complex.normSq l0 = 1 := by simp [hl0, hu 0]
  have hjk : ω ^ j0.val * c 0 = 1 := by rw [hk]; exact ω_neg_mul k
  have hu' : (fun t : I3 => l0 * ω ^ (t.val * j0.val) * u t) = uCan ζ := by
    funext t
    fin_cases t
    · simp only [uCan, hl0, Fin.zero_eta, Fin.val_zero, zero_mul, pow_zero, mul_one,
        Matrix.cons_val_zero]
      exact huu 0
    · simp only [uCan, Fin.mk_one, Fin.val_one, one_mul, Matrix.cons_val_one,
        Matrix.cons_val_zero]
      rw [← hjk]; simp only [hc, hl0, show (0 : I3) + 1 = 1 from rfl]; ring
    · simp only [uCan, Fin.reduceFinMk, Fin.val_two, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons]
      have h01 : c 0 * c 1 = star (u 0) * u 2 := by
        simp only [hc, show (0 : I3) + 1 = 1 from rfl, show (1 : I3) + 1 = 2 from rfl]
        linear_combination (star (u 0) * u 2) * huu 1
      calc l0 * ω ^ (2 * j0.val) * u 2 = ω ^ (2 * j0.val) * (c 0 * c 1) := by
            rw [h01, hl0]; ring
        _ = (ω ^ j0.val * c 0) ^ 2 * ζ := by rw [hc1]; ring
        _ = ζ := by rw [hjk]; ring
  have hv' : (fun t : I3 => l0 * ω ^ (t.val * j0.val) * v t) =
      fun t => Complex.I * uCan ζ t := by
    funext t; rw [← hu', hvI]; ring
  have hE := tripleEquiv_std_colK (H := symH x) (K := symK y u v)
    (isMonomial_colOpK (l₀ := l0) (l₁ := 1) j0 0 hl0n (by simp))
  rw [symK_mul_colOpK y u v j0 0 1 hl0n, hu', hv'] at hE
  refine ⟨_, fun t => by simp [Complex.normSq_mul, hl0n, normSq_ω_pow, hy t], ?_, hE⟩
  -- transport of the `w`-pattern
  have hz : ∀ t, zvec x (fun t => 1 * star l0 * ω ^ (t.val * (0 : I3).val) *
      ω ^ (2 * (t.val * j0.val)) * y t) (uCan ζ) (fun t => Complex.I * uCan ζ t) t =
      l0 * ω ^ (t.val * (4 * j0.val)) * zvec x y u v t := by
    intro t
    have e1 := congrFun hu' t
    simp only [zvec, Fin.val_zero, mul_zero, pow_zero, mul_one, one_mul]
    rw [← e1, hvI]
    have hll := mul_star_self_of_normSq hl0n
    rw [show t.val * (4 * j0.val) = 2 * (t.val * j0.val) + t.val * j0.val + t.val * j0.val by ring,
      pow_add, pow_add]
    linear_combination (-(star (x t) * y t * u t * (Complex.I * u t) * l0 *
      ω ^ (2 * (t.val * j0.val)) * ω ^ (t.val * j0.val) * ω ^ (t.val * j0.val))) * hll
  have hw' := wvec_of_zvec hl0n (4 * j0.val) hz
  have := hw.smul (star (ω ^ (4 * j0.val)))
  simp only [WPattern] at this ⊢
  rw [hw' 0, hw' 1, hw' 2]
  exact this

/-! ### Step 3: `x = y = 1` -/

lemma ζ_facts {ζ : ℂ} (hζ : ζ = ω ∨ ζ = ω ^ 2) :
    Complex.normSq ζ = 1 ∧ star ζ = ζ ^ 2 ∧ ζ + star ζ = -1 ∧ ζ - star ζ ≠ 0 := by
  have hs3 : Real.sqrt 3 ≠ 0 := by positivity
  rcases hζ with rfl | rfl
  · refine ⟨normSq_ω, star_ω, by rw [star_ω]; linear_combination ω_sq_add, ?_⟩
    intro h; have := congrArg Complex.im h; simp at this
  · refine ⟨by rw [map_pow, normSq_ω, one_pow], by rw [star_pow, star_ω, ← pow_mul, ω_sq_sq.symm.trans
      (by rw [← pow_mul])], ?_, ?_⟩
    · rw [star_pow, star_ω, ω_sq_sq]; linear_combination ω_sq_add
    · intro h; have := congrArg Complex.im h
      rw [Complex.sub_im, star_pow, star_ω, ω_sq_sq, ω_sq_im, ω_im, Complex.zero_im] at this
      exact hs3 (by linarith)

lemma unitVec_uCan {ζ : ℂ} (hζ : ζ = ω ∨ ζ = ω ^ 2) : UnitVec (uCan ζ) := by
  intro t; fin_cases t <;> simp [uCan, (ζ_facts hζ).1]

lemma unitVec_I_mul {u : I3 → ℂ} (hu : UnitVec u) : UnitVec (fun t => Complex.I * u t) := by
  intro t; simp [Complex.normSq_mul, hu t]

lemma star_I : star Complex.I = -Complex.I := Complex.conj_I

lemma star_one_sub_I : star (1 - Complex.I) * (1 - Complex.I) = 2 := by
  simp only [star_sub, star_one, Complex.star_def, Complex.conj_I]
  ring_nf; rw [Complex.I_sq]; ring

/-- A geometric unit vector `x₀ αᵗ` (`α³ = 1`) is gauged to `1`. -/
lemma geometric_to_one {x : I3 → ℂ} (hx : UnitVec x) {α : ℂ} (h1 : x 1 = x 0 * α)
    (h2 : x 2 = x 0 * α ^ 2) (hα : α ^ 3 = 1) :
    ∃ (j : I3) (l : ℂ), Complex.normSq l = 1 ∧
      (fun t : I3 => l * ω ^ (t.val * j.val) * x t) = 1 := by
  obtain ⟨k, hk⟩ := cube_root_cases hα
  refine ⟨-k, star (x 0), by simp [hx 0], ?_⟩
  have hxx := star_mul_self_of_normSq (hx 0)
  have hkk : ω ^ (-k).val * α = 1 := by rw [hk]; exact ω_neg_mul k
  funext t
  fin_cases t
  · simpa using hxx
  · simp only [Fin.mk_one, Fin.val_one, one_mul, Pi.one_apply]
    rw [h1]; linear_combination (ω ^ (-k).val * α) * hxx + hkk
  · simp only [Fin.reduceFinMk, Fin.val_two, Pi.one_apply]
    rw [h2, pow_mul]
    linear_combination ((ω ^ (-k).val) ^ 2 * α ^ 2) * hxx + (ω ^ (-k).val * α + 1) * hkk

/-- **Step 3.** -/
theorem step_xy {x y : I3 → ℂ} (hx : UnitVec x) (hy : UnitVec y) {ζ : ℂ}
    (hζ : ζ = ω ∨ ζ = ω ^ 2)
    (hT : IsMUBTriple (std (symH x) (symK y (uCan ζ) (fun t => Complex.I * uCan ζ t))))
    (hw : WPattern (wvec x y (uCan ζ) (fun t => Complex.I * uCan ζ t)) ζ) :
    TripleEquiv (std (symH x) (symK y (uCan ζ) (fun t => Complex.I * uCan ζ t)))
      (std (symH 1) (symK 1 (uCan ζ) (fun t => Complex.I * uCan ζ t))) := by
  obtain ⟨hζn, hζs, hζsum, hζne⟩ := ζ_facts hζ
  have hζ3 := ζ_cube hζ
  have hu := unitVec_uCan hζ
  have hv := unitVec_I_mul hu
  obtain ⟨-, fm, fxm, -⟩ := (isMUBTriple_sym_iff hx hy hu hv).1 hT
  have Ey0 := ((flat_iff _).1 fm).2
  have Ex0 := ((flat_iff _).1 fxm).2
  have h2 := star_one_sub_I
  have hxx : ∀ t, star (x t) * x t = 1 := fun t => star_mul_self_of_normSq (hx t)
  have hyy : ∀ t, star (y t) * y t = 1 := fun t => star_mul_self_of_normSq (hy t)
  have hζζ : star ζ * ζ = 1 := star_mul_self_of_normSq hζn
  -- the autocorrelation equations
  have Ey : star (y 0) * y 1 + ζ * (star (y 1) * y 2) + star ζ * (star (y 2) * y 0) = 0 := by
    simp only [autoc, Pi.mul_apply, Pi.sub_apply, uCan, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, star_mul', star_sub] at Ey0
    have : (2 : ℂ) * (star (y 0) * y 1 + ζ * (star (y 1) * y 2) + star ζ * (star (y 2) * y 0)) = 0 := by
      rw [← Ey0, ← h2]; simp only [star_one, star_mul', star_sub, Complex.star_def, Complex.conj_I]
      ring
    simpa using this
  have Ex : x 0 * star (x 1) + ζ * (x 1 * star (x 2)) + star ζ * (x 2 * star (x 0)) = 0 := by
    simp only [autoc, Pi.mul_apply, Pi.sub_apply, Pi.star_apply, uCan, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, star_mul',
      star_sub, star_star] at Ex0
    have : (2 : ℂ) * (x 0 * star (x 1) + ζ * (x 1 * star (x 2)) + star ζ * (x 2 * star (x 0))) = 0 := by
      rw [← Ex0, ← h2]; simp only [star_one, star_mul', star_sub, Complex.star_def, Complex.conj_I]
      ring
    simpa using this
  have W1 := hw.1
  have W2 := hw.2
  simp only [wvec, zvec, uCan, show (0 : I3) + 1 = 1 from rfl, show (1 : I3) + 1 = 2 from rfl,
    show (2 : I3) + 1 = 0 from rfl, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, star_neg, star_mul', star_one,
    star_I, star_star, mul_one] at W1 W2
  have hI := Complex.I_sq
  have W1' : star (x 1) * x 2 * (y 1 * star (y 2)) = star (x 0) * x 1 * (y 0 * star (y 1)) := by
    linear_combination ζ ^ 2 * W1 +
      (star (x 1) * x 2 * y 1 * star (y 2) * ζ ^ 2 * star ζ ^ 2 -
        star (x 0) * y 0 * x 1 * star (y 1) * ζ ^ 3) * hI -
      star (x 1) * x 2 * y 1 * star (y 2) * (star ζ * ζ + 1) * hζζ +
      star (x 0) * y 0 * x 1 * star (y 1) * hζ3
  have W2' : star (x 2) * x 0 * (y 2 * star (y 0)) = star (x 0) * x 1 * (y 0 * star (y 1)) := by
    linear_combination ζ * W2 +
      (star (x 2) * x 0 * y 2 * star (y 0) - star (x 0) * y 0 * x 1 * star (y 1)) * ζ ^ 3 * hI -
      (star (x 2) * x 0 * y 2 * star (y 0) - star (x 0) * y 0 * x 1 * star (y 1)) * hζ3
  -- `x̄ₜ xₜ₊₁ = κ ȳₜ yₜ₊₁`
  set κ := star (x 0) * x 1 * (y 0 * star (y 1)) with hκ
  have hyy' : ∀ t, y t * star (y t) = 1 := fun t => mul_star_self_of_normSq (hy t)
  have hxx' : ∀ t, x t * star (x t) = 1 := fun t => mul_star_self_of_normSq (hx t)
  have k0 : star (x 0) * x 1 = κ * (star (y 0) * y 1) := by
    rw [hκ]; linear_combination (-(star (x 0) * x 1)) * (star (y 1) * y 1 * hyy 0 + hyy 1)
  have k1 : star (x 1) * x 2 = κ * (star (y 1) * y 2) := by
    rw [← W1']
    linear_combination (-(star (x 1) * x 2)) * (star (y 2) * y 2 * hyy' 1 + hyy 2)
  have k2 : star (x 2) * x 0 = κ * (star (y 2) * y 0) := by
    rw [← W2']
    linear_combination (-(star (x 2) * x 0)) * (star (y 0) * y 0 * hyy' 2 + hyy 0)
  have hconj : star (x 0) * x 1 + star ζ * (star (x 1) * x 2) + ζ * (star (x 2) * x 0) = 0 := by
    have := congrArg star Ex
    simp only [star_add, star_mul', star_star, star_zero] at this
    linear_combination this
  have hκn : Complex.normSq κ = 1 := by
    simp [hκ, Complex.normSq_mul, hx 0, hx 1, hy 0, hy 1]
  have hκ0 : κ ≠ 0 := ne_zero_of_normSq hκn
  have E2 : star (y 0) * y 1 + star ζ * (star (y 1) * y 2) + ζ * (star (y 2) * y 0) = 0 := by
    apply mul_left_cancel₀ hκ0
    linear_combination hconj - k0 - star ζ * k1 - ζ * k2
  have hb12 : star (y 1) * y 2 = star (y 2) * y 0 := by
    have : (ζ - star ζ) * (star (y 1) * y 2 - star (y 2) * y 0) = 0 := by
      linear_combination Ey - E2
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hζne)
  have hb01 : star (y 0) * y 1 = star (y 1) * y 2 := by
    linear_combination Ey - (star (y 1) * y 2) * hζsum + star ζ * hb12
  -- `y` and `x` are geometric
  set β := star (y 0) * y 1 with hβ
  have hy1 : y 1 = y 0 * β := by rw [hβ]; linear_combination (-(y 1)) * hyy' 0
  have hy2 : y 2 = y 0 * β ^ 2 := by
    have : y 2 = y 1 * (star (y 1) * y 2) := by linear_combination (-(y 2)) * hyy' 1
    rw [this, ← hb01, hy1]; ring
  have hβ3 : β ^ 3 = 1 := by
    calc β ^ 3 = (star (y 0) * y 1) * (star (y 1) * y 2) * (star (y 2) * y 0) := by
          rw [← hb01, ← hb12, ← hb01]; ring
      _ = 1 := by
          linear_combination (star (y 0) * y 0 * (star (y 1) * y 1)) * hyy 2 +
            star (y 0) * y 0 * hyy 1 + hyy 0
  set α := star (x 0) * x 1 with hα
  have ha1 : star (x 1) * x 2 = α := by rw [k1, ← hb01, k0]
  have ha2 : star (x 2) * x 0 = α := by rw [k2, ← hb12, ← hb01, k0]
  have hx1 : x 1 = x 0 * α := by rw [hα]; linear_combination (-(x 1)) * hxx' 0
  have hx2 : x 2 = x 0 * α ^ 2 := by
    have : x 2 = x 1 * (star (x 1) * x 2) := by linear_combination (-(x 2)) * hxx' 1
    rw [this, ha1, hx1]; ring
  have hα3 : α ^ 3 = 1 := by
    calc α ^ 3 = (star (x 0) * x 1) * (star (x 1) * x 2) * (star (x 2) * x 0) := by
          rw [ha1, ha2]; ring
      _ = 1 := by
          linear_combination (star (x 0) * x 0 * (star (x 1) * x 1)) * hxx 2 +
            star (x 0) * x 0 * hxx 1 + hxx 0
  obtain ⟨jx, lx, hlx, hxe⟩ := geometric_to_one hx hx1 hx2 hα3
  obtain ⟨jy, ly, hly, hye⟩ := geometric_to_one hy hy1 hy2 hβ3
  have hE1 := tripleEquiv_std_colH (H := symH x)
    (K := symK y (uCan ζ) (fun t => Complex.I * uCan ζ t)) (isMonomial_colOpH jx hlx)
  rw [symH_mul_colOpH, hxe] at hE1
  have hE2 := tripleEquiv_std_colK (H := symH 1)
    (K := symK y (uCan ζ) (fun t => Complex.I * uCan ζ t))
    (isMonomial_colOpK (l₀ := 1) (l₁ := ly) 0 jy (by simp) hly)
  rw [symK_mul_colOpK_orbit1, hye] at hE2
  exact tripleEquiv_trans hE1 hE2

/-! ### Step 4: the two canonical forms -/

lemma uCan_ω_shift : (fun t : I3 => 1 * ω ^ (t.val * (2 : I3).val) * uCan ω t) = isoVec := by
  funext t; fin_cases t <;> simp [uCan, isoVec, ω_pow_reduce, ← pow_add] <;> ring_nf <;>
    simp [ω_pow_reduce]

/-- `ζ = ω`: a cyclic relabelling of both `K`-orbits gives the isolated triple. -/
theorem canonical_ω :
    TripleEquiv (std (symH 1) (symK 1 (uCan ω) (fun t => Complex.I * uCan ω t)))
      isolatedTriple := by
  have hE := tripleEquiv_std_colK (H := symH 1)
    (K := symK 1 (uCan ω) (fun t => Complex.I * uCan ω t))
    (isMonomial_colOpK (l₀ := 1) (l₁ := 1) 2 2 (by simp) (by simp))
  rw [symK_mul_colOpK _ _ _ 2 2 1 (by simp)] at hE
  have hy : (fun t : I3 => (1 : ℂ) * star 1 * ω ^ (t.val * (2 : I3).val) *
      ω ^ (2 * (t.val * (2 : I3).val)) * (1 : I3 → ℂ) t) = 1 := by
    funext t; fin_cases t <;> simp [ω_pow_reduce] <;> linear_combination ω_cube
  have hv : (fun t : I3 => 1 * ω ^ (t.val * (2 : I3).val) * (Complex.I * uCan ω t)) =
      Complex.I • isoVec := by
    rw [← uCan_ω_shift]; funext t; simp; ring
  rw [hy, uCan_ω_shift, hv] at hE
  rw [isolatedTriple, isoK_eq]; exact hE

/-! #### `ζ = ω²`: the product equivalence (SM Eq. `tc-product-equivalence`) -/

/-- `g₊ = (1, ω, ω) = (ω^{t²})`. -/
noncomputable def gPlus : I3 → ℂ := ![1, ω, ω]

lemma unitVec_gPlus : UnitVec gPlus := by
  intro t; fin_cases t <;> simp [gPlus, normSq_ω]

lemma canonical_ω2_to_plus :
    TripleEquiv (std (symH 1) (symK 1 (uCan (ω ^ 2)) (fun t => Complex.I * uCan (ω ^ 2) t)))
      (std (symH 1) (symK 1 gPlus (fun t => Complex.I * gPlus t))) := by
  have hE := tripleEquiv_std_colK (H := symH 1)
    (K := symK 1 (uCan (ω ^ 2)) (fun t => Complex.I * uCan (ω ^ 2) t))
    (isMonomial_colOpK (l₀ := 1) (l₁ := 1) 1 1 (by simp) (by simp))
  rw [symK_mul_colOpK _ _ _ 1 1 1 (by simp)] at hE
  have hu : (fun t : I3 => 1 * ω ^ (t.val * (1 : I3).val) * uCan (ω ^ 2) t) = gPlus := by
    funext t; fin_cases t <;> simp [uCan, gPlus, ω_pow_reduce, ← pow_add]
  have hy : (fun t : I3 => (1 : ℂ) * star 1 * ω ^ (t.val * (1 : I3).val) *
      ω ^ (2 * (t.val * (1 : I3).val)) * (1 : I3 → ℂ) t) = 1 := by
    funext t; fin_cases t <;> simp [ω_pow_reduce] <;> linear_combination ω_cube
  have hv : (fun t : I3 => 1 * ω ^ (t.val * (1 : I3).val) * (Complex.I * uCan (ω ^ 2) t)) =
      fun t => Complex.I * gPlus t := by
    rw [← hu]; funext t; ring
  rw [hy, hu, hv] at hE
  exact hE

/-- Negation of the position inside each column orbit. -/
def negPerm : Equiv.Perm I6 := Equiv.sumCongr (Equiv.neg I3) (Equiv.neg I3)

lemma ω_sq_neg_pow (s t : I3) : (ω ^ 2) ^ ((-s).val * t.val) = ω ^ (t.val * s.val) := by
  rw [← pow_mul, ω_pow_mod, ω_pow_mod (t.val * s.val)]
  congr 1
  fin_cases s <;> fin_cases t <;> decide

lemma symH_one_conjTranspose_mul :
    (symH 1)ᴴ * monomial negPerm (fun _ => 1) = symH 1 := by
  ext i j
  rw [mul_monomial_apply, conjTranspose_apply]
  rcases i with t | t <;> rcases j with s | s <;>
    simp [symH, negPerm, conj_ω, ω_sq_neg_pow, diagonal_mul]

lemma one_add_two_ω : 1 + 2 * ω = Complex.I * (Real.sqrt 3 : ℂ) := by
  apply Complex.ext <;> simp <;> ring

@[simp] lemma neg_one_val3 : (-1 : I3).val = 2 := rfl
@[simp] lemma neg_two_val3 : (-2 : I3).val = 1 := rfl

lemma circ_gPlus (r s : I3) :
    circ gPlus r (-s) = (1 + 2 * ω) * isoVec r * ω ^ (r.val * s.val) * isoVec s := by
  rw [circ_apply]
  fin_cases r <;> fin_cases s <;>
    simp [gPlus, isoVec, Fin.sum_univ_three] <;> ω_norm

/-- `1/√2`. -/
noncomputable def s2 : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

lemma two_s2_sqrt3 : 2 * s2 * (Real.sqrt 3 : ℂ) = t6 := by
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have h6 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2i : (2 : ℝ) * (Real.sqrt 2)⁻¹ = Real.sqrt 2 := by
    calc (2 : ℝ) * (Real.sqrt 2)⁻¹ = Real.sqrt 2 * Real.sqrt 2 * (Real.sqrt 2)⁻¹ := by rw [h22]
      _ = Real.sqrt 2 := by rw [mul_assoc, mul_inv_cancel₀ h2, mul_one]
  have hr : (2 : ℝ) * (Real.sqrt 2)⁻¹ * Real.sqrt 3 = Real.sqrt 6 := by rw [h2i, h6]
  simp only [s2, t6]
  exact_mod_cast hr

lemma normSq_s2 : Complex.normSq s2 = 1 / 2 := by
  rw [s2, Complex.normSq_ofReal, ← mul_inv, Real.mul_self_sqrt (by norm_num)]; norm_num

/-- `(1 - i)/√2` and `(1 + i)/√2`. -/
noncomputable def qm : ℂ := (1 - Complex.I) * s2
noncomputable def qp : ℂ := (1 + Complex.I) * s2

lemma normSq_qm : Complex.normSq qm = 1 := by
  rw [qm, Complex.normSq_mul, normSq_s2, Complex.normSq_apply]; simp; norm_num

lemma normSq_qp : Complex.normSq qp = 1 := by
  rw [qp, Complex.normSq_mul, normSq_s2, Complex.normSq_apply]; simp; norm_num

lemma scal1 : (1 - Complex.I) * qm * (1 + 2 * ω) = t6 := by
  rw [qm, one_add_two_ω, ← two_s2_sqrt3]
  linear_combination (s2 * (Real.sqrt 3 : ℂ) * (Complex.I - 2)) * Complex.I_sq

lemma scal2 : (1 + Complex.I) * qm * (1 + 2 * ω) = Complex.I * t6 := by
  rw [qm, one_add_two_ω, ← two_s2_sqrt3]
  linear_combination (-(Complex.I * s2 * (Real.sqrt 3 : ℂ))) * Complex.I_sq

lemma scal3 : (1 + Complex.I) * (-qp) * (1 + 2 * ω) = t6 := by
  rw [qp, one_add_two_ω, ← two_s2_sqrt3]
  linear_combination (-(s2 * (Real.sqrt 3 : ℂ) * (Complex.I + 2))) * Complex.I_sq

lemma scal4 : (1 - Complex.I) * (-qp) * (1 + 2 * ω) = -(Complex.I * t6) := by
  rw [qp, one_add_two_ω, ← two_s2_sqrt3]
  linear_combination (Complex.I * s2 * (Real.sqrt 3 : ℂ)) * Complex.I_sq

/-- Exchange the two column orbits and negate the position. -/
def swapNeg : Equiv.Perm I6 := (Equiv.sumComm I3 I3).trans negPerm

/-- Column phases of the product equivalence. -/
noncomputable def c2 : I6 → ℂ
  | Sum.inl s => qm * star (isoVec s)
  | Sum.inr s => -(qp * star (isoVec s))

noncomputable def M2 : Mat6 := monomial swapNeg c2

lemma isMonomial_M2 : IsMonomial M2 :=
  ⟨_, _, fun j => by
    rcases j with s | s <;>
      simp [c2, Complex.normSq_mul, normSq_qm, normSq_qp, unitVec_isoVec s], rfl⟩

lemma isoG_apply (r s : I3) : isoG r s = isoVec r * ω ^ (r.val * s.val) := by
  simp [isoG, isoVec, diagonal_mul]

lemma key_M2 :
    (symH 1)ᴴ * symK 1 gPlus (fun t => Complex.I * gPlus t) * M2 = t6 • isoK := by
  have e1 : gPlus + (fun t => Complex.I * gPlus t) = (1 + Complex.I) • gPlus := by
    funext t; simp; ring
  have e2 : (gPlus - fun t => Complex.I * gPlus t) * 1 = (1 - Complex.I) • gPlus := by
    funext t; simp; ring
  have e3 : star (1 : I3 → ℂ) * (gPlus - fun t => Complex.I * gPlus t) =
      (1 - Complex.I) • gPlus := by
    funext t; simp; ring
  have e4 : star (1 : I3 → ℂ) * (gPlus + fun t => Complex.I * gPlus t) * 1 =
      (1 + Complex.I) • gPlus := by
    funext t; simp; ring
  rw [symH_conjTranspose_mul_symK, e4, e1, e2, e3]
  ext i j
  rw [M2, mul_monomial_apply]
  have hv : ∀ s, isoVec s * star (isoVec s) = 1 := fun s => mul_star_self_of_normSq (unitVec_isoVec s)
  rcases i with r | r <;> rcases j with s | s
  · simp only [swapNeg, negPerm, Equiv.trans_apply, Equiv.sumComm_apply, Sum.swap_inl,
      Equiv.sumCongr_apply, Sum.map_inr, Equiv.neg_apply, fromBlocks_apply₁₂, c2, circ_smul,
      Matrix.smul_apply, smul_eq_mul, circ_gPlus, isoK, fromBlocks_apply₁₁, isoG_apply]
    rw [← scal1]; linear_combination ((1 - Complex.I) * qm * (1 + 2 * ω)) * isoVec r *
      ω ^ (r.val * s.val) * hv s
  · simp only [swapNeg, negPerm, Equiv.trans_apply, Equiv.sumComm_apply, Sum.swap_inr,
      Equiv.sumCongr_apply, Sum.map_inl, Equiv.neg_apply, fromBlocks_apply₁₁, c2, circ_smul,
      Matrix.smul_apply, smul_eq_mul, circ_gPlus, isoK, fromBlocks_apply₁₂, isoG_apply]
    rw [← scal3]; linear_combination ((1 + Complex.I) * (-qp) * (1 + 2 * ω)) * isoVec r *
      ω ^ (r.val * s.val) * hv s
  · simp only [swapNeg, negPerm, Equiv.trans_apply, Equiv.sumComm_apply, Sum.swap_inl,
      Equiv.sumCongr_apply, Sum.map_inr, Equiv.neg_apply, fromBlocks_apply₂₂, c2, circ_smul,
      Matrix.smul_apply, smul_eq_mul, circ_gPlus, isoK, fromBlocks_apply₂₁, isoG_apply]
    rw [show t6 * (Complex.I * (isoVec r * ω ^ (r.val * s.val))) =
      (Complex.I * t6) * (isoVec r * ω ^ (r.val * s.val)) by ring, ← scal2]
    linear_combination ((1 + Complex.I) * qm * (1 + 2 * ω)) * isoVec r *
      ω ^ (r.val * s.val) * hv s
  · simp only [swapNeg, negPerm, Equiv.trans_apply, Equiv.sumComm_apply, Sum.swap_inr,
      Equiv.sumCongr_apply, Sum.map_inl, Equiv.neg_apply, fromBlocks_apply₂₁, c2, circ_smul,
      Matrix.smul_apply, smul_eq_mul, circ_gPlus, isoK, fromBlocks_apply₂₂, isoG_apply,
      Matrix.neg_apply]
    rw [show t6 * -(Complex.I * (isoVec r * ω ^ (r.val * s.val))) =
      (-(Complex.I * t6)) * (isoVec r * ω ^ (r.val * s.val)) by ring, ← scal4]
    linear_combination ((1 - Complex.I) * (-qp) * (1 + 2 * ω)) * isoVec r *
      ω ^ (r.val * s.val) * hv s

/-- **Product equivalence.**  The common unitary `(F₂ ⊗ F₃)ᴴ/√6` and the exchange of the first
two bases relate the `ζ = ω²` canonical triple to the isolated triple. -/
theorem plus_to_isolated :
    TripleEquiv (std (symH 1) (symK 1 gPlus (fun t => Complex.I * gPlus t))) isolatedTriple := by
  have hH : Hadamard6.IsHadamard (symH 1) := symH_isHadamard unitVec_one
  have hU : IsUnitary (s6 • symH 1) := (isUnitary_s6_smul_iff _).2 hH.2
  have hWs : (s6 • symH 1)ᴴ = s6 • (symH 1)ᴴ := by rw [conjTranspose_smul, s6_star]
  refine ⟨(s6 • symH 1)ᴴ, Equiv.swap 0 1, ![1, monomial negPerm (fun _ => 1), M2],
    hU.conjTranspose, fun k => ?_, fun k => ?_⟩
  · fin_cases k
    · exact isMonomial_one
    · exact ⟨negPerm, _, fun _ => by simp, rfl⟩
    · exact isMonomial_M2
  · fin_cases k
    · show (1 : Mat6) = (s6 • symH 1)ᴴ * std (symH 1) _ ((Equiv.swap (0 : Fin 3) 1) 0) * 1
      rw [Equiv.swap_apply_left, Matrix.mul_one]; exact hU.2.symm
    · show s6 • symH 1 = (s6 • symH 1)ᴴ * std (symH 1) _ ((Equiv.swap (0 : Fin 3) 1) 1) *
        monomial negPerm (fun _ => 1)
      rw [Equiv.swap_apply_right, std_zero, Matrix.mul_one, hWs, Matrix.smul_mul,
        symH_one_conjTranspose_mul]
    · show s6 • isoK = (s6 • symH 1)ᴴ * std (symH 1) _ ((Equiv.swap (0 : Fin 3) 1) 2) * M2
      rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide), std_two, hWs, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, key_M2, smul_smul, smul_smul,
        mul_assoc, s6_mul_t6, mul_one]

/-- **The isolated case of the recognition.** -/
theorem isolatedRecognition : IsolatedRecognition := by
  intro x y u v hx hy hu hv hT hD
  obtain ⟨ζ, hζ, hP, hA, hw⟩ := (isolatedData_iff x y u v).1 hD
  obtain ⟨x1, y1, u1, v1, hx1, hy1, hu1, hv1, hvI, hA1, hw1, hE1⟩ :=
    step_v_eq_i hx hy hu hv hP hA hw
  obtain ⟨y2, hy2, hw2, hE2⟩ := step_u_canonical hy1 hu1 hvI hζ hA1 hw1
  have hT2 := isMUBTriple_of_tripleEquiv (tripleEquiv_trans hE1 hE2) hT
  have hE3 := step_xy hx1 hy2 hζ hT2 hw2
  have hE4 : TripleEquiv (std (symH 1) (symK 1 (uCan ζ) (fun t => Complex.I * uCan ζ t)))
      isolatedTriple := by
    rcases hζ with rfl | rfl
    · exact canonical_ω
    · exact tripleEquiv_trans canonical_ω2_to_plus plus_to_isolated
  exact tripleEquiv_trans hE1 (tripleEquiv_trans hE2 (tripleEquiv_trans hE3 hE4))

/-- **Algebraic recognition of the symmetric triples** (SM §"Algebraic recognition"):
every MUB triple with an order-three symmetry is equivalent to a member of the continuous
family or to the isolated Fourier triple. -/
theorem symmetricRecognition : SymmetricRecognition :=
  symmetricRecognition_of_isolated isolatedRecognition

end MUBTriples
