import MUBTriples.Assembly

/-!
# `Γ_F` is the paper's score (SM Eq. `gamma-score`)

`Score.lean` defines `ΓF` through a symmetric encoding that makes the invariance proofs
short: the plaquette sum runs over *all* ordered quadruples `(i, k, j, l)` and is divided
by `4`, the labels are bijections `I6 ≃ ZMod 6` without the normalization `a₁ = b₁ = 0`,
and `dist_{2π}` is written as `|arg|`.  Here we define the paper's formula literally,
`ΓFpaper`, on real phase arrays `Q : Fin 6 → Fin 6 → ℝ` (the paper's rows and columns
`1, …, 6` are `0, …, 5`), and prove that the two agree.

Paper (arXiv:2611.06917, SM §"Patterns and the triple equations", Eq. `gamma-score`):

`Γ_F(e^{iQ}) = (1/15) min_{a,b} ‖dist_{2π}(RQ − (π/3) v(a,b))‖₂`,

* `(RQ)_{ik;jl} = Q_ij + Q_kl − Q_il − Q_kj` for `i < k`, `j < l` (`225` plaquettes);
* `v(a,b)_{ik;jl} = (a_i − a_k)(b_j − b_l)`;
* `a, b` range over the permutations of the labels `0, …, 5` assigned to the six rows and
  the six columns, with `a₁ = b₁ = 0`;
* `dist_{2π}` takes the distance of each entry to `2πℤ`.

## Main results

* `ΓF_exp_eq_ΓFpaper`: for every real phase array `Q` and all enumerations `e`, `f` of the
  rows and columns, `ΓF (e^{iQ}) = ΓFpaper Q`;
* `ΓF_eq_ΓFpaper`, `ΓF_eq_ΓFpaper_phaseArray`: for every matrix with unimodular entries,
  `ΓF H = ΓFpaper (arg H)`;
* `ΓFpaper_congr`: the paper's score of `e^{iQ}` does not depend on the choice of `Q`;
* `minTransition_iff_paper`: for a MUB triple `{I₆, H/√6, K/√6}`, the hypothesis
  `MinTransition H K` used in (H2) of `TripleCertificate` is exactly SM
  Eq. `minimum-transition` with the paper's `Γ_F`;
* `classified_of_paper`: (H2) with the paper's literal score implies (H2) as stated.
-/

open Matrix Hadamard6
open scoped Real

namespace MUBTriples

/-! ### The paper's definition -/

/-- `dist_{2π}(x)`: the distance from `x` to `2πℤ`. -/
noncomputable def dist2pi (x : ℝ) : ℝ :=
  Metric.infDist x (Set.range fun n : ℤ => 2 * π * n)

/-- The plaquette difference `(RQ)_{ik;jl} = Q_ij + Q_kl − Q_il − Q_kj`. -/
def plaqDiff (Q : Fin 6 → Fin 6 → ℝ) (i k j l : Fin 6) : ℝ :=
  Q i j + Q k l - Q i l - Q k j

/-- `v(a,b)_{ik;jl} = (a_i − a_k)(b_j − b_l)` for integer labels `a`, `b`. -/
def vLabel (a b : Fin 6 → ℤ) (i k j l : Fin 6) : ℤ :=
  (a i - a k) * (b j - b l)

/-- The `15` index pairs `i < k`. -/
def pairsLT : Finset (Fin 6 × Fin 6) :=
  Finset.univ.filter fun p => p.1 < p.2

/-- `‖dist_{2π}(RQ − (π/3) v(a,b))‖₂`: the Euclidean norm over the `225` plaquettes
`i < k`, `j < l`. -/
noncomputable def alignNorm (Q : Fin 6 → Fin 6 → ℝ) (a b : Fin 6 → ℤ) : ℝ :=
  Real.sqrt (∑ p ∈ pairsLT, ∑ q ∈ pairsLT,
    dist2pi (plaqDiff Q p.1 p.2 q.1 q.2 - π / 3 * vLabel a b p.1 p.2 q.1 q.2) ^ 2)

/-- The integer values of a labelling of the six rows (or columns) by `0, …, 5`. -/
def labelVal (a : Equiv.Perm (Fin 6)) (i : Fin 6) : ℤ := ((a i : ℕ) : ℤ)

/-- The admissible labellings of the six rows (or columns): permutations `a` of the labels
`0, …, 5` with `a₁ = 0` (the first row or column is index `0 : Fin 6`). -/
abbrev Labelling := {a : Equiv.Perm (Fin 6) // a 0 = 0}

instance : Nonempty Labelling := ⟨⟨1, rfl⟩⟩

/-- **SM Eq. `gamma-score`**, literally:
`Γ_F(e^{iQ}) = (1/15) min_{a,b} ‖dist_{2π}(RQ − (π/3) v(a,b))‖₂`, the minimum over
permutations `a, b` of `0, …, 5` with `a₁ = b₁ = 0` (`120² = 14,400` label pairs). -/
noncomputable def ΓFpaper (Q : Fin 6 → Fin 6 → ℝ) : ℝ :=
  (1 / 15) * Finset.univ.inf' Finset.univ_nonempty
    fun p : Labelling × Labelling => alignNorm Q (labelVal p.1) (labelVal p.2)

/-- The matrix `e^{iQ}`, rows and columns of `Mat6` enumerated by `e` and `f`. -/
noncomputable def expMat (Q : Fin 6 → Fin 6 → ℝ) (e f : I6 ≃ Fin 6) : Mat6 :=
  Matrix.of fun r c => Complex.exp ((Q (e r) (f c) : ℂ) * Complex.I)

/-- The standard enumeration `inl 0, inl 1, inl 2, inr 0, inr 1, inr 2 ↦ 0, …, 5` of the
rows and columns of `Mat6` (block form `[[E, B], [C, D]]`). -/
def stdIdx : I6 ≃ Fin 6 := finSumFinEquiv

/-- The phase array `Q = arg H` of `H`, in the standard enumeration. -/
noncomputable def phaseArray (H : Mat6) : Fin 6 → Fin 6 → ℝ :=
  fun i j => Complex.arg (H (stdIdx.symm i) (stdIdx.symm j))

/-! ### `dist_{2π}` -/

/-- `dist_{2π}(x) = |arg e^{ix}|`. -/
lemma dist2pi_eq_abs_arg (x : ℝ) :
    dist2pi x = |Complex.arg (Complex.exp (x * Complex.I))| := by
  rw [Complex.arg_exp_mul_I]
  set y := toIocMod Real.two_pi_pos (-π) x with hy
  have hmem : y ∈ Set.Ioc (-π) (-π + 2 * π) := toIocMod_mem_Ioc _ _ _
  obtain ⟨h1, h2⟩ := hmem
  have hyabs : |y| ≤ π := abs_le.2 ⟨h1.le, by linarith⟩
  set n := toIocDiv Real.two_pi_pos (-π) x
  have hxy : x - y = n * (2 * π) := self_sub_toIocMod_eq_mul _ _ _
  apply le_antisymm
  · calc dist2pi x ≤ dist x (2 * π * n) := Metric.infDist_le_dist_of_mem ⟨n, rfl⟩
      _ = |y| := by rw [Real.dist_eq]; congr 1; linarith
  · rw [dist2pi, Metric.le_infDist (Set.range_nonempty _)]
    rintro _ ⟨m, rfl⟩
    rw [Real.dist_eq]
    have hx : x - 2 * π * m = y + 2 * π * ((n : ℝ) - m) := by linarith
    rw [hx]
    rcases eq_or_ne n m with h | h
    · subst h; simp
    · have hk : (1 : ℝ) ≤ |(n : ℝ) - m| := by
        rw [← Int.cast_sub, ← Int.cast_abs]
        exact_mod_cast Int.one_le_abs (sub_ne_zero.2 h)
      have hpi := Real.pi_pos
      have h2pi : 2 * π ≤ |2 * π * ((n : ℝ) - m)| := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
        nlinarith
      have := abs_sub_abs_le_abs_sub (2 * π * ((n : ℝ) - m)) (-y)
      rw [abs_neg, sub_neg_eq_add, add_comm] at this
      linarith [abs_nonneg y]

lemma dist2pi_neg (x : ℝ) : dist2pi (-x) = dist2pi x := by
  rw [dist2pi_eq_abs_arg, dist2pi_eq_abs_arg]
  have : Complex.exp (((-x : ℝ) : ℂ) * Complex.I) =
      (starRingEnd ℂ) (Complex.exp ((x : ℂ) * Complex.I)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal]
  rw [this, Complex.arg_conj]
  split_ifs with h
  · rw [h]
  · rw [abs_neg]

lemma dist2pi_zero : dist2pi 0 = 0 :=
  Metric.infDist_zero_of_mem ⟨0, by simp⟩

/-- Labels only matter modulo `6`: `(π/3)·6 = 2π`. -/
lemma exp_sub_pi_div_three_mul (x : ℝ) {n m : ℤ} (h : (n : ZMod 6) = m) :
    Complex.exp (((x - π / 3 * n : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((x - π / 3 * m : ℝ) : ℂ) * Complex.I) := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  obtain ⟨t, ht⟩ := h
  have hm : (m : ℝ) = n + 6 * t := by
    have : m = n + 6 * t := by push_cast at ht; linarith
    exact_mod_cast this
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨t, ?_⟩
  rw [hm]
  push_cast
  ring

lemma dist2pi_congr_mod_six (x : ℝ) {n m : ℤ} (h : (n : ZMod 6) = m) :
    dist2pi (x - π / 3 * n) = dist2pi (x - π / 3 * m) := by
  rw [dist2pi_eq_abs_arg, dist2pi_eq_abs_arg, exp_sub_pi_div_three_mul x h]

/-! ### The plaquette terms -/

/-- The squared plaquette term `dist_{2π}((RQ)_{ik;jl} − (π/3) v(a,b)_{ik;jl})²`. -/
noncomputable def plaqTerm (Q : Fin 6 → Fin 6 → ℝ) (α β : Fin 6 → ℤ) (i k j l : Fin 6) : ℝ :=
  dist2pi (plaqDiff Q i k j l - π / 3 * vLabel α β i k j l) ^ 2

lemma plaqTerm_swap₁ (Q : Fin 6 → Fin 6 → ℝ) (α β : Fin 6 → ℤ) (i k j l : Fin 6) :
    plaqTerm Q α β k i j l = plaqTerm Q α β i k j l := by
  have : plaqDiff Q k i j l - π / 3 * vLabel α β k i j l =
      -(plaqDiff Q i k j l - π / 3 * vLabel α β i k j l) := by
    simp only [plaqDiff, vLabel]; push_cast; ring
  rw [plaqTerm, plaqTerm, this, dist2pi_neg]

lemma plaqTerm_swap₂ (Q : Fin 6 → Fin 6 → ℝ) (α β : Fin 6 → ℤ) (i k j l : Fin 6) :
    plaqTerm Q α β i k l j = plaqTerm Q α β i k j l := by
  have : plaqDiff Q i k l j - π / 3 * vLabel α β i k l j =
      -(plaqDiff Q i k j l - π / 3 * vLabel α β i k j l) := by
    simp only [plaqDiff, vLabel]; push_cast; ring
  rw [plaqTerm, plaqTerm, this, dist2pi_neg]

lemma plaqTerm_diag₁ (Q : Fin 6 → Fin 6 → ℝ) (α β : Fin 6 → ℤ) (i j l : Fin 6) :
    plaqTerm Q α β i i j l = 0 := by
  have : plaqDiff Q i i j l - π / 3 * vLabel α β i i j l = 0 := by
    simp only [plaqDiff, vLabel]; push_cast; ring
  rw [plaqTerm, this, dist2pi_zero]; norm_num

lemma plaqTerm_diag₂ (Q : Fin 6 → Fin 6 → ℝ) (α β : Fin 6 → ℤ) (i k j : Fin 6) :
    plaqTerm Q α β i k j j = 0 := by
  have : plaqDiff Q i k j j - π / 3 * vLabel α β i k j j = 0 := by
    simp only [plaqDiff, vLabel]; push_cast; ring
  rw [plaqTerm, this, dist2pi_zero]; norm_num

/-! ### Plaquettes of `e^{iQ}` -/

lemma star_exp_ofReal_mul_I (q : ℝ) :
    star (Complex.exp ((q : ℂ) * Complex.I)) = Complex.exp (-((q : ℂ) * Complex.I)) := by
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal]

lemma ζ6_pow (n : ℕ) : ζ6 ^ n = Complex.exp ((n : ℂ) * (((π / 3 : ℝ) : ℂ) * Complex.I)) := by
  rw [ζ6, Complex.exp_nat_mul]

lemma plaq_expMat (Q : Fin 6 → Fin 6 → ℝ) (e f : I6 ≃ Fin 6) (a b : I6 ≃ ZMod 6)
    (r s t u : I6) :
    plaq (expMat Q e f) a b r s t u =
      Complex.exp (((plaqDiff Q (e r) (e s) (f t) (f u) -
        π / 3 * ((((a r - a s) * (b t - b u)).val : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I) := by
  have hz : star (ζ6 ^ ((a r - a s) * (b t - b u)).val) =
      Complex.exp (-(((((((a r - a s) * (b t - b u)).val : ℕ) : ℝ) * (π / 3) : ℝ) : ℂ) *
        Complex.I)) := by
    rw [ζ6_pow, show ((((a r - a s) * (b t - b u)).val : ℕ) : ℂ) * (((π / 3 : ℝ) : ℂ) *
        Complex.I) = (((((a r - a s) * (b t - b u)).val : ℕ) : ℝ) * (π / 3) : ℝ) * Complex.I by
      push_cast; ring, star_exp_ofReal_mul_I]
  simp only [plaq, expMat, Matrix.of_apply, star_exp_ofReal_mul_I, hz, ← Complex.exp_add]
  congr 1
  simp only [plaqDiff, Int.cast_natCast]
  push_cast
  ring

/-- One plaquette term of `labelScore`, for labels congruent modulo `6` to integer
labels `α`, `β`. -/
lemma arg_plaq_expMat_sq (Q : Fin 6 → Fin 6 → ℝ) (e f : I6 ≃ Fin 6) (a b : I6 ≃ ZMod 6)
    (α β : Fin 6 → ℤ) (hα : ∀ i, (α i : ZMod 6) = a (e.symm i) - a (e.symm 0))
    (hβ : ∀ j, (β j : ZMod 6) = b (f.symm j) - b (f.symm 0)) (i k j l : Fin 6) :
    Complex.arg (plaq (expMat Q e f) a b (e.symm i) (e.symm k) (f.symm j) (f.symm l)) ^ 2 =
      plaqTerm Q α β i k j l := by
  rw [plaq_expMat, ← sq_abs, ← dist2pi_eq_abs_arg, plaqTerm]
  simp only [Equiv.apply_symm_apply]
  congr 1
  apply dist2pi_congr_mod_six
  rw [Int.cast_natCast, ZMod.natCast_zmod_val, vLabel]
  push_cast
  rw [hα, hα, hβ, hβ]
  ring

/-! ### From all ordered quadruples to `i < k`, `j < l` -/

lemma sum_sum_eq_two_mul_sum_pairsLT (h : Fin 6 → Fin 6 → ℝ) (hs : ∀ i k, h k i = h i k)
    (hd : ∀ i, h i i = 0) : ∑ i, ∑ k, h i k = 2 * ∑ p ∈ pairsLT, h p.1 p.2 := by
  have key : ∀ i k, h i k = (if i < k then h i k else 0) + (if k < i then h k i else 0) := by
    intro i k
    rcases lt_trichotomy i k with hik | rfl | hki
    · simp [hik, not_lt.2 hik.le]
    · simp [hd]
    · simp [hki, not_lt.2 hki.le, hs]
  have hlt : ∑ i, ∑ k, (if i < k then h i k else 0) = ∑ p ∈ pairsLT, h p.1 p.2 := by
    rw [pairsLT, Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]
  calc ∑ i, ∑ k, h i k
      = ∑ i, ∑ k, ((if i < k then h i k else 0) + (if k < i then h k i else 0)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => key i k
    _ = ∑ i, ∑ k, (if i < k then h i k else 0) + ∑ i, ∑ k, (if k < i then h k i else 0) := by
        simp only [Finset.sum_add_distrib]
    _ = 2 * ∑ p ∈ pairsLT, h p.1 p.2 := by
        rw [Finset.sum_comm (f := fun i k => if k < i then h k i else 0), hlt, two_mul]

lemma sum_quad_eq_four_mul (T : Fin 6 → Fin 6 → Fin 6 → Fin 6 → ℝ)
    (hs₁ : ∀ i k j l, T k i j l = T i k j l) (hd₁ : ∀ i j l, T i i j l = 0)
    (hs₂ : ∀ i k j l, T i k l j = T i k j l) (hd₂ : ∀ i k j, T i k j j = 0) :
    ∑ i, ∑ k, ∑ j, ∑ l, T i k j l = 4 * ∑ p ∈ pairsLT, ∑ q ∈ pairsLT, T p.1 p.2 q.1 q.2 := by
  have inner : ∀ i k, ∑ j, ∑ l, T i k j l = 2 * ∑ q ∈ pairsLT, T i k q.1 q.2 := fun i k =>
    sum_sum_eq_two_mul_sum_pairsLT (T i k) (fun j l => hs₂ i k j l) (fun j => hd₂ i k j)
  simp_rw [inner]
  rw [sum_sum_eq_two_mul_sum_pairsLT (fun i k => 2 * ∑ q ∈ pairsLT, T i k q.1 q.2)
    (fun i k => by simp_rw [hs₁]) (fun i => by simp [hd₁]), ← Finset.mul_sum, ← mul_assoc]
  norm_num

/-! ### One labelling -/

/-- The score of the labelling `(a, b)` is the paper's norm for any integer labels `α`, `β`
that agree with `a`, `b` modulo `6` up to translation. -/
lemma labelScore_expMat (Q : Fin 6 → Fin 6 → ℝ) (e f : I6 ≃ Fin 6) (a b : I6 ≃ ZMod 6)
    (α β : Fin 6 → ℤ) (hα : ∀ i, (α i : ZMod 6) = a (e.symm i) - a (e.symm 0))
    (hβ : ∀ j, (β j : ZMod 6) = b (f.symm j) - b (f.symm 0)) :
    labelScore (expMat Q e f) a b = alignNorm Q α β / 15 := by
  have hsum : ∑ q : I6 × I6 × I6 × I6,
      Complex.arg (plaq (expMat Q e f) a b q.1 q.2.1 q.2.2.1 q.2.2.2) ^ 2 =
      ∑ i, ∑ k, ∑ j, ∑ l, plaqTerm Q α β i k j l := by
    rw [← Fintype.sum_equiv (e.symm.prodCongr (e.symm.prodCongr (f.symm.prodCongr f.symm)))
      (fun q : Fin 6 × Fin 6 × Fin 6 × Fin 6 => plaqTerm Q α β q.1 q.2.1 q.2.2.1 q.2.2.2) _
      (fun q => (arg_plaq_expMat_sq Q e f a b α β hα hβ _ _ _ _).symm)]
    simp only [Fintype.sum_prod_type]
  have quad := sum_quad_eq_four_mul (plaqTerm Q α β) (plaqTerm_swap₁ Q α β)
    (plaqTerm_diag₁ Q α β) (plaqTerm_swap₂ Q α β) (plaqTerm_diag₂ Q α β)
  have h4 : (1 / 4 : ℝ) * (4 * ∑ p ∈ pairsLT, ∑ q ∈ pairsLT, plaqTerm Q α β p.1 p.2 q.1 q.2) =
      ∑ p ∈ pairsLT, ∑ q ∈ pairsLT, plaqTerm Q α β p.1 p.2 q.1 q.2 := by ring
  rw [labelScore, hsum, quad, h4]
  rfl

/-! ### Labels -/

/-- `Fin 6 ≃ ZMod 6`, `x ↦ (x : ℕ)`. -/
def finZMod : Fin 6 ≃ ZMod 6 := (ZMod.finEquiv 6).toEquiv

lemma finZMod_apply (x : Fin 6) : finZMod x = ((x : ℕ) : ZMod 6) := by
  rw [← ZMod.natCast_zmod_val (finZMod x)]
  rfl

lemma intCast_labelVal (a : Equiv.Perm (Fin 6)) (i : Fin 6) :
    ((labelVal a i : ℤ) : ZMod 6) = finZMod (a i) := by
  rw [labelVal, finZMod_apply, Int.cast_natCast]

/-- A paper labelling `a` (permutation of `0, …, 5`) as a `ZMod 6` labelling of `I6`. -/
def liftLabel (e : I6 ≃ Fin 6) (a : Equiv.Perm (Fin 6)) : I6 ≃ ZMod 6 :=
  e.trans (a.trans finZMod)

lemma liftLabel_spec (e : I6 ≃ Fin 6) (a : Equiv.Perm (Fin 6)) (ha : a 0 = 0) (i : Fin 6) :
    ((labelVal a i : ℤ) : ZMod 6) = liftLabel e a (e.symm i) - liftLabel e a (e.symm 0) := by
  simp only [liftLabel, Equiv.trans_apply, Equiv.apply_symm_apply, ha, intCast_labelVal]
  rw [show finZMod 0 = 0 by rw [finZMod_apply]; simp, sub_zero]

/-- A `ZMod 6` labelling of `I6`, translated so that the first label is `0`, as a paper
labelling (permutation of `0, …, 5` with `a₁ = 0`). -/
def normLabel (e : I6 ≃ Fin 6) (a : I6 ≃ ZMod 6) : Equiv.Perm (Fin 6) :=
  e.symm.trans (a.trans ((Equiv.subRight (a (e.symm 0))).trans finZMod.symm))

lemma normLabel_zero (e : I6 ≃ Fin 6) (a : I6 ≃ ZMod 6) : normLabel e a 0 = 0 := by
  simp only [normLabel, Equiv.trans_apply, Equiv.subRight_apply, sub_self]
  apply finZMod.injective
  rw [Equiv.apply_symm_apply, finZMod_apply]
  simp

lemma normLabel_spec (e : I6 ≃ Fin 6) (a : I6 ≃ ZMod 6) (i : Fin 6) :
    ((labelVal (normLabel e a) i : ℤ) : ZMod 6) = a (e.symm i) - a (e.symm 0) := by
  rw [intCast_labelVal]
  simp [normLabel]

/-! ### Main results -/

/-- **`Γ_F` is the paper's score.**  For every real phase array `Q` and every enumeration of
the rows and of the columns, `ΓF (e^{iQ}) = ΓFpaper Q` (SM Eq. `gamma-score`). -/
theorem ΓF_exp_eq_ΓFpaper (Q : Fin 6 → Fin 6 → ℝ) (e f : I6 ≃ Fin 6) :
    ΓF (expMat Q e f) = ΓFpaper Q := by
  apply le_antisymm
  · obtain ⟨p, -, hpeq⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
      (fun p : Labelling × Labelling => alignNorm Q (labelVal p.1) (labelVal p.2))
    rw [ΓFpaper, hpeq]
    calc ΓF (expMat Q e f)
        ≤ labelScore (expMat Q e f) (liftLabel e p.1) (liftLabel f p.2) :=
          Finset.inf'_le (fun p : (I6 ≃ ZMod 6) × (I6 ≃ ZMod 6) =>
            labelScore (expMat Q e f) p.1 p.2) (Finset.mem_univ (liftLabel e p.1, liftLabel f p.2))
      _ = alignNorm Q (labelVal p.1) (labelVal p.2) / 15 :=
          labelScore_expMat Q e f _ _ _ _ (liftLabel_spec e p.1 p.1.2)
            (liftLabel_spec f p.2 p.2.2)
      _ = 1 / 15 * alignNorm Q (labelVal p.1) (labelVal p.2) := by ring
  · obtain ⟨p, -, hpeq⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
      (fun p : (I6 ≃ ZMod 6) × (I6 ≃ ZMod 6) => labelScore (expMat Q e f) p.1 p.2)
    let q : Labelling × Labelling :=
      (⟨normLabel e p.1, normLabel_zero e p.1⟩, ⟨normLabel f p.2, normLabel_zero f p.2⟩)
    have hle := Finset.inf'_le
      (fun p : Labelling × Labelling => alignNorm Q (labelVal p.1) (labelVal p.2))
      (Finset.mem_univ q)
    have hval : ΓF (expMat Q e f) =
        alignNorm Q (labelVal (normLabel e p.1)) (labelVal (normLabel f p.2)) / 15 := by
      unfold ΓF
      rw [hpeq]
      exact labelScore_expMat Q e f _ _ _ _ (normLabel_spec e p.1) (normLabel_spec f p.2)
    rw [ΓFpaper, hval]
    have : alignNorm Q (labelVal q.1) (labelVal q.2) =
        alignNorm Q (labelVal (normLabel e p.1)) (labelVal (normLabel f p.2)) := rfl
    linarith

lemma exp_arg_mul_I_of_normSq {z : ℂ} (hz : Complex.normSq z = 1) :
    Complex.exp ((Complex.arg z : ℂ) * Complex.I) = z := by
  have hn : ‖z‖ = 1 := by
    rw [Complex.normSq_eq_norm_sq] at hz
    nlinarith [norm_nonneg z]
  have := Complex.norm_mul_exp_arg_mul_I z
  rwa [hn, Complex.ofReal_one, one_mul] at this

/-- For a matrix with unimodular entries, `ΓF H` is the paper's score of its phase array
`Q = arg H`, for every enumeration of the rows and columns. -/
theorem ΓF_eq_ΓFpaper {H : Mat6} (hH : EntrywiseUnit H) (e f : I6 ≃ Fin 6) :
    ΓF H = ΓFpaper (fun i j => Complex.arg (H (e.symm i) (f.symm j))) := by
  rw [← ΓF_exp_eq_ΓFpaper _ e f]
  congr 1
  ext r c
  simp only [expMat, Matrix.of_apply, Equiv.symm_apply_apply]
  exact (exp_arg_mul_I_of_normSq (hH r c)).symm

/-- The paper's score is well defined on `H = e^{iQ}`: it does not depend on the choice of
the phase array `Q`. -/
theorem ΓFpaper_congr {Q Q' : Fin 6 → Fin 6 → ℝ}
    (h : ∀ i j, Complex.exp ((Q i j : ℂ) * Complex.I) = Complex.exp ((Q' i j : ℂ) * Complex.I)) :
    ΓFpaper Q = ΓFpaper Q' := by
  rw [← ΓF_exp_eq_ΓFpaper Q stdIdx stdIdx, ← ΓF_exp_eq_ΓFpaper Q' stdIdx stdIdx]
  congr 1
  ext r c
  exact h _ _

/-- `ΓF H = ΓFpaper (arg H)` in the standard enumeration of rows and columns. -/
theorem ΓF_eq_ΓFpaper_phaseArray {H : Mat6} (hH : EntrywiseUnit H) :
    ΓF H = ΓFpaper (phaseArray H) :=
  ΓF_eq_ΓFpaper hH stdIdx stdIdx

/-- For a MUB triple `{I₆, H/√6, K/√6}` the three transitions `H`, `K`, `Hᴴ K/√6` have
unimodular entries, so `MinTransition` (used in (H2)) is SM Eq. `minimum-transition` with
the paper's `Γ_F`. -/
theorem minTransition_iff_paper {H K : Mat6} (hT : IsMUBTriple (std H K)) :
    MinTransition H K ↔
      ΓFpaper (phaseArray H) ≤ ΓFpaper (phaseArray K) ∧
        ΓFpaper (phaseArray H) ≤ ΓFpaper (phaseArray (s6 • (Hᴴ * K))) := by
  obtain ⟨hH, hK, hHK⟩ := (isMUBTriple_std_iff H K).1 hT
  have hL : EntrywiseUnit (s6 • (Hᴴ * K)) := by
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul, Complex.normSq_mul, normSq_s6, hHK]
    norm_num
  rw [MinTransition, ΓF_eq_ΓFpaper_phaseArray hH.1, ΓF_eq_ΓFpaper_phaseArray hK.1,
    ΓF_eq_ΓFpaper_phaseArray hL]

/-- Hypothesis (H2) of `TripleCertificate`, with SM Eq. `minimum-transition` stated through the
paper's literal score `ΓFpaper`, implies (H2) as stated in `TripleCertificate`. -/
theorem classified_of_paper {ι : Type} {piece : ι → Set Mat6} {ordering : ι → Prop}
    (h : ∀ p, ∀ H ∈ piece p, ∀ K, IsMUBTriple (std H K) →
      (ordering p → ΓFpaper (phaseArray H) ≤ ΓFpaper (phaseArray K) ∧
        ΓFpaper (phaseArray H) ≤ ΓFpaper (phaseArray (s6 • (Hᴴ * K)))) →
      HasOrder3Symmetry (std H K)) :
    ∀ p, ∀ H ∈ piece p, ∀ K, IsMUBTriple (std H K) →
      (ordering p → MinTransition H K) → HasOrder3Symmetry (std H K) :=
  fun p H hH K hT hord => h p H hH K hT fun ho => (minTransition_iff_paper hT).1 (hord ho)

end MUBTriples
