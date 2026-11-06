import MUBTriples.Recognition.Cases

/-!
# Normal form of a symmetric triple, part 1: anchor frame and column normalization

From an order-three symmetry `T` with anchor `U m` we pass (common unitary `U mᴴ`,
permutation of the bases) to a triple `V` with `V 0 = I₆`, on which the symmetry is the
diagonal unitary `diag d` (`dᵢ³ = 1`), and then relabel/rephase the columns of `V 1`, `V 2`
so that `diag d` acts as the standard double three-cycle `cyc`.
-/

open Matrix Hadamard6

namespace MUBTriples

lemma normSq_of_monomial_unitary {σ : Equiv.Perm I6} {c : I6 → ℂ}
    (h : IsUnitary (monomial σ c)) (j : I6) : Complex.normSq (c j) = 1 := by
  have h2 := h.2
  rw [monomial_conjTranspose, monomial_mul_monomial, inv_mul_cancel, monomial_one_eq_diagonal]
    at h2
  have := congrFun (congrFun h2 j) j
  simp only [diagonal_apply_eq, Matrix.one_apply_eq] at this
  rw [show σ⁻¹ (σ j) = j by simp] at this
  have e : (Complex.normSq (c j) : ℂ) = 1 := by rw [normSq_eq_mul_star, mul_comm]; exact this
  exact_mod_cast e

lemma normSq_of_cube_one {z : ℂ} (h : z ^ 3 = 1) : Complex.normSq z = 1 := by
  have h1 : Complex.normSq z ^ 3 = 1 := by rw [← map_pow, h, map_one]
  have h0 := Complex.normSq_nonneg z
  nlinarith [sq_nonneg (Complex.normSq z - 1), sq_nonneg (Complex.normSq z + 1)]

lemma isUnitary_diagonal {d : I6 → ℂ} (hd : ∀ i, Complex.normSq (d i) = 1) :
    IsUnitary (diagonal d) := by
  refine IsUnitary.of_mul_eq_one ?_
  rw [diagonal_conjTranspose, diagonal_mul_diagonal]
  have : (fun i => (star d) i * d i) = fun _ => (1 : ℂ) := by
    funext i; exact star_mul_self_of_normSq (hd i)
  rw [this]; rfl

/-- **Anchor frame.** -/
theorem anchor_frame {U : Triple} (hU : IsMUBTriple U) (hS : HasOrder3Symmetry U) :
    ∃ (V : Triple) (d : I6 → ℂ), TripleEquiv U V ∧ IsMUBTriple V ∧ V 0 = 1 ∧
      (∀ i, d i ^ 3 = 1) ∧
      ∀ k, k ≠ 0 → ∃ (σ : Equiv.Perm I6) (c : I6 → ℂ), IsDoubleThreeCycle σ ∧
        diagonal d * V k = V k * monomial σ c := by
  obtain ⟨T, m, hTu, hT3, ⟨d, hd⟩, hk⟩ := hS
  set π : Equiv.Perm (Fin 3) := Equiv.swap 0 m
  set W := (U m)ᴴ
  have hUm := hU.1 m
  have hE : TripleEquiv U (fun k => W * U (π k)) :=
    ⟨W, π, fun _ => 1, hUm.conjTranspose, fun _ => isMonomial_one, fun k => by simp⟩
  have hπ0 : π 0 = m := Equiv.swap_apply_left 0 m
  have hT' : W * T * U m = diagonal d := by
    rw [Matrix.mul_assoc, hd, ← Matrix.mul_assoc, hUm.2, Matrix.one_mul]
  refine ⟨_, d, hE, isMUBTriple_of_tripleEquiv hE hU, ?_, ?_, ?_⟩
  · show W * U (π 0) = 1
    rw [hπ0]; exact hUm.2
  · intro i
    have h3 : diagonal d ^ 3 = 1 := by
      rw [← hT', pow_succ, pow_two]
      have e : ∀ A B : Mat6, (W * A * U m) * (W * B * U m) = W * (A * B) * U m := by
        intro A B
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (U m) W, hUm.1, Matrix.one_mul]
      rw [e, e, ← pow_two, ← pow_succ, hT3, Matrix.mul_one]; exact hUm.2
    rw [diagonal_pow] at h3
    have := congrFun (congrFun h3 i) i
    simpa using this
  · intro k hk0
    have hπk : π k ≠ m := by
      intro h; apply hk0; apply π.injective; rw [h, hπ0]
    obtain ⟨σ, c, hσ, hσeq⟩ := hk (π k) hπk
    refine ⟨σ, c, hσ, ?_⟩
    show diagonal d * (W * U (π k)) = (W * U (π k)) * monomial σ c
    rw [← hT', Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (U m), hUm.1,
      Matrix.one_mul, Matrix.mul_assoc, hσeq, ← Matrix.mul_assoc]

lemma exists_ne_zero_col {X : Mat6} (hX : IsUnitary X) (j : I6) : ∃ i, X i j ≠ 0 := by
  by_contra h
  push Not at h
  have := congrFun (congrFun hX.2 j) j
  simp [Matrix.mul_apply, h] at this

@[simp] lemma cyc_inl (s : I3) : cyc (Sum.inl s) = Sum.inl (s + 1) := by
  simp [cyc, finRotate_apply]

@[simp] lemma cyc_inr (s : I3) : cyc (Sum.inr s) = Sum.inr (s + 1) := by
  simp [cyc, finRotate_apply]

/-- Phases accumulated along each column orbit. -/
def orbitPhase (c : I6 → ℂ) (e : Equiv.Perm I6) : I6 → ℂ
  | Sum.inl s => ![1, c (e (Sum.inl 0)), c (e (Sum.inl 0)) * c (e (Sum.inl 1))] s
  | Sum.inr s => ![1, c (e (Sum.inr 0)), c (e (Sum.inr 0)) * c (e (Sum.inr 1))] s

/-- **Column normalization.**  Relabelling and rephasing the columns of `X` turns the
action of `diag d` into the standard double three-cycle. -/
theorem column_normalize {d : I6 → ℂ} {X : Mat6} (hX : IsUnitary X) (hd3 : ∀ i, d i ^ 3 = 1)
    {σ : Equiv.Perm I6} {c : I6 → ℂ} (hσ : IsDoubleThreeCycle σ)
    (h : diagonal d * X = X * monomial σ c) :
    ∃ M, IsMonomial M ∧ diagonal d * (X * M) = (X * M) * monomial cyc 1 := by
  have hdn : ∀ i, Complex.normSq (d i) = 1 := fun i => normSq_of_cube_one (hd3 i)
  have hc : ∀ j, Complex.normSq (c j) = 1 := by
    apply normSq_of_monomial_unitary
    have : monomial σ c = Xᴴ * diagonal d * X := by
      rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, hX.2, Matrix.one_mul]
    rw [this]; exact (hX.conjTranspose.mul (isUnitary_diagonal hdn)).mul hX
  obtain ⟨e, he⟩ := hσ
  have hent : ∀ i j, d i * X i j = X i (σ j) * c j := by
    intro i j; have := congrFun (congrFun h i) j; rwa [diagonal_mul, mul_monomial_apply] at this
  -- the phases around each cycle multiply to one
  have hcyc : ∀ b : I6, c (e b) * c (e (cyc b)) * c (e (cyc (cyc b))) = 1 ∨
      cyc (cyc (cyc b)) ≠ b := by
    intro b
    by_cases hb : cyc (cyc (cyc b)) = b
    · left
      obtain ⟨i, hi⟩ := exists_ne_zero_col hX (e b)
      have E1 := hent i (e b); rw [he] at E1
      have E2 := hent i (e (cyc b)); rw [he] at E2
      have E3 := hent i (e (cyc (cyc b))); rw [he, hb] at E3
      have key : (c (e b) * c (e (cyc b)) * c (e (cyc (cyc b))) - 1) * X i (e b) = 0 := by
        linear_combination (X i (e b)) * hd3 i - d i ^ 2 * E1 -
          d i * c (e b) * E2 - c (e b) * c (e (cyc b)) * E3
      exact sub_eq_zero.1 ((mul_eq_zero.1 key).resolve_right hi)
    · right; exact hb
  have hcyc' : ∀ b : I6, c (e b) * c (e (cyc b)) * c (e (cyc (cyc b))) = 1 := by
    intro b
    rcases hcyc b with h | h
    · exact h
    · exfalso; apply h
      rcases b with s | s <;> fin_cases s <;> rfl
  refine ⟨monomial e (orbitPhase c e), ⟨e, _, fun j => ?_, rfl⟩, ?_⟩
  · rcases j with s | s <;> fin_cases s <;> simp [orbitPhase, Complex.normSq_mul, hc]
  · ext i j
    rw [diagonal_mul, mul_monomial_apply, mul_monomial_apply, mul_monomial_apply, Pi.one_apply,
      mul_one, ← mul_assoc, hent, he, mul_assoc]
    congr 1
    rcases j with s | s <;> fin_cases s
    · simp [orbitPhase]
    · simp [orbitPhase]; ring
    · have := hcyc' (Sum.inl 0)
      simp [orbitPhase] at this ⊢
      linear_combination this
    · simp [orbitPhase]
    · simp [orbitPhase]; ring
    · have := hcyc' (Sum.inr 0)
      simp [orbitPhase] at this ⊢
      linear_combination this

/-! ### Eigenvalue multiplicities -/

/-- If `diag d` acts on the columns of `Y` (unbiased to `I₆`) as `cyc`, then `Σᵢ dᵢ = 0`. -/
lemma sum_d_eq_zero {d : I6 → ℂ} {Y : Mat6} (hY : IsUnitary Y) (hub : Unbiased 1 Y)
    (h : diagonal d * Y = Y * monomial cyc 1) : ∑ i, d i = 0 := by
  have hent : ∀ i j, Y i (cyc j) = d i * Y i j := by
    intro i j; have := congrFun (congrFun h i) j
    rw [diagonal_mul, mul_monomial_apply] at this; simpa using this.symm
  have hn : ∀ i j, Complex.normSq (Y i j) = 1 / 6 := by
    intro i j; have := hub i j; simpa using this
  have h01 := congrFun (congrFun hY.2 (Sum.inl 0)) (Sum.inl 1)
  rw [Matrix.mul_apply, Matrix.one_apply_ne (by simp)] at h01
  have e : ∀ i, (Y)ᴴ (Sum.inl 0) i * Y i (Sum.inl 1) = (1 / 6 : ℂ) * d i := by
    intro i
    rw [conjTranspose_apply, show (Sum.inl 1 : I6) = cyc (Sum.inl 0) by simp, hent]
    have := normSq_eq_mul_star (Y i (Sum.inl 0)); rw [hn] at this; push_cast at this
    linear_combination (-(d i)) * this
  simp only [e, ← Finset.mul_sum] at h01
  exact (mul_eq_zero.1 h01).resolve_left (by norm_num)

/-- Six cube roots of unity summing to zero take each value twice. -/
lemma card_fiber_two {e : I6 → I3} (h : ∑ i, ω ^ (e i).val = 0) (t : I3) :
    (Finset.univ.filter (fun i => e i = t)).card = 2 := by
  set n : I3 → ℕ := fun t => (Finset.univ.filter (fun i => e i = t)).card with hn
  have hsum : ∑ i, ω ^ (e i).val = ∑ t : I3, (n t : ℂ) * ω ^ t.val := by
    rw [← Finset.sum_fiberwise Finset.univ e (fun i => ω ^ (e i).val)]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Finset.sum_congr rfl (g := fun _ => ω ^ t.val) (fun i hi => by
      rw [(Finset.mem_filter.1 hi).2]), Finset.sum_const, nsmul_eq_mul]
  have htot : ∑ t : I3, n t = 6 := by
    rw [hn, ← Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_univ (e i))]; rfl
  rw [hsum, Fin.sum_univ_three] at h
  rw [Fin.sum_univ_three] at htot
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, mul_one, pow_one,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.natCast_re,
    Complex.natCast_im, ω_re, ω_im, ω_sq_re, ω_sq_im, Complex.zero_re, Complex.zero_im,
    Complex.one_re, Complex.one_im] at hre him
  have hs3 : 0 < Real.sqrt 3 := by positivity
  have h12 : (n 1 : ℝ) = n 2 := by nlinarith
  have h01 : (n 0 : ℝ) = n 1 := by nlinarith
  have htot' : (n 0 : ℝ) + n 1 + n 2 = 6 := by exact_mod_cast htot
  have : (n t : ℝ) = 2 := by fin_cases t <;> simp <;> linarith
  exact_mod_cast this

/-- A labelling with every fibre of size two is a relabelling of `tIdx`. -/
lemma exists_perm_of_fibers {e : I6 → I3}
    (h : ∀ t, (Finset.univ.filter (fun i => e i = t)).card = 2) :
    ∃ p : Equiv.Perm I6, ∀ a, e (p a) = tIdx a := by
  have hx : ∀ t, ∃ x y : I6, x ≠ y ∧ Finset.univ.filter (fun i => e i = t) = {x, y} :=
    fun t => Finset.card_eq_two.1 (h t)
  choose x y hxy hset using hx
  have hxe : ∀ t, e (x t) = t := fun t => by
    have : x t ∈ Finset.univ.filter (fun i => e i = t) := by rw [hset]; simp
    exact (Finset.mem_filter.1 this).2
  have hye : ∀ t, e (y t) = t := fun t => by
    have : y t ∈ Finset.univ.filter (fun i => e i = t) := by rw [hset]; simp
    exact (Finset.mem_filter.1 this).2
  let f : I6 → I6 := fun a => Sum.elim x y a
  have hf : ∀ a, e (f a) = tIdx a := by
    intro a; rcases a with t | t
    · exact hxe t
    · exact hye t
  have hinj : Function.Injective f := by
    intro a b hab
    have ht : tIdx a = tIdx b := by rw [← hf a, ← hf b, hab]
    rcases a with s | s <;> rcases b with t | t <;> simp only [tIdx] at ht <;> subst ht <;>
      simp only [f, Sum.elim_inl, Sum.elim_inr] at hab
    · rfl
    · exact absurd hab (hxy s)
    · exact absurd hab.symm (hxy s)
    · rfl
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), hf⟩

/-! ### Row phases: the twelve-phase normal form -/

lemma dft_inv {a b c : ℂ} (h0 : a + b + c = 0) (h1 : a + b * ω + c * ω ^ 2 = 0)
    (h2 : a + b * ω ^ 2 + c * ω = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have ha : a = 0 := by
    linear_combination (1 / 3 : ℂ) * (h0 + h1 + h2) - (1 / 3 : ℂ) * (b + c) * ω_sq_add
  have hb : b = 0 := by
    linear_combination (1 / 3 : ℂ) * (h0 + ω ^ 2 * h1 + ω * h2) -
      (1 / 3 : ℂ) * (a + c * ω) * ω_sq_add - (1 / 3 : ℂ) * (2 * b + c * (ω + 1)) * ω_cube +
      (2 / 3 : ℂ) * c * ω_cube
  refine ⟨ha, hb, ?_⟩
  linear_combination h0 - ha - hb

lemma Fintype_sum_I6 (f : I6 → ℂ) :
    ∑ i, f i = ∑ t : I3, (f (Sum.inl t) + f (Sum.inr t)) := by
  rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]

/-- Columns `(b, s)` are `T^s` applied to column `(b, 0)`. -/
lemma col_formula {Z : Mat6} (hc : ∀ i j, Z i (cyc j) = ω ^ (tIdx i).val * Z i j) (i : I6) (s : I3) :
    Z i (Sum.inl s) = ω ^ ((tIdx i).val * s.val) * Z i (Sum.inl 0) ∧
      Z i (Sum.inr s) = ω ^ ((tIdx i).val * s.val) * Z i (Sum.inr 0) := by
  have h1 := hc i (Sum.inl 0); have h2 := hc i (Sum.inl 1)
  have h3 := hc i (Sum.inr 0); have h4 := hc i (Sum.inr 1)
  simp only [cyc_inl, cyc_inr] at h1 h2 h3 h4
  fin_cases s
  · simp
  · simp only [Fin.mk_one, Fin.val_one, mul_one]
    exact ⟨by simpa using h1, by simpa using h3⟩
  · simp only [Fin.reduceFinMk, Fin.val_two]
    have e1 : (1 : I3) + 1 = 2 := rfl
    have e0 : (0 : I3) + 1 = 1 := rfl
    rw [e0] at h1 h3; rw [e1] at h2 h4
    rw [mul_comm, pow_mul, h2, h1, h4, h3]
    constructor <;> ring

/-- Orthogonality of the two column orbits gives, eigenspace by eigenspace,
`Σₐ conj(Z(a,t),(0,0)) Z(a,t),(1,0) = 0`. -/
lemma orbit_orth {Z : Mat6} (hZ : IsUnitary Z)
    (hc : ∀ i j, Z i (cyc j) = ω ^ (tIdx i).val * Z i j) (t : I3) :
    star (Z (Sum.inl t) (Sum.inl 0)) * Z (Sum.inl t) (Sum.inr 0) +
      star (Z (Sum.inr t) (Sum.inl 0)) * Z (Sum.inr t) (Sum.inr 0) = 0 := by
  set G : I3 → ℂ := fun t => star (Z (Sum.inl t) (Sum.inl 0)) * Z (Sum.inl t) (Sum.inr 0) +
      star (Z (Sum.inr t) (Sum.inl 0)) * Z (Sum.inr t) (Sum.inr 0) with hG
  have horth : ∀ s : I3, ∑ t : I3, ω ^ (t.val * s.val) * G t = 0 := by
    intro s
    have h := congrFun (congrFun hZ.2 (Sum.inl 0)) (Sum.inr s)
    rw [Matrix.mul_apply, Matrix.one_apply_ne (by simp), Fintype_sum_I6] at h
    rw [← h]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    simp only [conjTranspose_apply, hG, (col_formula hc _ s).2]
    simp only [tIdx]; ring
  have h0 := horth 0; have h1 := horth 1; have h2 := horth 2
  simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, mul_zero, zero_mul,
    pow_zero, one_mul, mul_one] at h0 h1 h2
  rw [show (2 * 2 : ℕ) = 3 + 1 by rfl, pow_add, ω_cube, one_mul, pow_one] at h2
  obtain ⟨g0, g1, g2⟩ := dft_inv h0 (by linear_combination h1) (by linear_combination h2)
  fin_cases t
  exacts [g0, g1, g2]

lemma normSq_t6 : Complex.normSq t6 = 6 := by
  rw [t6, Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num)]

lemma t6_mul_sixth : t6 * (1 / 6 : ℂ) = s6 := by
  have h := t6_mul_t6
  have hs := s6_mul_t6
  have ht : t6 ≠ 0 := by intro h0; rw [h0] at h; simp at h
  apply mul_right_cancel₀ ht
  rw [hs]; linear_combination (1 / 6 : ℂ) * h

/-- **Row phases.**  Rephasing the rows of two bases on which `T = diag(1,ω,ω²,1,ω,ω²)` acts
as `cyc` brings them to `symH x/√6` and `symK y u v/√6`. -/
theorem phase_normalize {Z1 Z2 : Mat6} (hZ1 : IsUnitary Z1) (hZ2 : IsUnitary Z2)
    (hu1 : Unbiased 1 Z1) (hu2 : Unbiased 1 Z2)
    (hc1 : ∀ i j, Z1 i (cyc j) = ω ^ (tIdx i).val * Z1 i j)
    (hc2 : ∀ i j, Z2 i (cyc j) = ω ^ (tIdx i).val * Z2 i j) :
    ∃ (r x y u v : _), (∀ i : I6, Complex.normSq (r i) = 1) ∧ UnitVec x ∧ UnitVec y ∧
      UnitVec u ∧ UnitVec v ∧ diagonal r * Z1 = s6 • symH x ∧
      diagonal r * Z2 = s6 • symK y u v := by
  have hn1 : ∀ i j, Complex.normSq (Z1 i j) = 1 / 6 := fun i j => by simpa using hu1 i j
  have hn2 : ∀ i j, Complex.normSq (Z2 i j) = 1 / 6 := fun i j => by simpa using hu2 i j
  have hsq : ∀ z : ℂ, Complex.normSq z = 1 / 6 → star z * z = 1 / 6 := fun z hz => by
    have := normSq_eq_mul_star z; rw [hz] at this; push_cast at this
    rw [mul_comm]; exact this.symm
  set r : I6 → ℂ := fun i => t6 * star (Z1 i (Sum.inl 0)) with hr
  have hrn : ∀ i, Complex.normSq (r i) = 1 := fun i => by
    simp only [hr, Complex.normSq_mul, normSq_t6, normSq_star, hn1]; norm_num
  have hrh : ∀ i, r i * Z1 i (Sum.inl 0) = s6 := fun i => by
    rw [hr]; simp only; rw [mul_assoc, hsq _ (hn1 _ _), t6_mul_sixth]
  -- the unit phases
  set x : I3 → ℂ := fun t => t6 * r (Sum.inl t) * Z1 (Sum.inl t) (Sum.inr 0) with hx
  set κ0 : I6 → ℂ := fun i => t6 * r i * Z2 i (Sum.inl 0) with hκ0
  set κ1 : I6 → ℂ := fun i => t6 * r i * Z2 i (Sum.inr 0) with hκ1
  set u : I3 → ℂ := fun t => κ0 (Sum.inl t) with hu
  set v : I3 → ℂ := fun t => κ0 (Sum.inr t) with hv
  set y : I3 → ℂ := fun t => κ1 (Sum.inl t) * star (u t) with hy
  have hxn : UnitVec x := fun t => by
    simp only [hx, Complex.normSq_mul, normSq_t6, hrn, hn1]; norm_num
  have hκ0n : ∀ i, Complex.normSq (κ0 i) = 1 := fun i => by
    simp only [hκ0, Complex.normSq_mul, normSq_t6, hrn, hn2]; norm_num
  have hκ1n : ∀ i, Complex.normSq (κ1 i) = 1 := fun i => by
    simp only [hκ1, Complex.normSq_mul, normSq_t6, hrn, hn2]; norm_num
  have hun : UnitVec u := fun t => hκ0n _
  have hvn : UnitVec v := fun t => hκ0n _
  have hyn : UnitVec y := fun t => by
    simp only [hy, Complex.normSq_mul, normSq_star, hκ1n, hκ0n, hu]; norm_num
  -- `s6 * (t6 * a) = a`
  have hst : ∀ a : ℂ, s6 * (t6 * a) = a := fun a => by rw [← mul_assoc, s6_mul_t6, one_mul]
  -- orthogonality of the two orbits
  have o1 := orbit_orth hZ1 hc1
  have o2 := orbit_orth hZ2 hc2
  have hrr : ∀ i, star (r i) * r i = 1 := fun i => star_mul_self_of_normSq (hrn i)
  have ht6 : star t6 * t6 = 6 := by rw [t6_star, t6_mul_t6]
  have o2' : ∀ t, star (u t) * κ1 (Sum.inl t) + star (v t) * κ1 (Sum.inr t) = 0 := by
    intro t
    have := o2 t
    simp only [hu, hv, hκ0, hκ1, star_mul']
    linear_combination (6 : ℂ) * this +
      (star t6 * t6) * Z2 (Sum.inl t) (Sum.inr 0) * star (Z2 (Sum.inl t) (Sum.inl 0)) *
        hrr (Sum.inl t) +
      (star t6 * t6) * Z2 (Sum.inr t) (Sum.inr 0) * star (Z2 (Sum.inr t) (Sum.inl 0)) *
        hrr (Sum.inr t) +
      (star (Z2 (Sum.inl t) (Sum.inl 0)) * Z2 (Sum.inl t) (Sum.inr 0) +
        star (Z2 (Sum.inr t) (Sum.inl 0)) * Z2 (Sum.inr t) (Sum.inr 0)) * ht6
  refine ⟨r, x, y, u, v, hrn, hxn, hyn, hun, hvn, ?_, ?_⟩
  · ext i j
    rcases i with t | t <;> rcases j with s | s
    · rw [diagonal_mul, (col_formula hc1 _ s).1]
      simp only [symH, Matrix.smul_apply, fromBlocks_apply₁₁, F3_apply, smul_eq_mul, tIdx]
      rw [← hrh (Sum.inl t)]; ring
    · rw [diagonal_mul, (col_formula hc1 _ s).2]
      simp only [symH, Matrix.smul_apply, fromBlocks_apply₁₂, F3_apply, smul_eq_mul, tIdx,
        diagonal_mul, hx]
      rw [show s6 * (t6 * r (Sum.inl t) * Z1 (Sum.inl t) (Sum.inr 0) * ω ^ (t.val * s.val)) =
        s6 * (t6 * (r (Sum.inl t) * Z1 (Sum.inl t) (Sum.inr 0) * ω ^ (t.val * s.val))) by ring,
        hst]
      ring
    · rw [diagonal_mul, (col_formula hc1 _ s).1]
      simp only [symH, Matrix.smul_apply, fromBlocks_apply₂₁, F3_apply, smul_eq_mul, tIdx]
      rw [← hrh (Sum.inr t)]; ring
    · rw [diagonal_mul, (col_formula hc1 _ s).2]
      simp only [symH, Matrix.smul_apply, fromBlocks_apply₂₂, F3_apply, smul_eq_mul, tIdx,
        diagonal_mul, hx, Matrix.neg_apply]
      have e := o1 t
      have h1 : r (Sum.inr t) * Z1 (Sum.inr t) (Sum.inr 0) =
          -(r (Sum.inl t) * Z1 (Sum.inl t) (Sum.inr 0)) := by
        simp only [hr]; linear_combination t6 * e
      rw [show r (Sum.inr t) * (ω ^ (t.val * s.val) * Z1 (Sum.inr t) (Sum.inr 0)) =
        ω ^ (t.val * s.val) * (r (Sum.inr t) * Z1 (Sum.inr t) (Sum.inr 0)) by ring, h1]
      rw [show s6 * -(t6 * r (Sum.inl t) * Z1 (Sum.inl t) (Sum.inr 0) * ω ^ (t.val * s.val)) =
        -(s6 * (t6 * (r (Sum.inl t) * Z1 (Sum.inl t) (Sum.inr 0) * ω ^ (t.val * s.val)))) by ring,
        hst]
      ring
  · ext i j
    have hu1 : ∀ t, u t * star (u t) = 1 := fun t => mul_star_self_of_normSq (hun t)
    have hv1 : ∀ t, v t * star (v t) = 1 := fun t => mul_star_self_of_normSq (hvn t)
    rcases i with t | t <;> rcases j with s | s
    · rw [diagonal_mul, (col_formula hc2 _ s).1]
      simp only [symK, Matrix.smul_apply, fromBlocks_apply₁₁, F3_apply, smul_eq_mul, tIdx,
        diagonal_mul, hu, hκ0]
      rw [show s6 * (t6 * r (Sum.inl t) * Z2 (Sum.inl t) (Sum.inl 0) * ω ^ (t.val * s.val)) =
        s6 * (t6 * (r (Sum.inl t) * Z2 (Sum.inl t) (Sum.inl 0) * ω ^ (t.val * s.val))) by ring,
        hst]
      ring
    · rw [diagonal_mul, (col_formula hc2 _ s).2]
      simp only [symK, Matrix.smul_apply, fromBlocks_apply₁₂, F3_apply, smul_eq_mul, tIdx,
        diagonal_mul, Pi.mul_apply]
      have : u t * y t = κ1 (Sum.inl t) := by
        simp only [hy]; linear_combination κ1 (Sum.inl t) * hu1 t
      rw [this, hκ1]; simp only
      rw [show s6 * (t6 * r (Sum.inl t) * Z2 (Sum.inl t) (Sum.inr 0) * ω ^ (t.val * s.val)) =
        s6 * (t6 * (r (Sum.inl t) * Z2 (Sum.inl t) (Sum.inr 0) * ω ^ (t.val * s.val))) by ring,
        hst]
      ring
    · rw [diagonal_mul, (col_formula hc2 _ s).1]
      simp only [symK, Matrix.smul_apply, fromBlocks_apply₂₁, F3_apply, smul_eq_mul, tIdx,
        diagonal_mul, hv, hκ0]
      rw [show s6 * (t6 * r (Sum.inr t) * Z2 (Sum.inr t) (Sum.inl 0) * ω ^ (t.val * s.val)) =
        s6 * (t6 * (r (Sum.inr t) * Z2 (Sum.inr t) (Sum.inl 0) * ω ^ (t.val * s.val))) by ring,
        hst]
      ring
    · rw [diagonal_mul, (col_formula hc2 _ s).2]
      simp only [symK, Matrix.smul_apply, fromBlocks_apply₂₂, F3_apply, smul_eq_mul, tIdx,
        diagonal_mul, Pi.mul_apply, Matrix.neg_apply]
      have : v t * y t = -κ1 (Sum.inr t) := by
        simp only [hy]
        have := o2' t
        linear_combination (v t) * this - κ1 (Sum.inr t) * hv1 t
      rw [this, hκ1]; simp only
      rw [show s6 * -(-(t6 * r (Sum.inr t) * Z2 (Sum.inr t) (Sum.inr 0)) * ω ^ (t.val * s.val)) =
        s6 * (t6 * (r (Sum.inr t) * Z2 (Sum.inr t) (Sum.inr 0) * ω ^ (t.val * s.val))) by ring,
        hst]
      ring

/-! ### The normal form theorem -/

lemma isMonomial_diagonal {r : I6 → ℂ} (hr : ∀ i, Complex.normSq (r i) = 1) :
    IsMonomial (diagonal r) := ⟨1, r, hr, (monomial_one_eq_diagonal r).symm⟩

/-- **Normal form of symmetric triples** (SM Eq. `tc-cyclic-coordinates`).  A MUB triple
with an order-three symmetry is equivalent to `{I₆, symH x/√6, symK y u v/√6}` for unit
phases `x, y, u, v`. -/
theorem normalForm_of_symmetric {U : Triple} (hU : IsMUBTriple U) (hS : HasOrder3Symmetry U) :
    ∃ x y u v : I3 → ℂ, UnitVec x ∧ UnitVec y ∧ UnitVec u ∧ UnitVec v ∧
      TripleEquiv U (std (symH x) (symK y u v)) := by
  obtain ⟨V, d, hUV, hV, hV0, hd3, hk⟩ := anchor_frame hU hS
  obtain ⟨σ1, c1, hσ1, h1⟩ := hk 1 (by decide)
  obtain ⟨σ2, c2, hσ2, h2⟩ := hk 2 (by decide)
  obtain ⟨M1, hM1, hY1⟩ := column_normalize (hV.1 1) hd3 hσ1 h1
  obtain ⟨M2, hM2, hY2⟩ := column_normalize (hV.1 2) hd3 hσ2 h2
  -- relabel the columns
  set Y : Triple := ![1, V 1 * M1, V 2 * M2] with hYdef
  have hVY : TripleEquiv V Y := by
    refine ⟨1, 1, ![1, M1, M2], isUnitary_one, fun k => ?_, fun k => ?_⟩
    · fin_cases k
      exacts [isMonomial_one, hM1, hM2]
    · fin_cases k
      · show (1 : Mat6) = 1 * V 0 * 1; rw [hV0]; simp
      · show V 1 * M1 = 1 * V 1 * M1; simp
      · show V 2 * M2 = 1 * V 2 * M2; simp
  have hY : IsMUBTriple Y := isMUBTriple_of_tripleEquiv hVY hV
  have hub1 : Unbiased 1 (V 1 * M1) := hY.2 0 1 (by decide)
  -- eigenvalue multiplicities
  have hsum := sum_d_eq_zero (hY.1 1) hub1 hY1
  have hroot : ∀ i, ∃ t : I3, d i = ω ^ t.val := fun i => cube_root_cases (hd3 i)
  choose e he using hroot
  have hfib := card_fiber_two (e := e) (by rw [← hsum]; simp only [he])
  obtain ⟨p, hp⟩ := exists_perm_of_fibers hfib
  -- permute the rows
  set R : Mat6 := monomial p⁻¹ (fun _ => 1) with hRdef
  have hR : IsMonomial R := ⟨p⁻¹, _, fun _ => by simp, rfl⟩
  have hRapp : ∀ (A : Mat6) i j, (R * A) i j = A (p i) j := by
    intro A i j; rw [hRdef, monomial_mul_apply]; simp
  set Z : Triple := ![1, R * (V 1 * M1), R * (V 2 * M2)] with hZdef
  have hYZ : TripleEquiv Y Z := by
    refine ⟨R, 1, ![Rᴴ, 1, 1], hR.isUnitary, fun k => ?_, fun k => ?_⟩
    · fin_cases k
      exacts [hR.conjTranspose, isMonomial_one, isMonomial_one]
    · fin_cases k
      · show (1 : Mat6) = R * 1 * Rᴴ; rw [Matrix.mul_one, hR.isUnitary.1]
      · show R * (V 1 * M1) = R * (V 1 * M1) * 1; simp
      · show R * (V 2 * M2) = R * (V 2 * M2) * 1; simp
  have hZ : IsMUBTriple Z := isMUBTriple_of_tripleEquiv hYZ hY
  have hcyc : ∀ {X : Mat6}, diagonal d * X = X * monomial cyc 1 →
      ∀ i j, (R * X) i (cyc j) = ω ^ (tIdx i).val * (R * X) i j := by
    intro X hX i j
    rw [hRapp, hRapp]
    have := congrFun (congrFun hX (p i)) j
    rw [diagonal_mul, mul_monomial_apply] at this
    simp only [Pi.one_apply, mul_one] at this
    rw [← this, he, hp]
  obtain ⟨r, x, y, u, v, hr, hx, hy, hu, hv, hZ1, hZ2⟩ :=
    phase_normalize (hZ.1 1) (hZ.1 2) (hZ.2 0 1 (by decide)) (hZ.2 0 2 (by decide))
      (hcyc hY1) (hcyc hY2)
  have hD := isMonomial_diagonal hr
  have hZS : TripleEquiv Z (std (symH x) (symK y u v)) := by
    refine ⟨diagonal r, 1, ![(diagonal r)ᴴ, 1, 1], hD.isUnitary, fun k => ?_, fun k => ?_⟩
    · fin_cases k
      exacts [hD.conjTranspose, isMonomial_one, isMonomial_one]
    · fin_cases k
      · show (1 : Mat6) = diagonal r * 1 * (diagonal r)ᴴ
        rw [Matrix.mul_one, hD.isUnitary.1]
      · show s6 • symH x = diagonal r * (R * (V 1 * M1)) * 1
        rw [Matrix.mul_one]; exact hZ1.symm
      · show s6 • symK y u v = diagonal r * (R * (V 2 * M2)) * 1
        rw [Matrix.mul_one]; exact hZ2.symm
  exact ⟨x, y, u, v, hx, hy, hu, hv,
    tripleEquiv_trans hUV (tripleEquiv_trans hVY (tripleEquiv_trans hYZ hZS))⟩

end MUBTriples
