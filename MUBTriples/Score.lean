import MUBTriples.Basic

/-!
# The ordering score `Γ_F` (SM Eq. `gamma-score`)

For a phase array `Q` with `H = e^{iQ}`, the paper defines the plaquettes
`(RQ)_{ik;jl} = Q_ij + Q_kl - Q_il - Q_kj` (`i < k`, `j < l`) and

`Γ_F(e^{iQ}) = (1/15) min_{a,b} ‖dist_{2π}(RQ - (π/3) v(a,b))‖₂`,
`v(a,b)_{ik;jl} = (a_i - a_k)(b_j - b_l)`,

the minimum running over bijective labellings `a, b` of the rows and columns by
`0, …, 5` with `a₁ = b₁ = 0`.

**Our encoding.**  `dist_{2π}(θ) = |arg(e^{iθ})|`, so each plaquette term is
`|arg(H_ij H_kl H̄_il H̄_kj ζ^{-v})|` with `ζ = e^{iπ/3}`; since `ζ⁶ = 1` the
exponent only matters modulo `6`, so labels are bijections `I6 ≃ ZMod 6`.  We sum
over *all* ordered quadruples `(i, k, j, l)` and divide by `4`: terms with `i = k` or
`j = l` vanish and the four orderings of a plaquette give the same `arg²`
(`arg (conj z)² = arg z²`), so this is the paper's sum over `i < k, j < l`.  We
minimize over all bijections (without `a₁ = b₁ = 0`): translating labels modulo `6`
does not change `ζ^{-v}`, so the minimum is the same.  These identifications are
proved in `MUBTriples.ScoreFormula` (`ΓF_exp_eq_ΓFpaper`: `ΓF (e^{iQ})` equals the
paper's formula `ΓFpaper Q`, defined there literally).

## Main results

* `ΓF_of_equivalent`: invariance under Hadamard equivalence (row/column
  permutations and unit phases);
* `ΓF_conjM`, `ΓF_transpose`, `ΓF_conjTranspose`: invariance under conjugation,
  transpose and adjoint.
-/

open Matrix Hadamard6

namespace MUBTriples

/-- `ζ = e^{iπ/3}`. -/
noncomputable def ζ6 : ℂ := Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * Complex.I)

lemma normSq_ζ6_pow (n : ℕ) : Complex.normSq (ζ6 ^ n) = 1 := by
  rw [map_pow, Complex.normSq_eq_norm_sq, ζ6, Complex.norm_exp_ofReal_mul_I]; simp

lemma ζ6_pow_six : ζ6 ^ 6 = 1 := by
  rw [ζ6, ← Complex.exp_nat_mul]
  have : ((6 : ℕ) : ℂ) * (((Real.pi / 3 : ℝ) : ℂ) * Complex.I) = 2 * Real.pi * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_two_pi_mul_I]

lemma ζ6_pow_ne_zero (n : ℕ) : ζ6 ^ n ≠ 0 := by
  intro h; have := normSq_ζ6_pow n; rw [h] at this; simp at this

lemma ζ6_pow_neg_val (x : ZMod 6) : ζ6 ^ ((-x).val) = star (ζ6 ^ x.val) := by
  rw [ZMod.neg_val]
  split_ifs with hx
  · subst hx; simp
  · have hlt : x.val ≤ 6 := (ZMod.val_lt x).le
    apply mul_right_cancel₀ (ζ6_pow_ne_zero x.val)
    rw [← pow_add, Nat.sub_add_cancel hlt, ζ6_pow_six, star_mul_self_of_normSq (normSq_ζ6_pow _)]

/-- The phase-corrected plaquette `H_ij H_kl H̄_il H̄_kj ζ^{-(a_i-a_k)(b_j-b_l)}`. -/
noncomputable def plaq (H : Mat6) (a b : I6 ≃ ZMod 6) (i k j l : I6) : ℂ :=
  H i j * H k l * star (H i l) * star (H k j) * star (ζ6 ^ ((a i - a k) * (b j - b l)).val)

/-- The score of one labelling `(a, b)`. -/
noncomputable def labelScore (H : Mat6) (a b : I6 ≃ ZMod 6) : ℝ :=
  Real.sqrt ((1 / 4) * ∑ q : I6 × I6 × I6 × I6,
    Complex.arg (plaq H a b q.1 q.2.1 q.2.2.1 q.2.2.2) ^ 2) / 15

instance : Nonempty (I6 ≃ ZMod 6) := by
  refine ⟨Fintype.equivOfCardEq ?_⟩
  simp

/-- The Fourier score `Γ_F` of SM Eq. `gamma-score`. -/
noncomputable def ΓF (H : Mat6) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun p : (I6 ≃ ZMod 6) × (I6 ≃ ZMod 6) => labelScore H p.1 p.2)

/-- Minimum over a finite type is invariant under precomposition with a bijection. -/
lemma inf'_comp_equiv {α : Type*} [Fintype α] [Nonempty α] (e : α ≃ α) (f : α → ℝ) :
    Finset.univ.inf' Finset.univ_nonempty (f ∘ e) = Finset.univ.inf' Finset.univ_nonempty f := by
  apply le_antisymm
  · apply Finset.le_inf'
    intro x _
    calc Finset.univ.inf' Finset.univ_nonempty (f ∘ e) ≤ (f ∘ e) (e.symm x) :=
          Finset.inf'_le _ (Finset.mem_univ _)
      _ = f x := by simp
  · apply Finset.le_inf'
    intro x _
    exact Finset.inf'_le f (Finset.mem_univ (e x))

lemma ΓF_eq_of_labelScore {H G : Mat6} (e : (I6 ≃ ZMod 6) × (I6 ≃ ZMod 6) ≃
    (I6 ≃ ZMod 6) × (I6 ≃ ZMod 6))
    (h : ∀ p, labelScore G p.1 p.2 = labelScore H (e p).1 (e p).2) : ΓF G = ΓF H := by
  unfold ΓF
  rw [← inf'_comp_equiv e (fun p => labelScore H p.1 p.2)]
  congr 1
  funext p; exact h p

lemma arg_star_sq (z : ℂ) : Complex.arg (star z) ^ 2 = Complex.arg z ^ 2 := by
  have : star z = (starRingEnd ℂ) z := rfl
  rw [this, Complex.arg_conj]
  split_ifs with h
  · rw [h]
  · ring

/-! ### Invariance under equivalence -/

theorem ΓF_of_equivalent {H K : Mat6} (h : Equivalent H K) : ΓF K = ΓF H := by
  obtain ⟨σ, τ, r, c, hr, hc, hK⟩ := h
  refine ΓF_eq_of_labelScore
    (Equiv.prodCongr (Equiv.equivCongr σ (Equiv.refl _))
      (Equiv.equivCongr τ (Equiv.refl _))) ?_
  rintro ⟨a, b⟩
  have ha : ∀ x, (Equiv.equivCongr σ (Equiv.refl _) a) (σ x) = a x := by
    intro x; simp [Equiv.equivCongr_apply_apply]
  have hb : ∀ x, (Equiv.equivCongr τ (Equiv.refl _) b) (τ x) = b x := by
    intro x; simp [Equiv.equivCongr_apply_apply]
  simp only [labelScore, Equiv.prodCongr_apply, Prod.map]
  congr 3
  refine Fintype.sum_equiv
    (Equiv.prodCongr σ (Equiv.prodCongr σ (Equiv.prodCongr τ τ))) _ _ ?_
  rintro ⟨i, k, j, l⟩
  simp only [Equiv.prodCongr_apply, Prod.map]
  congr 2
  simp only [plaq, ha, hb, hK, star_mul']
  have hri := mul_star_self_of_normSq (hr i)
  have hrk := mul_star_self_of_normSq (hr k)
  have hcj := mul_star_self_of_normSq (hc j)
  have hcl := mul_star_self_of_normSq (hc l)
  linear_combination
    (H (σ i) (τ j) * H (σ k) (τ l) * star (H (σ i) (τ l)) * star (H (σ k) (τ j)) *
      star (ζ6 ^ ((a i - a k) * (b j - b l)).val)) *
    (r k * star (r k) * c j * star (c j) * c l * star (c l) * hri +
      c j * star (c j) * c l * star (c l) * hrk + c l * star (c l) * hcj + hcl)

/-! ### Conjugation, transpose, adjoint -/

/-- Negation of labels. -/
def negLabel (a : I6 ≃ ZMod 6) : I6 ≃ ZMod 6 := a.trans (Equiv.neg (ZMod 6))

theorem ΓF_conjM (H : Mat6) : ΓF (conjM H) = ΓF H := by
  refine ΓF_eq_of_labelScore
    (Equiv.prodCongr ⟨negLabel, negLabel, fun a => by ext; simp [negLabel],
      fun a => by ext; simp [negLabel]⟩ (Equiv.refl _)) ?_
  rintro ⟨a, b⟩
  simp only [labelScore]
  congr 3
  refine Fintype.sum_congr _ _ (fun q => ?_)
  have : plaq (conjM H) a b q.1 q.2.1 q.2.2.1 q.2.2.2 =
      star (plaq H (negLabel a) b q.1 q.2.1 q.2.2.1 q.2.2.2) := by
    simp only [plaq, conjM, Matrix.map_apply, negLabel, Equiv.trans_apply, Equiv.neg_apply]
    rw [show (-a q.1 - -a q.2.1) * (b q.2.2.1 - b q.2.2.2) =
      -((a q.1 - a q.2.1) * (b q.2.2.1 - b q.2.2.2)) by ring, ζ6_pow_neg_val]
    simp only [starRingEnd_apply, star_mul', star_star]
  rw [this, arg_star_sq]
  rfl

theorem ΓF_transpose (H : Mat6) : ΓF Hᵀ = ΓF H := by
  refine ΓF_eq_of_labelScore (Equiv.prodComm _ _) ?_
  rintro ⟨a, b⟩
  simp only [labelScore, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
  congr 3
  refine Fintype.sum_equiv
    ⟨fun q => (q.2.2.1, q.2.2.2, q.1, q.2.1), fun q => (q.2.2.1, q.2.2.2, q.1, q.2.1),
      fun _ => rfl, fun _ => rfl⟩ _ _ ?_
  rintro ⟨i, k, j, l⟩
  simp only [Equiv.coe_fn_mk, plaq, transpose_apply]
  congr 2
  rw [mul_comm (b j - b l)]
  ring

lemma conjM_transpose (H : Mat6) : conjM Hᵀ = Hᴴ := by
  ext i j; simp [conjM]

theorem ΓF_conjTranspose (H : Mat6) : ΓF Hᴴ = ΓF H := by
  rw [← conjM_transpose, ΓF_conjM, ΓF_transpose]

/-- Left and right multiplication by monomial matrices is a Hadamard equivalence. -/
lemma equivalent_monomial_mul {X M N : Mat6} (hM : IsMonomial M) (hN : IsMonomial N) :
    Equivalent X (M * X * N) := by
  obtain ⟨μ, m, hm, rfl⟩ := hM
  obtain ⟨ν, n, hn, rfl⟩ := hN
  refine ⟨μ⁻¹, ν, fun i => m (μ⁻¹ i), n, fun i => hm _, hn, fun i j => ?_⟩
  rw [mul_monomial_apply, monomial_mul_apply]

theorem ΓF_monomial_mul {X M N : Mat6} (hM : IsMonomial M) (hN : IsMonomial N) :
    ΓF (M * X * N) = ΓF X :=
  ΓF_of_equivalent (equivalent_monomial_mul hM hN)

end MUBTriples
