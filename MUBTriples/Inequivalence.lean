import MUBTriples.Seeds
import MUBTriples.MainTheorem

/-!
# The isolated triple is not equivalent to any family member

We use a triple-equivalence invariant built from the *Bargmann (three-vertex) products*
`⟨e|f⟩⟨f|g⟩⟨g|e⟩` of a vector `e` of the first basis, `f` of the second and `g` of the third:

`bargmann4 U = Σ_{e,f,g} (⟨e|f⟩⟨f|g⟩⟨g|e⟩)⁴`  (216 terms).

* Column phases cancel in each product and column permutations, as well as a common
  unitary, only reindex the sum (`bargmann4_frame`); a cyclic permutation of the three bases
  reindexes it and a transposition conjugates it (`bargmann4_perm`).  Hence
  `bargmann4 V ∈ {bargmann4 U, conj (bargmann4 U)}` whenever `TripleEquiv U V`
  (`bargmann4_of_tripleEquiv`), and *the vanishing of its imaginary part is an invariant*.
* Every member of the continuous family is equivalent to its own complex conjugate by an
  equivalence that fixes the three bases (`familyTriple_conj_frame`; the common unitary swaps
  the two coordinates of each eigenspace of the order-three symmetry, with phases `±D̄`), so its
  invariant is real (`bargmann4_familyTriple_im`).
* For the isolated triple the invariant is `-2592 (1 + 2ω)/6⁸ = -2592 √3 i/6⁸`
  (`bargmann4_isolatedTriple`), which is not real.

Main result: `not_tripleEquiv_isolatedTriple_of_familyMember`.  The two alternatives of
`TripleClassification` are therefore mutually exclusive (`family_and_isolated_exclusive`).

Remark.  The isolated triple's first seed `(2π/3, -2π/3, -2π/3, 2π/3)` (`seedOf_isolatedTriple`)
is also the seed `(θ₁, θ₂, θ₁ - θ₂, θ₁)` of the family member with `(θ₁, θ₂) = (2π/3, -2π/3)`,
`σ = 0` (SM: "coincident seed coordinates need not represent equivalent triples"); numerically
all three transitions of that family member have Haagerup invariants in the sixth roots of
unity, like `F₆`, so pairwise invariants of the transitions do not separate the two classes,
whereas the three-basis invariant `bargmann4` does.

Finally, `SeedClassification` restates the classification with the explicit seed
parametrization and with the exclusive "or" (`mubTriple_seedClassification` under the
certificate hypotheses; `symmetric_seedClassification` without hypotheses for triples with an
order-three symmetry).
-/

open Matrix Hadamard6

namespace MUBTriples

/-- The Bargmann product `⟨e|f⟩⟨f|g⟩⟨g|e⟩` with `e ∈ U₀`, `f ∈ U₁`, `g ∈ U₂`. -/
noncomputable def bargmann (U : Triple) (e f g : I6) : ℂ :=
  ((U 0)ᴴ * U 1) e f * ((U 1)ᴴ * U 2) f g * ((U 2)ᴴ * U 0) g e

/-- The invariant `Σ_{e,f,g} (⟨e|f⟩⟨f|g⟩⟨g|e⟩)⁴`. -/
noncomputable def bargmann4 (U : Triple) : ℂ :=
  ∑ x : I6 × I6 × I6, bargmann U x.1 x.2.1 x.2.2 ^ 4

/-! ### Invariance -/

lemma monomial_conjTranspose_mul_mul_monomial (σ τ : Equiv.Perm I6) (c e : I6 → ℂ) (X : Mat6)
    (i j : I6) :
    ((monomial σ c)ᴴ * X * monomial τ e) i j = star (c i) * X (σ i) (τ j) * e j := by
  rw [mul_monomial_apply, monomial_conjTranspose, monomial_mul_apply]
  simp

lemma gram_frame_monomial {W A B M N : Mat6} (hW : IsUnitary W) :
    (W * A * M)ᴴ * (W * B * N) = Mᴴ * (Aᴴ * B) * N := by
  rw [conjTranspose_mul, conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Wᴴ W, hW.2, Matrix.one_mul]

/-- Common unitary, column permutations and column phases (no permutation of the bases)
leave the invariant unchanged. -/
theorem bargmann4_frame {U V : Triple} {W : Mat6} {M : Fin 3 → Mat6} (hW : IsUnitary W)
    (hM : ∀ k, IsMonomial (M k)) (hV : ∀ k, V k = W * U k * M k) :
    bargmann4 V = bargmann4 U := by
  choose σ c hc hMe using hM
  have hX : ∀ k l i j, ((V k)ᴴ * V l) i j =
      star (c k i) * ((U k)ᴴ * U l) (σ k i) (σ l j) * c l j := by
    intro k l i j
    rw [hV k, hV l, gram_frame_monomial hW, hMe k, hMe l,
      monomial_conjTranspose_mul_mul_monomial]
  have hb : ∀ e f g, bargmann V e f g = bargmann U (σ 0 e) (σ 1 f) (σ 2 g) := by
    intro e f g
    simp only [bargmann, hX]
    have h0 := star_mul_self_of_normSq (hc 0 e)
    have h1 := star_mul_self_of_normSq (hc 1 f)
    have h2 := star_mul_self_of_normSq (hc 2 g)
    linear_combination (((U 0)ᴴ * U 1) (σ 0 e) (σ 1 f) * ((U 1)ᴴ * U 2) (σ 1 f) (σ 2 g) *
      ((U 2)ᴴ * U 0) (σ 2 g) (σ 0 e)) *
      (star (c 1 f) * c 1 f * star (c 2 g) * c 2 g * h0 + star (c 2 g) * c 2 g * h1 + h2)
  simp only [bargmann4, hb]
  exact Equiv.sum_comp ((σ 0).prodCongr ((σ 1).prodCongr (σ 2)))
    (fun x => bargmann U x.1 x.2.1 x.2.2 ^ 4)

lemma star_gram (A B : Mat6) (i j : I6) : star ((Aᴴ * B) i j) = (Bᴴ * A) j i := by
  rw [← conjTranspose_apply, conjTranspose_mul, conjTranspose_conjTranspose]

/-- The cyclic relabelling `(e, f, g) ↦ (g, e, f)`. -/
def cycEquiv : I6 × I6 × I6 ≃ I6 × I6 × I6 where
  toFun x := (x.2.2, x.1, x.2.1)
  invFun x := (x.2.1, x.2.2, x.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The relabelling `(e, f, g) ↦ (f, e, g)`. -/
def swapEquiv : I6 × I6 × I6 ≃ I6 × I6 × I6 where
  toFun x := (x.2.1, x.1, x.2.2)
  invFun x := (x.2.1, x.1, x.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

lemma sum_cyc (F : I6 → I6 → I6 → ℂ) :
    ∑ x : I6 × I6 × I6, F x.2.2 x.1 x.2.1 = ∑ x : I6 × I6 × I6, F x.1 x.2.1 x.2.2 :=
  Equiv.sum_comp cycEquiv (fun x => F x.1 x.2.1 x.2.2)

lemma sum_cyc2 (F : I6 → I6 → I6 → ℂ) :
    ∑ x : I6 × I6 × I6, F x.2.1 x.2.2 x.1 = ∑ x : I6 × I6 × I6, F x.1 x.2.1 x.2.2 :=
  Equiv.sum_comp cycEquiv.symm (fun x => F x.1 x.2.1 x.2.2)

lemma sum_swap (F : I6 → I6 → I6 → ℂ) :
    ∑ x : I6 × I6 × I6, F x.2.1 x.1 x.2.2 = ∑ x : I6 × I6 × I6, F x.1 x.2.1 x.2.2 :=
  Equiv.sum_comp swapEquiv (fun x => F x.1 x.2.1 x.2.2)

/-- The relabelling `(e, f, g) ↦ (e, g, f)`. -/
def swap23Equiv : I6 × I6 × I6 ≃ I6 × I6 × I6 where
  toFun x := (x.1, x.2.2, x.2.1)
  invFun x := (x.1, x.2.2, x.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The relabelling `(e, f, g) ↦ (g, f, e)`. -/
def swap13Equiv : I6 × I6 × I6 ≃ I6 × I6 × I6 where
  toFun x := (x.2.2, x.2.1, x.1)
  invFun x := (x.2.2, x.2.1, x.1)
  left_inv _ := rfl
  right_inv _ := rfl

lemma sum_swap23 (F : I6 → I6 → I6 → ℂ) :
    ∑ x : I6 × I6 × I6, F x.1 x.2.2 x.2.1 = ∑ x : I6 × I6 × I6, F x.1 x.2.1 x.2.2 :=
  Equiv.sum_comp swap23Equiv (fun x => F x.1 x.2.1 x.2.2)

lemma sum_swap13 (F : I6 → I6 → I6 → ℂ) :
    ∑ x : I6 × I6 × I6, F x.2.2 x.2.1 x.1 = ∑ x : I6 × I6 × I6, F x.1 x.2.1 x.2.2 :=
  Equiv.sum_comp swap13Equiv (fun x => F x.1 x.2.1 x.2.2)

lemma star_bargmann4 (U : Triple) :
    star (bargmann4 U) = ∑ x : I6 × I6 × I6, star (bargmann U x.1 x.2.1 x.2.2) ^ 4 := by
  rw [bargmann4, star_sum]; simp [star_pow]

/-- Permuting the three bases leaves the invariant unchanged (even permutations) or
conjugates it (odd permutations). -/
theorem bargmann4_perm (U : Triple) (π : Equiv.Perm (Fin 3)) :
    bargmann4 (fun k => U (π k)) = bargmann4 U ∨
      bargmann4 (fun k => U (π k)) = star (bargmann4 U) := by
  have hb : ∀ e f g, bargmann (fun k => U (π k)) e f g =
      ((U (π 0))ᴴ * U (π 1)) e f * ((U (π 1))ᴴ * U (π 2)) f g *
        ((U (π 2))ᴴ * U (π 0)) g e := fun _ _ _ => rfl
  have hinj := π.injective
  have v : ∀ k : Fin 3, π k = 0 ∨ π k = 1 ∨ π k = 2 := fun k => by
    rcases π k with ⟨n, hn⟩; interval_cases n <;> simp
  rw [star_bargmann4]
  simp only [bargmann4, hb]
  rcases v 0 with h0 | h0 | h0 <;> rcases v 1 with h1 | h1 | h1 <;>
    rcases v 2 with h2 | h2 | h2 <;>
    first
    | (exfalso; have := hinj (h0.trans h1.symm); exact absurd this (by decide))
    | (exfalso; have := hinj (h0.trans h2.symm); exact absurd this (by decide))
    | (exfalso; have := hinj (h1.trans h2.symm); exact absurd this (by decide))
    | skip
  all_goals simp only [h0, h1, h2]
  · left; rfl
  · right
    have := sum_swap23 (fun e f g => star (bargmann U e f g) ^ 4)
    rw [← this]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [bargmann, star_mul', star_gram]
    ring
  · right
    have := sum_swap (fun e f g => star (bargmann U e f g) ^ 4)
    rw [← this]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [bargmann, star_mul', star_gram]
    ring
  · left
    have := sum_cyc (fun e f g => bargmann U e f g ^ 4)
    rw [← this]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [bargmann]; ring
  · left
    have := sum_cyc2 (fun e f g => bargmann U e f g ^ 4)
    rw [← this]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [bargmann]; ring
  · right
    have := sum_swap13 (fun e f g => star (bargmann U e f g) ^ 4)
    rw [← this]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [bargmann, star_mul', star_gram]
    ring

/-- **Invariance**: equivalent triples have equal or complex-conjugate invariants. -/
theorem bargmann4_of_tripleEquiv {U V : Triple} (h : TripleEquiv U V) :
    bargmann4 V = bargmann4 U ∨ bargmann4 V = star (bargmann4 U) := by
  obtain ⟨W, π, M, hW, hM, hV⟩ := h
  rw [bargmann4_frame (U := fun k => U (π k)) hW hM hV]
  exact bargmann4_perm U π

/-- The reality of the invariant is an invariant of triple equivalence. -/
theorem im_bargmann4_eq_zero_iff {U V : Triple} (h : TripleEquiv U V) :
    (bargmann4 V).im = 0 ↔ (bargmann4 U).im = 0 := by
  rcases bargmann4_of_tripleEquiv h with e | e <;> rw [e]
  simp [Complex.conj_im]

lemma conjM_gram (A B : Mat6) (i j : I6) : ((conjM A)ᴴ * conjM B) i j = star ((Aᴴ * B) i j) := by
  rw [← conjM_conjTranspose, ← conjM_mul]; rfl

/-- Entrywise conjugation of all three bases conjugates the invariant. -/
theorem bargmann4_conjTriple (U : Triple) : bargmann4 (conjTriple U) = star (bargmann4 U) := by
  rw [star_bargmann4, bargmann4]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  simp only [bargmann, conjTriple, conjM_gram, star_mul']

/-! ### Family members are equivalent to their complex conjugates -/

lemma star_ω_pow_neg (t s : I3) : star (ω ^ (t.val * s.val)) = ω ^ (t.val * (-s).val) := by
  rw [star_ω_pow, ω_pow_mod, ω_pow_mod (t.val * (-s).val)]
  congr 1
  fin_cases t <;> fin_cases s <;> decide

/-- The common unitary: swap the two coordinates of every eigenspace, with phases `±D̄`. -/
noncomputable def conjW (d : I3 → ℂ) : Mat6 :=
  monomial (Equiv.sumComm I3 I3) (Sum.elim (fun t => -star (d t)) (fun t => star (d t)))

lemma isMonomial_conjW {d : I3 → ℂ} (hd : UnitVec d) : IsMonomial (conjW d) :=
  ⟨_, _, fun i => by rcases i with t | t <;> simp [hd t], rfl⟩

/-- Column operation on `U₂`: exchange the two orbits, negate the position, signs `(-1, 1)`. -/
noncomputable def conjQH : Mat6 := monomial swapNeg (Sum.elim (fun _ => -1) (fun _ => 1))

/-- Column operation on `U₃`: exchange the two orbits, negate the position, signs `(1, -1)`. -/
noncomputable def conjQK : Mat6 := monomial swapNeg (Sum.elim (fun _ => 1) (fun _ => -1))

lemma isMonomial_conjQH : IsMonomial conjQH :=
  ⟨_, _, fun i => by rcases i with t | t <;> simp, rfl⟩

lemma isMonomial_conjQK : IsMonomial conjQK :=
  ⟨_, _, fun i => by rcases i with t | t <;> simp, rfl⟩

lemma conjW_mul_apply (d : I3 → ℂ) (X : Mat6) (t : I3) (j : I6) :
    (conjW d * X) (Sum.inl t) j = star (d t) * X (Sum.inr t) j ∧
      (conjW d * X) (Sum.inr t) j = -star (d t) * X (Sum.inl t) j := by
  constructor <;> rw [conjW, monomial_mul_apply] <;> rfl

lemma swapNeg_inl (s : I3) : swapNeg (Sum.inl s) = Sum.inr (-s) := rfl
lemma swapNeg_inr (s : I3) : swapNeg (Sum.inr s) = Sum.inl (-s) := rfl

lemma conjM_symH {d : I3 → ℂ} (hd : UnitVec d) : conjM (symH d) = conjW d * symH d * conjQH := by
  ext i j
  rw [conjQH, mul_monomial_apply]
  rcases i with t | t <;> rcases j with s | s
  · rw [(conjW_mul_apply d _ t _).1, swapNeg_inl]
    simp only [conjM, Matrix.map_apply, symH, fromBlocks_apply₁₁, fromBlocks_apply₂₂, F3_apply,
      Matrix.neg_apply, diagonal_mul, Sum.elim_inl]
    rw [show (starRingEnd ℂ) (ω ^ (t.val * s.val)) = star (ω ^ (t.val * s.val)) from rfl,
      star_ω_pow_neg]
    have := star_mul_self_of_normSq (hd t)
    linear_combination (-(ω ^ (t.val * (-s).val))) * this
  · rw [(conjW_mul_apply d _ t _).1, swapNeg_inr]
    simp only [conjM, Matrix.map_apply, symH, fromBlocks_apply₁₂, fromBlocks_apply₂₁, F3_apply,
      diagonal_mul, Sum.elim_inr, map_mul]
    rw [show (starRingEnd ℂ) (ω ^ (t.val * s.val)) = star (ω ^ (t.val * s.val)) from rfl,
      star_ω_pow_neg]
    simp
  · rw [(conjW_mul_apply d _ t _).2, swapNeg_inl]
    simp only [conjM, Matrix.map_apply, symH, fromBlocks_apply₂₁, fromBlocks_apply₁₂, F3_apply,
      diagonal_mul, Sum.elim_inl]
    rw [show (starRingEnd ℂ) (ω ^ (t.val * s.val)) = star (ω ^ (t.val * s.val)) from rfl,
      star_ω_pow_neg]
    have := star_mul_self_of_normSq (hd t)
    linear_combination (-(ω ^ (t.val * (-s).val))) * this
  · rw [(conjW_mul_apply d _ t _).2, swapNeg_inr]
    simp only [conjM, Matrix.map_apply, symH, fromBlocks_apply₂₂, fromBlocks_apply₁₁, F3_apply,
      Matrix.neg_apply, diagonal_mul, Sum.elim_inr, map_neg, map_mul]
    rw [show (starRingEnd ℂ) (ω ^ (t.val * s.val)) = star (ω ^ (t.val * s.val)) from rfl,
      star_ω_pow_neg]
    simp

lemma conjM_famK {d : I3 → ℂ} (hd : UnitVec d) (r s : I3 → ℂ) :
    conjM (famK d r s) = conjW d * famK d r s * conjQK := by
  ext i j
  rw [conjQK, mul_monomial_apply]
  rcases i with t | t <;> rcases j with s' | s'
  · rw [(conjW_mul_apply d _ t _).1, swapNeg_inl]
    simp only [conjM, Matrix.map_apply, famK, fromBlocks_apply₁₁, fromBlocks_apply₂₂, F3_apply,
      diagonal_mul, Sum.elim_inl, Pi.mul_apply, Pi.star_apply, map_mul]
    rw [show (starRingEnd ℂ) (ω ^ (t.val * s'.val)) = star (ω ^ (t.val * s'.val)) from rfl,
      star_ω_pow_neg]
    have := star_mul_self_of_normSq (hd t)
    simp only [Complex.star_def] at this ⊢
    linear_combination (-((starRingEnd ℂ) (r t) * ω ^ (t.val * (-s').val))) * this
  · rw [(conjW_mul_apply d _ t _).1, swapNeg_inr]
    simp only [conjM, Matrix.map_apply, famK, fromBlocks_apply₁₂, fromBlocks_apply₂₁, F3_apply,
      Matrix.neg_apply, diagonal_mul, Sum.elim_inr, Pi.mul_apply, Pi.star_apply, map_neg, map_mul]
    rw [show (starRingEnd ℂ) (ω ^ (t.val * s'.val)) = star (ω ^ (t.val * s'.val)) from rfl,
      star_ω_pow_neg]
    simp only [Complex.star_def, Complex.conj_conj]
    ring
  · rw [(conjW_mul_apply d _ t _).2, swapNeg_inl]
    simp only [conjM, Matrix.map_apply, famK, fromBlocks_apply₂₁, fromBlocks_apply₁₂, F3_apply,
      Matrix.neg_apply, diagonal_mul, Sum.elim_inl, Pi.mul_apply, Pi.star_apply, map_mul]
    rw [show (starRingEnd ℂ) (ω ^ (t.val * s'.val)) = star (ω ^ (t.val * s'.val)) from rfl,
      star_ω_pow_neg]
    have := star_mul_self_of_normSq (hd t)
    simp only [Complex.star_def] at this ⊢
    linear_combination (-((starRingEnd ℂ) (s t) * ω ^ (t.val * (-s').val))) * this
  · rw [(conjW_mul_apply d _ t _).2, swapNeg_inr]
    simp only [conjM, Matrix.map_apply, famK, fromBlocks_apply₂₂, fromBlocks_apply₁₁, F3_apply,
      diagonal_mul, Sum.elim_inr, Pi.mul_apply, Pi.star_apply, map_mul]
    rw [show (starRingEnd ℂ) (ω ^ (t.val * s'.val)) = star (ω ^ (t.val * s'.val)) from rfl,
      star_ω_pow_neg]
    simp only [Complex.star_def, Complex.conj_conj]
    ring

/-- **Every explicit family triple is equivalent to its complex conjugate**, by an equivalence
that keeps each basis in place (common unitary `conjW d`, column operations). -/
theorem familyTriple_conj_frame {d : I3 → ℂ} (hd : UnitVec d) (r s : I3 → ℂ) :
    ∀ k, conjTriple (familyTriple d r s) k =
      conjW d * familyTriple d r s k * ![(conjW d)ᴴ, conjQH, conjQK] k := by
  have hW := (isMonomial_conjW hd).isUnitary
  intro k
  fin_cases k
  · show conjM 1 = conjW d * 1 * (conjW d)ᴴ
    rw [conjM_one, Matrix.mul_one, hW.1]
  · show conjM (s6 • symH d) = conjW d * (s6 • symH d) * conjQH
    rw [conjM_smul, show (starRingEnd ℂ) s6 = s6 from s6_star, conjM_symH hd, Matrix.mul_smul,
      Matrix.smul_mul]
  · show conjM (s6 • famK d r s) = conjW d * (s6 • famK d r s) * conjQK
    rw [conjM_smul, show (starRingEnd ℂ) s6 = s6 from s6_star, conjM_famK hd, Matrix.mul_smul,
      Matrix.smul_mul]

/-- The invariant of an explicit family triple is real. -/
theorem bargmann4_familyTriple_im {d : I3 → ℂ} (hd : UnitVec d) (r s : I3 → ℂ) :
    (bargmann4 (familyTriple d r s)).im = 0 := by
  have h := bargmann4_frame (isMonomial_conjW hd).isUnitary
    (M := ![(conjW d)ᴴ, conjQH, conjQK])
    (fun k => by
      fin_cases k
      exacts [(isMonomial_conjW hd).conjTranspose, isMonomial_conjQH, isMonomial_conjQK])
    (familyTriple_conj_frame hd r s)
  rw [bargmann4_conjTriple] at h
  have := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at this
  linarith

/-! ### The invariant of the isolated triple -/

lemma bargmann_std (H K : Mat6) (e f g : I6) :
    bargmann (std H K) e f g = s6 ^ 4 * (H e f * (Hᴴ * K) f g * star (K e g)) := by
  simp only [bargmann, std_zero, std_one, std_two, conjTranspose_one, Matrix.one_mul,
    Matrix.mul_one, conjTranspose_smul, s6_star, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_apply, smul_eq_mul, conjTranspose_apply]
  ring

lemma bargmann4_std (H K : Mat6) :
    bargmann4 (std H K) =
      s6 ^ 16 *
        ∑ x : I6 × I6 × I6, (H x.1 x.2.1 * (Hᴴ * K) x.2.1 x.2.2 * star (K x.1 x.2.2)) ^ 4 := by
  rw [bargmann4, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [bargmann_std]; ring

/-- The transition of the isolated triple: `(F₂ ⊗ F₃)ᴴ K = [[(1+i)C, (1-i)C], [(1-i)C, (1+i)C]]`
with `C = F₃ᴴ diag(1, ω², ω²) F₃`. -/
lemma iso_transition :
    (symH 1)ᴴ * isoK = fromBlocks ((1 + Complex.I) • circ isoVec) ((1 - Complex.I) • circ isoVec)
      ((1 - Complex.I) • circ isoVec) ((1 + Complex.I) • circ isoVec) := by
  rw [isoK_eq, symH_conjTranspose_mul_symK]
  have e1 : isoVec + Complex.I • isoVec = (1 + Complex.I) • isoVec := by rw [add_smul, one_smul]
  have e2 : isoVec - Complex.I • isoVec = (1 - Complex.I) • isoVec := by rw [sub_smul, one_smul]
  simp only [star_one, one_mul, mul_one, e1, e2, circ_smul]

/-- The qutrit factor of a Bargmann product of the isolated triple. -/
noncomputable def qv (t s s' : I3) : ℂ :=
  ω ^ (t.val * s.val) * circ isoVec s s' * star (isoVec t * ω ^ (t.val * s'.val))

lemma pow4_of_eq {T q κ : ℂ} (h : T = κ * q) (hκ : κ ^ 4 = -4) : T ^ 4 = -4 * q ^ 4 := by
  rw [h, mul_pow, hκ]

lemma k_pp : (1 + Complex.I) ^ 4 = -4 := by
  linear_combination (Complex.I ^ 2 + 4 * Complex.I + 5) * Complex.I_sq
lemma k_mm : (1 - Complex.I) ^ 4 = -4 := by
  linear_combination (Complex.I ^ 2 - 4 * Complex.I + 5) * Complex.I_sq
lemma k_ip : (-Complex.I * (1 + Complex.I)) ^ 4 = -4 := by
  rw [mul_pow, k_pp, neg_pow, Complex.I_pow_four]; norm_num
lemma k_im : (Complex.I * (1 - Complex.I)) ^ 4 = -4 := by
  rw [mul_pow, k_mm, Complex.I_pow_four]; norm_num

/-- Each Bargmann product of the isolated triple is `κ · qv` with `κ⁴ = -4`. -/
lemma iso_term (e f g : I6) :
    (symH 1 e f * ((symH 1)ᴴ * isoK) f g * star (isoK e g)) ^ 4 =
      -4 * qv (tIdx e) (tIdx f) (tIdx g) ^ 4 := by
  rw [iso_transition]
  rcases e with t | t <;> rcases f with s | s <;> rcases g with s' | s' <;>
    simp only [symH, isoK, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, diagonal_mul,
      Pi.one_apply, one_mul, F3_apply, isoG_apply, tIdx, star_neg, star_mul', star_I]
  · exact pow4_of_eq (κ := 1 + Complex.I) (by simp only [qv, star_mul']; ring) k_pp
  · exact pow4_of_eq (κ := 1 - Complex.I) (by simp only [qv, star_mul']; ring) k_mm
  · exact pow4_of_eq (κ := 1 - Complex.I) (by simp only [qv, star_mul']; ring) k_mm
  · exact pow4_of_eq (κ := 1 + Complex.I) (by simp only [qv, star_mul']; ring) k_pp
  · exact pow4_of_eq (κ := -Complex.I * (1 + Complex.I)) (by simp only [qv, star_mul']; ring) k_ip
  · exact pow4_of_eq (κ := Complex.I * (1 - Complex.I)) (by simp only [qv, star_mul']; ring) k_im
  · exact pow4_of_eq (κ := Complex.I * (1 - Complex.I)) (by simp only [qv, star_mul']; ring) k_im
  · exact pow4_of_eq (κ := -Complex.I * (1 + Complex.I)) (by simp only [qv, star_mul']; ring) k_ip

lemma sum_tIdx3 (G : I3 → I3 → I3 → ℂ) :
    ∑ x : I6 × I6 × I6, G (tIdx x.1) (tIdx x.2.1) (tIdx x.2.2) =
      8 * ∑ t : I3, ∑ s : I3, ∑ s' : I3, G t s s' := by
  simp only [Fintype.sum_prod_type, Fintype.sum_sum_type, tIdx, Finset.sum_add_distrib]
  ring

lemma sum_qv_pow4 : ∑ t : I3, ∑ s : I3, ∑ s' : I3, qv t s s' ^ 4 = 81 * (1 + 2 * ω) := by
  simp only [qv, Fin.sum_univ_three, circ_apply, isoVec, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, star_mul',
    star_pow, star_ω, Fin.val_zero, Fin.val_one, Fin.val_two, star_one]
  ω_norm

/-- **The invariant of the isolated Fourier triple**: `-2592 (1 + 2ω)/6⁸`. -/
theorem bargmann4_isolatedTriple :
    bargmann4 isolatedTriple = s6 ^ 16 * (-2592 * (1 + 2 * ω)) := by
  rw [isolatedTriple, bargmann4_std]
  congr 1
  simp only [iso_term]
  rw [← Finset.mul_sum, sum_tIdx3 (fun t s s' => qv t s s' ^ 4), sum_qv_pow4]
  ring

lemma bargmann4_isolatedTriple_im : (bargmann4 isolatedTriple).im ≠ 0 := by
  have hs : s6 ^ 16 = (((Real.sqrt 6)⁻¹ ^ 16 : ℝ) : ℂ) := by simp [s6]
  have him : (-2592 * (1 + 2 * ω)).im = -2592 * Real.sqrt 3 := by
    simp [Complex.mul_im]; ring
  rw [bargmann4_isolatedTriple, hs, Complex.im_ofReal_mul, him]
  have h6 : (0 : ℝ) < (Real.sqrt 6)⁻¹ ^ 16 := by positivity
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  exact mul_ne_zero h6.ne' (by nlinarith)

/-- **The isolated Fourier triple is not equivalent to any member of the continuous family.** -/
theorem not_tripleEquiv_isolatedTriple_of_familyMember {V : Triple} (hV : IsFamilyMember V) :
    ¬ TripleEquiv V isolatedTriple := by
  obtain ⟨d, r, s, hd, -, -, rfl, -⟩ := hV
  intro h
  exact bargmann4_isolatedTriple_im
    ((im_bargmann4_eq_zero_iff h).2 (bargmann4_familyTriple_im hd r s))

/-- The two alternatives of `TripleClassification` are mutually exclusive: no MUB triple is
equivalent both to a family member and to the isolated triple. -/
theorem family_and_isolated_exclusive (U : Triple) :
    ¬ ((∃ V, IsFamilyMember V ∧ TripleEquiv U V) ∧ TripleEquiv U isolatedTriple) := by
  rintro ⟨⟨V, hV, hUV⟩, hUI⟩
  exact not_tripleEquiv_isolatedTriple_of_familyMember hV
    (tripleEquiv_trans (tripleEquiv_symm hUV) hUI)

/-! ### The two specified seeds of the isolated triple -/

lemma dephase_smul (c : ℂ) (hc : c ≠ 0) (M : Mat3) (r s : I3) :
    dephase (c • M) r s = dephase M r s := by
  simp only [dephase, Matrix.smul_apply, smul_eq_mul]
  rw [show c * M r s * (c * M 0 0) = (c * c) * (M r s * M 0 0) by ring,
    show c * M r 0 * (c * M 0 s) = (c * c) * (M r 0 * M 0 s) by ring,
    mul_div_mul_left _ _ (mul_ne_zero hc hc)]

lemma circ_isoVec_diag (s : I3) : circ isoVec s s = -1 - 2 * ω := by
  rw [circ_apply]; simp only [Fin.sum_univ_three, isoVec]
  fin_cases s <;> simp <;> ω_norm

lemma circ_isoVec_off {s s' : I3} (h : s ≠ s') : circ isoVec s s' = 2 + ω := by
  rw [circ_apply]; simp only [Fin.sum_univ_three, isoVec]
  fin_cases s <;> fin_cases s' <;> simp at h ⊢ <;> ω_norm

lemma two_add_ω_ne_zero : (2 : ℂ) + ω ≠ 0 := by
  intro h
  have := normSq_add_mul_ω 2 1
  push_cast at this
  rw [one_mul, h] at this; norm_num at this

/-- **The two specified seeds of the isolated triple** (SM §"Seeds of all mutually unbiased
triples"): the upper-left corner of `√6 U₂† U₃` has seed `(2π/3, -2π/3, -2π/3, 2π/3)` and
rows `(1, 4, 2)`, columns `(1, 2, 3)` of `√6 U₃†` have seed `(0, 0, -2π/3, 2π/3)`
(`ω = e^{2πi/3}`, `ω² = e^{-2πi/3}`). -/
theorem seedOf_isolatedTriple :
    seedOf (t6 • ((isolatedTriple 1)ᴴ * isolatedTriple 2)).toBlocks₁₁ = ![ω, ω ^ 2, ω ^ 2, ω] ∧
      seedOf (corner142 (t6 • (isolatedTriple 2)ᴴ)) = ![1, 1, ω ^ 2, ω] := by
  have h2 := two_add_ω_ne_zero
  constructor
  · have e : t6 • ((isolatedTriple 1)ᴴ * isolatedTriple 2) = s6 • ((symH 1)ᴴ * isoK) := by
      rw [isolatedTriple, std_one, std_two, conjTranspose_smul, s6_star, Matrix.smul_mul,
        Matrix.mul_smul, smul_smul, smul_smul, t6_s6_s6]
    have hκ : s6 * (1 + Complex.I) ≠ 0 := mul_ne_zero s6_ne_zero (by
      intro h; have := congrArg Complex.re h; simp at this)
    rw [e, iso_transition, fromBlocks_smul, toBlocks_fromBlocks₁₁, smul_smul]
    funext i
    fin_cases i <;>
      simp only [seedOf, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        Matrix.cons_val_three] <;>
      rw [dephase_smul _ hκ] <;>
      simp only [dephase, circ_isoVec_diag,
        circ_isoVec_off (show (1 : I3) ≠ 0 by decide),
        circ_isoVec_off (show (0 : I3) ≠ 1 by decide),
        circ_isoVec_off (show (0 : I3) ≠ 2 by decide),
        circ_isoVec_off (show (1 : I3) ≠ 2 by decide),
        circ_isoVec_off (show (2 : I3) ≠ 0 by decide),
        circ_isoVec_off (show (2 : I3) ≠ 1 by decide)] <;>
      rw [div_eq_iff (mul_ne_zero h2 h2)] <;> ω_norm
  · have e : t6 • (isolatedTriple 2)ᴴ = isoKᴴ := by
      rw [isolatedTriple, std_two, conjTranspose_smul, s6_star, smul_smul, mul_comm t6 s6,
        s6_mul_t6, one_smul]
    have hv : ∀ t, (starRingEnd ℂ) (isoVec t) ≠ 0 := fun t => by
      rw [map_ne_zero]; exact ne_zero_of_normSq (unitVec_isoVec t)
    have := hv 0; have := hv 1; have := hv 2
    rw [e]
    funext i
    fin_cases i <;>
      simp [seedOf, dephase, corner142, isoK, isoG_apply, conj_ω] <;> field_simp <;> ω_norm

/-! ### The classification in terms of the seed parametrization -/

/-- `U` is equivalent to a seed triple of SM §"Seeds of all mutually unbiased triples". -/
def IsSeedClass (U : Triple) : Prop :=
  ∃ (θ₁ θ₂ : ℝ) (ℓ : ℤ) (ρ : Fin 3 → ℂ) (ε : I3 → ℤˣ), InDomain θ₁ θ₂ ℓ ∧
    IsRootTriple (seedσ θ₁ θ₂ ℓ) ρ ∧ TripleEquiv U (seedTriple θ₁ θ₂ ℓ ρ ε)

/-- The classification with the explicit parametrization: every MUB triple is equivalent to
a seed triple with parameters in the domain, or to the isolated triple, **and not both**. -/
def SeedClassification : Prop :=
  ∀ U : Triple, IsMUBTriple U → Xor (IsSeedClass U) (TripleEquiv U isolatedTriple)

lemma xor_of_or {U : Triple}
    (h : (∃ V, IsFamilyMember V ∧ TripleEquiv U V) ∨ TripleEquiv U isolatedTriple) :
    Xor (IsSeedClass U) (TripleEquiv U isolatedTriple) := by
  have hex := family_and_isolated_exclusive U
  have e : IsSeedClass U ↔ ∃ V, IsFamilyMember V ∧ TripleEquiv U V :=
    (exists_familyMember_iff_seed U).symm
  rw [Xor, e]
  rcases h with h | h
  · exact Or.inl ⟨h, fun h' => hex ⟨h, h'⟩⟩
  · exact Or.inr ⟨h, fun h' => hex ⟨h', h⟩⟩

/-- `TripleClassification` is equivalent to its sharpened seed form. -/
theorem tripleClassification_iff_seedClassification :
    TripleClassification ↔ SeedClassification := by
  constructor
  · intro h U hU; exact xor_of_or (h U hU)
  · intro h U hU
    rcases h U hU with ⟨h1, -⟩ | ⟨h2, -⟩
    · exact Or.inl ((exists_familyMember_iff_seed U).2 h1)
    · exact Or.inr h2

/-- **Main theorem, seed form** (under the certificate hypotheses (H1)–(H3)): every MUB triple
of `ℂ⁶` is equivalent to exactly one of: a seed triple `seedTriple θ₁ θ₂ ℓ ρ ε` with
`(θ₁, θ₂, ℓ)` in the domain, or the isolated Fourier triple. -/
theorem mubTriple_seedClassification {ι : Type} {piece : ι → Set Mat6} {ordering : ι → Prop}
    (C : TripleCertificate piece ordering) : SeedClassification :=
  tripleClassification_iff_seedClassification.1 (mubTriple_classification C)

/-- **Without hypotheses**: every MUB triple with an order-three symmetry is equivalent to
exactly one of a seed triple (parameters in the domain) and the isolated triple. -/
theorem symmetric_seedClassification (U : Triple) (hU : IsMUBTriple U)
    (hS : HasOrder3Symmetry U) : Xor (IsSeedClass U) (TripleEquiv U isolatedTriple) :=
  xor_of_or (symmetricRecognition U hU hS)

end MUBTriples
