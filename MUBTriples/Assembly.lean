import MUBTriples.Score
import MUBTriples.Statement

/-!
# The assembly theorem: certificate facts ⇒ every MUB triple has the order-three symmetry

This formalizes the logical skeleton of SM Proposition `tc-certificate` together
with SM Lemma `minimum-transition`.

## Hypotheses (`TripleCertificate`)

The cover pieces are an arbitrary family `piece : ι → Set Mat6` (in the paper: the
2,775 seed balls, each the set of matrices reconstructed from the ball, together with
the Fourier chart), and `ordering : ι → Prop` marks the pieces whose certificate only
covers triples whose first transition minimizes `Γ_F` (ball IDs 1035, 1217, 1622,
2705).

* (H1) `covered`: every Hadamard matrix not in Tao's orbit becomes, after one of the
  operations `Γ = {id, conj, ᵀ, conj ∘ ᵀ}`, equivalent to a matrix of some piece.
  (Same shape as `NoFourMUBs.Inputs.covered`; in the paper this is the phase-ball
  cover + boundary transfers + connectedness, Theorem `connected`, SM Prop. `finite`.)
* (H2) `classified`: for every piece `p`, every `H ∈ piece p` and every `K` such that
  `{I₆, H/√6, K/√6}` is a MUB triple — and, if `ordering p`, such that `H` has the least
  `Γ_F` of the three transitions (ties included) — the triple has an order-three
  symmetry.  ("Excluded" patterns are the case that no such `K` exists.)  For MUB triples
  `MinTransition` is SM Eq. `minimum-transition` with the paper's literal `Γ_F`
  (`minTransition_iff_paper`, `classified_of_paper` in `MUBTriples.ScoreFormula`).
* (H3) `taoNoThird`: if `H` is in Tao's orbit, `{I₆, H/√6}` has no third unbiased basis
  (Brierley–Weigert 2009).

## Conclusion

`every_mubTriple_hasOrder3Symmetry`: under (H1)–(H3) every MUB triple of `ℂ⁶` has an
order-three symmetry.  Combined with the algebraic recognition
(`SymmetricRecognition`) this gives `TripleClassification`
(`tripleClassification_of_certificate`).
-/

open Matrix Hadamard6

namespace MUBTriples

/-- `G` is the image of `H` under an element of `Γ = {id, conj, ᵀ, conj ∘ ᵀ}`
(as `NoFourMUBs.InGamma`). -/
def InGamma (H G : Mat6) : Prop := G = H ∨ G = conjM H ∨ G = Hᵀ ∨ G = conjM Hᵀ

/-- SM Eq. `minimum-transition`: `H` has the least score among the three transitions
`H`, `K`, `Hᴴ K/√6` of `{I₆, H/√6, K/√6}` (ties included). -/
def MinTransition (H K : Mat6) : Prop := ΓF H ≤ ΓF K ∧ ΓF H ≤ ΓF (s6 • (Hᴴ * K))

/-- The finite certificate facts, stated as hypotheses (H1)–(H3). -/
structure TripleCertificate {ι : Type} (piece : ι → Set Mat6) (ordering : ι → Prop) : Prop where
  /-- (H1) Every non-Tao Hadamard class is represented in a cover piece, up to `Γ`. -/
  covered : ∀ H, Hadamard6.IsHadamard H → ¬ IsTaoOrbit H →
    ∃ p G H', InGamma H G ∧ H' ∈ piece p ∧ Equivalent G H'
  /-- (H2) On every piece every triple (minimizing `Γ_F` on the ordering pieces) has an
  order-three symmetry. -/
  classified : ∀ p, ∀ H ∈ piece p, ∀ K, IsMUBTriple (std H K) →
    (ordering p → MinTransition H K) → HasOrder3Symmetry (std H K)
  /-- (H3) Tao's matrix admits no third basis. -/
  taoNoThird : ∀ H, IsTaoOrbit H → ∀ K, ¬ IsMUBTriple (std H K)

/-! ### Transitions of a triple -/

/-- The transition Hadamard `√6 Uᵢᴴ Uⱼ`. -/
noncomputable def tr (U : Triple) (i j : Fin 3) : Mat6 := t6 • ((U i)ᴴ * U j)

lemma tr_conjTranspose (U : Triple) (i j : Fin 3) : (tr U i j)ᴴ = tr U j i := by
  simp [tr, conjTranspose_smul, t6_star]

lemma ΓF_tr_symm (U : Triple) (i j : Fin 3) : ΓF (tr U j i) = ΓF (tr U i j) := by
  rw [← tr_conjTranspose, ΓF_conjTranspose]

lemma tr_third {U : Triple} {i : Fin 3} (hi : IsUnitary (U i)) (j k : Fin 3) :
    s6 • ((tr U i j)ᴴ * tr U i k) = tr U j k := by
  rw [tr_conjTranspose]
  simp only [tr, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [show (U j)ᴴ * U i * ((U i)ᴴ * U k) = (U j)ᴴ * (U i * (U i)ᴴ) * U k by
    simp only [Matrix.mul_assoc], hi.1, Matrix.mul_one]
  congr 1
  rw [← mul_assoc, s6_mul_t6, one_mul]

lemma tripleEquiv_frame {U : Triple} (hU : IsMUBTriple U) (π : Equiv.Perm (Fin 3)) :
    TripleEquiv U (std (tr U (π 0) (π 1)) (tr U (π 0) (π 2))) := by
  refine ⟨(U (π 0))ᴴ, π, fun _ => 1, (hU.1 _).conjTranspose, fun _ => isMonomial_one,
    fun k => ?_⟩
  rw [Matrix.mul_one]
  fin_cases k
  · exact ((hU.1 _).2).symm
  · show s6 • tr U (π 0) (π 1) = _
    rw [tr, smul_smul, s6_mul_t6, one_smul]; rfl
  · show s6 • tr U (π 0) (π 2) = _
    rw [tr, smul_smul, s6_mul_t6, one_smul]; rfl

lemma three_min {a b c : ℝ} (h1 : ¬ (a ≤ b ∧ a ≤ c)) (h2 : ¬ (b ≤ a ∧ b ≤ c)) :
    c ≤ a ∧ c ≤ b := by
  by_contra hc
  rcases le_total a b with hab | hab <;> rcases le_total a c with hac | hac <;>
    rcases le_total b c with hbc | hbc <;>
    first | exact h1 ⟨hab, hac⟩ | exact h2 ⟨hab, hbc⟩ |
      exact hc ⟨by linarith, by linarith⟩

/-- **Lemma `minimum-transition`, first half.**  Every MUB triple is equivalent to a
triple `{I₆, H/√6, K/√6}` whose first transition `H` minimizes `Γ_F`. -/
theorem exists_minTransition_frame {U : Triple} (hU : IsMUBTriple U) :
    ∃ H K, TripleEquiv U (std H K) ∧ MinTransition H K := by
  have third : ∀ π : Equiv.Perm (Fin 3),
      s6 • ((tr U (π 0) (π 1))ᴴ * tr U (π 0) (π 2)) = tr U (π 1) (π 2) :=
    fun π => tr_third (hU.1 _) _ _
  set g01 := ΓF (tr U 0 1)
  set g02 := ΓF (tr U 0 2)
  set g12 := ΓF (tr U 1 2)
  by_cases h1 : g01 ≤ g02 ∧ g01 ≤ g12
  · refine ⟨_, _, tripleEquiv_frame hU 1, ?_⟩
    simp only [MinTransition]
    rw [third 1]
    exact h1
  · by_cases h2 : g02 ≤ g01 ∧ g02 ≤ g12
    · refine ⟨_, _, tripleEquiv_frame hU (Equiv.swap 1 2), ?_⟩
      simp only [MinTransition]
      rw [third]
      have e0 : (Equiv.swap (1 : Fin 3) 2) 0 = 0 :=
        Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
      have e1 : (Equiv.swap (1 : Fin 3) 2) 1 = 2 := Equiv.swap_apply_left _ _
      have e2 : (Equiv.swap (1 : Fin 3) 2) 2 = 1 := Equiv.swap_apply_right _ _
      rw [e0, e1, e2, ΓF_tr_symm U 1 2]
      exact h2
    · have h3 : g12 ≤ g01 ∧ g12 ≤ g02 := three_min h1 h2
      refine ⟨_, _, tripleEquiv_frame hU (finRotate 3), ?_⟩
      simp only [MinTransition]
      rw [third]
      have e0 : (finRotate 3) 0 = 1 := rfl
      have e1 : (finRotate 3) 1 = 2 := rfl
      have e2 : (finRotate 3) 2 = 0 := rfl
      rw [e0, e1, e2, ΓF_tr_symm U 0 1, ΓF_tr_symm U 0 2]
      exact h3

/-! ### Transfers: equivalence, conjugation, adjoint -/

/-- Moving the first transition `G` of a triple to an equivalent `H'` by a common
monomial unitary and column operations. -/
lemma equivalent_step {G K H' : Mat6} (hGH : Equivalent G H') :
    ∃ K', TripleEquiv (std G K) (std H' K') ∧
      (MinTransition G K → MinTransition H' K') := by
  obtain ⟨σ, τ, r, c, hr, hc, hH'⟩ := hGH
  set R : Mat6 := monomial σ⁻¹ (fun l => r (σ⁻¹ l))
  set Cm : Mat6 := monomial τ c
  have hR : IsMonomial R := ⟨σ⁻¹, _, fun l => hr _, rfl⟩
  have hC : IsMonomial Cm := ⟨τ, c, hc, rfl⟩
  have hH'eq : H' = R * G * Cm := by
    ext i j
    rw [mul_monomial_apply, monomial_mul_apply, hH']
    simp
  refine ⟨R * K, ⟨R, 1, ![Rᴴ, Cm, 1], hR.isUnitary, fun k => ?_, fun k => ?_⟩, fun hmin => ?_⟩
  · fin_cases k
    exacts [hR.conjTranspose, hC, isMonomial_one]
  · fin_cases k
    · show (1 : Mat6) = R * 1 * Rᴴ
      rw [Matrix.mul_one, hR.isUnitary.1]
    · show s6 • H' = R * (s6 • G) * Cm
      rw [hH'eq, Matrix.mul_smul, Matrix.smul_mul]
    · show s6 • (R * K) = R * (s6 • K) * 1
      rw [Matrix.mul_one, Matrix.mul_smul]
  · have hΓH : ΓF H' = ΓF G := by rw [hH'eq]; exact ΓF_monomial_mul hR hC
    have hΓK : ΓF (R * K) = ΓF K := by
      rw [← Matrix.mul_one (R * K)]; exact ΓF_monomial_mul hR isMonomial_one
    have hΓL : ΓF (s6 • (H'ᴴ * (R * K))) = ΓF (s6 • (Gᴴ * K)) := by
      have e0 : (R * G * Cm)ᴴ * (R * K) = Cmᴴ * (Gᴴ * K) := by
        rw [conjTranspose_mul, conjTranspose_mul]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Rᴴ R K, hR.isUnitary.2, Matrix.one_mul]
      have e : s6 • (H'ᴴ * (R * K)) = Cmᴴ * (s6 • (Gᴴ * K)) * 1 := by
        rw [hH'eq, e0, Matrix.mul_one, Matrix.mul_smul]
      rw [e]; exact ΓF_monomial_mul hC.conjTranspose isMonomial_one
    exact ⟨by rw [hΓH, hΓK]; exact hmin.1, by rw [hΓH, hΓL]; exact hmin.2⟩

lemma std_conj (H K : Mat6) : std (conjM H) (conjM K) = conjTriple (std H K) := by
  funext k
  fin_cases k
  · show (1 : Mat6) = conjM 1
    rw [conjM_one]
  · show s6 • conjM H = conjM (s6 • H)
    rw [conjM_smul, starRingEnd_apply, s6_star]
  · show s6 • conjM K = conjM (s6 • K)
    rw [conjM_smul, starRingEnd_apply, s6_star]

lemma minTransition_conj {H K : Mat6} (h : MinTransition H K) :
    MinTransition (conjM H) (conjM K) := by
  have e : s6 • ((conjM H)ᴴ * conjM K) = conjM (s6 • (Hᴴ * K)) := by
    rw [conjM_smul, starRingEnd_apply, s6_star, conjM_mul, conjM_conjTranspose]
  simp only [MinTransition, e, ΓF_conjM]
  exact h

lemma adjoint_step {H K : Mat6} (hT : IsMUBTriple (std H K)) :
    TripleEquiv (std H K) (std Hᴴ (s6 • (Hᴴ * K))) ∧
      (MinTransition H K → MinTransition Hᴴ (s6 • (Hᴴ * K))) := by
  have hHu : IsUnitary (s6 • H) := hT.1 1
  have hH6 : H * Hᴴ = (6 : ℂ) • (1 : Mat6) := (isUnitary_s6_smul_iff H).1 hHu
  refine ⟨⟨(s6 • H)ᴴ, Equiv.swap 0 1, fun _ => 1, hHu.conjTranspose,
    fun _ => isMonomial_one, fun k => ?_⟩, fun hmin => ?_⟩
  · rw [Matrix.mul_one]
    fin_cases k
    · show (1 : Mat6) = (s6 • H)ᴴ * (s6 • H)
      exact hHu.2.symm
    · show s6 • Hᴴ = (s6 • H)ᴴ * 1
      rw [Matrix.mul_one, conjTranspose_smul, s6_star]
    · show s6 • (s6 • (Hᴴ * K)) = (s6 • H)ᴴ * (s6 • K)
      rw [conjTranspose_smul, s6_star, Matrix.smul_mul, Matrix.mul_smul]
  · have e : s6 • ((Hᴴ)ᴴ * (s6 • (Hᴴ * K))) = K := by
      rw [conjTranspose_conjTranspose, Matrix.mul_smul, smul_smul, ← Matrix.mul_assoc, hH6,
        Matrix.smul_mul, Matrix.one_mul, smul_smul, s6_mul_s6]
      norm_num
    refine ⟨?_, ?_⟩
    · rw [ΓF_conjTranspose]; exact hmin.2
    · rw [e, ΓF_conjTranspose]; exact hmin.1

/-! ### The assembly theorem -/

/-- If the first transition `G` of a MUB triple is equivalent to a matrix of a piece,
(H2) gives the symmetry. -/
lemma sym_of_piece {ι : Type} {piece : ι → Set Mat6} {ordering : ι → Prop}
    (C : TripleCertificate piece ordering) {G K H' : Mat6} {p : ι}
    (hT : IsMUBTriple (std G K)) (hmin : MinTransition G K)
    (hGH : Equivalent G H') (hp : H' ∈ piece p) : HasOrder3Symmetry (std G K) := by
  obtain ⟨K', hE, hmin'⟩ := equivalent_step (K := K) hGH
  have hT' := isMUBTriple_of_tripleEquiv hE hT
  have := C.classified p H' hp K' hT' (fun _ => hmin' hmin)
  exact hasOrder3Symmetry_of_tripleEquiv (tripleEquiv_symm hE) this

lemma sym_of_conj_piece {ι : Type} {piece : ι → Set Mat6} {ordering : ι → Prop}
    (C : TripleCertificate piece ordering) {H K H' : Mat6} {p : ι}
    (hT : IsMUBTriple (std H K)) (hmin : MinTransition H K)
    (hGH : Equivalent (conjM H) H') (hp : H' ∈ piece p) : HasOrder3Symmetry (std H K) := by
  have hT' : IsMUBTriple (std (conjM H) (conjM K)) := by rw [std_conj]; exact hT.conj
  have := sym_of_piece C hT' (minTransition_conj hmin) hGH hp
  rw [std_conj] at this
  have := hasOrder3Symmetry_conj this
  rwa [conjTriple_conjTriple] at this

/-- **Assembly theorem.**  Under the certificate facts (H1)–(H3), every MUB triple in
`ℂ⁶` has an order-three symmetry. -/
theorem every_mubTriple_hasOrder3Symmetry {ι : Type} {piece : ι → Set Mat6}
    {ordering : ι → Prop} (C : TripleCertificate piece ordering)
    (U : Triple) (hU : IsMUBTriple U) : HasOrder3Symmetry U := by
  obtain ⟨H, K, hE, hmin⟩ := exists_minTransition_frame hU
  have hT : IsMUBTriple (std H K) := isMUBTriple_of_tripleEquiv hE hU
  refine hasOrder3Symmetry_of_tripleEquiv (tripleEquiv_symm hE) ?_
  have hH : Hadamard6.IsHadamard H := ((isMUBTriple_std_iff H K).1 hT).1
  have hTao : ¬ IsTaoOrbit H := fun h => C.taoNoThird H h K hT
  obtain ⟨p, G, H', hG, hp, hGH'⟩ := C.covered H hH hTao
  obtain ⟨hE2, hmin2⟩ := adjoint_step hT
  have hT2 := isMUBTriple_of_tripleEquiv hE2 hT
  rcases hG with rfl | rfl | rfl | rfl
  · exact sym_of_piece C hT hmin hGH' hp
  · exact sym_of_conj_piece C hT hmin hGH' hp
  · -- `Hᵀ = conj (Hᴴ)`
    rw [show Hᵀ = conjM Hᴴ by rw [← conjM_transpose, conjM_conjM]] at hGH'
    refine hasOrder3Symmetry_of_tripleEquiv (tripleEquiv_symm hE2) ?_
    exact sym_of_conj_piece C hT2 (hmin2 hmin) hGH' hp
  · rw [conjM_transpose] at hGH'
    refine hasOrder3Symmetry_of_tripleEquiv (tripleEquiv_symm hE2) ?_
    exact sym_of_piece C hT2 (hmin2 hmin) hGH' hp

/-- **Classification of MUB triples from the certificate facts and the algebraic
recognition of symmetric triples.** -/
theorem tripleClassification_of_certificate {ι : Type} {piece : ι → Set Mat6}
    {ordering : ι → Prop} (C : TripleCertificate piece ordering)
    (hrec : SymmetricRecognition) : TripleClassification :=
  fun U hU => hrec U hU (every_mubTriple_hasOrder3Symmetry C U hU)

end MUBTriples
