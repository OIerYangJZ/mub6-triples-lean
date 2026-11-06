import MUBTriples.Assembly
import MUBTriples.Recognition.Isolated

/-!
# Main theorem: classification of MUB triples in `ℂ⁶` (Theorem `all-mubs`, item 3)

`mubTriple_classification`: from the finite certificate facts (H1)–(H3)
(`TripleCertificate`) every MUB triple of `ℂ⁶` is equivalent to a member of the continuous
family or to the isolated Fourier triple.  The algebraic recognition of symmetric triples
(`symmetricRecognition`) is proved, not assumed.

`no_four_mubs_of_classification`: the classification together with the theorem of Jaming,
Matolcsi, Móra, Szöllősi and Weiner (2009) that no pair `{I₆, symH d/√6}` (the transposed
Fourier family) extends to four MUBs (hypothesis `NoQuartetThroughFourierFamily`) gives
`¬ FourMUBs`, since both types of triple contain such a pair.
-/

open Matrix Hadamard6

namespace MUBTriples

/-- **Classification of MUB triples** (the computer-assisted part as hypotheses `C`). -/
theorem mubTriple_classification {ι : Type} {piece : ι → Set Mat6} {ordering : ι → Prop}
    (C : TripleCertificate piece ordering) : TripleClassification :=
  tripleClassification_of_certificate C symmetricRecognition



/-- Jaming–Matolcsi–Móra–Szöllősi–Weiner (2009): the pair `{I₆, symH d/√6}`, `symH d`
the transposed Fourier family `[[F₃, D F₃], [F₃, -D F₃]]`, is not part of four MUBs. -/
def NoQuartetThroughFourierFamily : Prop :=
  ∀ d : I3 → ℂ, UnitVec d → ¬ ∃ K L : Mat6, IsUnitary K ∧ IsUnitary L ∧
    Unbiased 1 K ∧ Unbiased 1 L ∧ Unbiased (s6 • symH d) K ∧ Unbiased (s6 • symH d) L ∧
    Unbiased K L

/-- A fourth basis follows a triple through a triple equivalence. -/
lemma fourth_basis_transport {U V : Triple} {L : Mat6} (h : TripleEquiv U V)
    (hL : IsUnitary L) (hUL : ∀ k, Unbiased (U k) L) :
    ∃ L', IsUnitary L' ∧ ∀ k, Unbiased (V k) L' := by
  obtain ⟨W, π, M, hW, hM, hV⟩ := h
  refine ⟨W * L, hW.mul hL, fun k => ?_⟩
  intro i j
  rw [hV k, Matrix.mul_assoc W, gram_frame hW.2]
  have := unbiased_mul_monomial (hM k) isMonomial_one (hUL (π k))
  rw [Matrix.mul_one] at this
  exact this i j

/-- **No four MUBs in `ℂ⁶`** from the triple classification and the Fourier-family result. -/
theorem no_four_mubs_of_classification (hC : TripleClassification)
    (hJ : NoQuartetThroughFourierFamily) : ¬ FourMUBs := by
  rintro ⟨U, hU, hUb⟩
  set U3 : Triple := ![U 0, U 1, U 2]
  have hU3 : IsMUBTriple U3 := by
    refine ⟨fun k => ?_, fun k l hkl => ?_⟩
    · fin_cases k <;> simp [U3, hU]
    · fin_cases k <;> fin_cases l <;> simp [U3] at hkl ⊢ <;> exact hUb _ _ (by decide)
  have hL : ∀ k, Unbiased (U3 k) (U 3) := by
    intro k; fin_cases k <;> simp [U3] <;> exact hUb _ _ (by decide)
  -- a triple of either type contains the pair `{I₆, symH d/√6}`
  have key : ∀ V : Triple, (∃ d : I3 → ℂ, UnitVec d ∧ V 0 = 1 ∧ V 1 = s6 • symH d) →
      IsMUBTriple V → TripleEquiv U3 V → False := by
    rintro V ⟨d, hd, hV0, hV1⟩ hV hE
    obtain ⟨L', hL', hVL⟩ := fourth_basis_transport hE (hU 3) hL
    apply hJ d hd
    refine ⟨V 2, L', hV.1 2, hL', ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hV0]; exact hV.2 0 2 (by decide)
    · rw [← hV0]; exact hVL 0
    · rw [← hV1]; exact hV.2 1 2 (by decide)
    · rw [← hV1]; exact hVL 1
    · exact hVL 2
  rcases hC U3 hU3 with ⟨V, ⟨d, r, s, hd, hr, hs, rfl, hV⟩, hE⟩ | hE
  · exact key _ ⟨d, hd, rfl, rfl⟩ hV hE
  · exact key _ ⟨1, unitVec_one, rfl, rfl⟩ isolatedTriple_isMUBTriple hE

/-- **No four MUBs in `ℂ⁶`** from the certificate facts and the Fourier-family theorem of
Jaming et al. -/
theorem no_four_mubs {ι : Type} {piece : ι → Set Mat6} {ordering : ι → Prop}
    (C : TripleCertificate piece ordering) (hJ : NoQuartetThroughFourierFamily) :
    ¬ FourMUBs :=
  no_four_mubs_of_classification (mubTriple_classification C) hJ

end MUBTriples
