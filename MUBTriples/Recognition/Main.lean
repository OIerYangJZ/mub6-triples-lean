import MUBTriples.Recognition.Anchor

/-!
# Algebraic recognition of symmetric triples (SM §"Algebraic recognition")

`symmetricRecognition_of_isolated`: every MUB triple with an order-three symmetry is
equivalent to a family member or to the isolated triple, given the last step
(`IsolatedRecognition`: the dependent case with non-constant `w` is the isolated Fourier
triple).  `IsolatedRecognition` is proved in `MUBTriples.Recognition.Isolated`
(`isolatedRecognition`), which also states the unconditional `symmetricRecognition`.
-/

open Matrix Hadamard6

namespace MUBTriples

/-- The last step of the recognition: normal-form triples in the dependent case with
non-constant `w` (SM: `wₜ = ω^j ω^{εt}`, the Gauss-sum case) are equivalent to the
isolated Fourier triple. -/
def IsolatedRecognition : Prop :=
  ∀ x y u v : I3 → ℂ, UnitVec x → UnitVec y → UnitVec u → UnitVec v →
    IsMUBTriple (std (symH x) (symK y u v)) → IsolatedData x y u v →
      TripleEquiv (std (symH x) (symK y u v)) isolatedTriple

/-- **Recognition**, modulo the isolated case. -/
theorem symmetricRecognition_of_isolated (hiso : IsolatedRecognition) : SymmetricRecognition := by
  intro U hU hS
  obtain ⟨x, y, u, v, hx, hy, hu, hv, hE⟩ := normalForm_of_symmetric hU hS
  have hT := isMUBTriple_of_tripleEquiv hE hU
  rcases recognition_dichotomy hx hy hu hv hT with ⟨V, hV, hE'⟩ | hd
  · exact Or.inl ⟨V, hV, tripleEquiv_trans hE hE'⟩
  · exact Or.inr (tripleEquiv_trans hE (hiso x y u v hx hy hu hv hT hd))

end MUBTriples
