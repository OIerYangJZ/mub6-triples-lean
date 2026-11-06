import MUBTriples.Symmetry

/-!
# The two known types of MUB triples and the classification statement

Paper: arXiv 2611.06917v1, Methods Eqs. `methods-isolated-triple-bases` and
`methods-explicit-continuous-bases`; main text Theorem `all-mubs`, item 3.

All bases are written as `H/√6` with an unnormalized matrix `H`, using
`F̂ₙ = Fₙ/√n`, so `F̂₂ ⊗ F̂₃ = symH 1/√6` etc.  Rows and columns are indexed by
`Fin 3 ⊕ Fin 3` with the *qubit index major*: `(a, t) ↦ inl t` for `a = 0` and
`inr t` for `a = 1`, so that `A ⊗ B = [[A₀₀ B, A₀₁ B], [A₁₀ B, A₁₁ B]]`.

## The continuous family (Methods Eq. `methods-explicit-continuous-bases`)

`U₂ = (1/√2) [[F̂₃, D F̂₃], [F̂₃, -D F̂₃]]`,
`U₃ = (1/√2) [[R F̂₃, -D S† F̂₃], [S F̂₃, D R† F̂₃]]`

with diagonal unitaries `D, R, S`.  The paper gives `D, R, S` as explicit
functions of two seed coordinates (SM §"Seeds of all mutually unbiased
triples").  **Here a family member is any MUB triple of this explicit block
form with arbitrary unit diagonals `D, R, S`** (`IsFamilyMember`); the
identification of this set with the image of the paper's `(θ₁, θ₂)`
parametrization is *not* formalized (see `STATUS.md`).

## The isolated Fourier triple (Methods Eq. `methods-isolated-triple-bases`)

`U₂ = F̂₂ ⊗ F̂₃`, `U₃ = [diag(1, i) F̂₂] ⊗ [diag(1, ω², ω²) F̂₃]`.
-/

open Matrix Hadamard6

namespace MUBTriples

/-- Unnormalized `U₃` of the continuous family: `[[R F₃, -D S̄ F₃], [S F₃, D R̄ F₃]]`. -/
noncomputable def famK (d r s : I3 → ℂ) : Mat6 :=
  fromBlocks (diagonal r * F3) (-(diagonal (d * star s) * F3)) (diagonal s * F3)
    (diagonal (d * star r) * F3)

/-- The triple `{I₆, U₂, U₃}` of Methods Eq. `methods-explicit-continuous-bases`. -/
noncomputable def familyTriple (d r s : I3 → ℂ) : Triple := std (symH d) (famK d r s)

/-- Membership in the continuous family: the explicit block form with unit diagonals,
and the three bases are mutually unbiased. -/
def IsFamilyMember (U : Triple) : Prop :=
  ∃ d r s : I3 → ℂ, UnitVec d ∧ UnitVec r ∧ UnitVec s ∧ U = familyTriple d r s ∧ IsMUBTriple U

/-- `diag(1, ω², ω²) F₃`. -/
noncomputable def isoG : Mat3 := diagonal ![1, ω ^ 2, ω ^ 2] * F3

/-- Unnormalized `U₃ = [diag(1,i) F₂] ⊗ [diag(1,ω²,ω²) F₃]`, i.e. `[[G, G], [iG, -iG]]`. -/
noncomputable def isoK : Mat6 :=
  fromBlocks isoG isoG (Complex.I • isoG) (-(Complex.I • isoG))

/-- The isolated Fourier triple `{I₆, F̂₂ ⊗ F̂₃, [diag(1,i)F̂₂] ⊗ [diag(1,ω²,ω²)F̂₃]}`. -/
noncomputable def isolatedTriple : Triple := std (symH 1) isoK

/-- **Conjecture 1 of Matolcsi–Matszangosz–Varga–Weiner; Theorem `all-mubs`, item 3.**
Every MUB triple in `ℂ⁶` is equivalent (common unitary, column phases and permutations,
permutation of the bases; no conjugation) to a member of the continuous family or to the
isolated Fourier triple. -/
def TripleClassification : Prop :=
  ∀ U : Triple, IsMUBTriple U →
    (∃ V, IsFamilyMember V ∧ TripleEquiv U V) ∨ TripleEquiv U isolatedTriple

/-- **Algebraic recognition** (SM §"Algebraic recognition of the symmetric triples"):
every MUB triple with an order-three symmetry is equivalent to a family member or to the
isolated triple. -/
def SymmetricRecognition : Prop :=
  ∀ U : Triple, IsMUBTriple U → HasOrder3Symmetry U →
    (∃ V, IsFamilyMember V ∧ TripleEquiv U V) ∨ TripleEquiv U isolatedTriple

/-- Four mutually unbiased bases of `ℂ⁶` (verbatim `NoFourMUBs.FourMUBs`, MIT License,
Copyright (c) 2026 Joseph Tindall and Mateo Cárdenes Wuttig; see `LICENSE`). -/
def FourMUBs : Prop :=
  ∃ U : Fin 4 → Mat6, (∀ k, IsUnitary (U k)) ∧ ∀ k l, k ≠ l → Unbiased (U k) (U l)

end MUBTriples
