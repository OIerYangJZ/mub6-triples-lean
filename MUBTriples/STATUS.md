# MUBTriples — status (2026-11-06)

Lean 4 formalization of the classification of MUB triples in C^6, arXiv:2611.06917v1
(Cárdenes Wuttig & Tindall), Theorem `all-mubs` item 3 (+ the "no four MUBs" corollary).
Standalone Lake package `mub6_triples`, depending on Mathlib and on `hadamard6_formal`
(commit 57b0302) for `Hadamard6.Mat6` (indexed by `Fin 3 ⊕ Fin 3`), `IsHadamard`, `Equivalent`,
`IsTaoOrbit`.

Build: `lake build` (16 modules, ≈4,000 lines, about a minute on top of a built Mathlib).
**No `sorry`, no `axiom`.** `#print axioms` of every main theorem (`scripts/PrintAxioms.lean`):
`propext, Classical.choice, Quot.sound`.

## Main results

| Lean | Content | Hypotheses |
|---|---|---|
| `MainTheorem.mubTriple_classification` | every MUB triple of C^6 is equivalent to a family member or to the isolated Fourier triple (`TripleClassification`) | `C : TripleCertificate piece ordering` |
| `MainTheorem.no_four_mubs` | `¬ FourMUBs` | `C`, `NoQuartetThroughFourierFamily` (Jaming et al. 2009) |
| `Assembly.every_mubTriple_hasOrder3Symmetry` | certificate ⇒ every MUB triple has an order-3 symmetry (SM Prop. `tc-certificate` + Lemma `minimum-transition`) | `C` |
| `Recognition.Isolated.symmetricRecognition` | every symmetric MUB triple is equivalent to a family member or the isolated triple (SM §"Algebraic recognition") | none |
| `Contraction.symmetry_criterion`, `eq_zero_of_contraction`, `covariance` | SM Eq. `tc-symmetry`, abstract, over real normed spaces (FTC along the segment) | none |
| `KnownTriples.isolatedTriple_isMUBTriple`, `familyTriple_isMUBTriple_iff`, `hasOrder3Symmetry_isolatedTriple/_familyTriple` | sanity: isolated triple is MUB; family block form is MUB ⇔ two circulants flat; both carry the symmetry | none |
| `Score.ΓF_of_equivalent`, `ΓF_conjM`, `ΓF_transpose`, `ΓF_conjTranspose` | invariance of the ordering score Γ_F | none |
| `ScoreFormula.ΓF_exp_eq_ΓFpaper`, `ΓF_eq_ΓFpaper`, `minTransition_iff_paper`, `classified_of_paper` | the Lean Γ_F equals the paper's Eq. `gamma-score` (defined literally as `ΓFpaper`); (H2) may be stated with the literal formula | none |

## Definitions (exact statement)

* `IsUnitary`, `Unbiased` (|(Uᴴ V)ᵢⱼ|² = 1/6), `FourMUBs` — verbatim from `NoFourMUBs.Basic` (MIT);
  `IsMUBTriple`.
* `TripleEquiv U V`: `V k = W * U (π k) * M k`, W unitary, π ∈ S₃, `M k` monomial (column permutation +
  unit phases). **Complex conjugation is NOT included** (the paper's equivalence).
* `HasOrder3Symmetry`: ∃ unitary T, T³ = 1, T fixes the vectors of an anchor basis up to phase
  (`T * U m = U m * diag d`) and acts on each other basis as a phased double three-cycle.
* Family (`IsFamilyMember`): MUB triples `{I, U₂, U₃}` of the explicit form of Methods
  Eq. `methods-explicit-continuous-bases` with **arbitrary** unit diagonals D, R, S.
* Isolated triple: Methods Eq. `methods-isolated-triple-bases` (F̂₂⊗F̂₃, [diag(1,i)F̂₂]⊗[diag(1,ω²,ω²)F̂₃]).
* Γ_F: `Score.ΓF` (symmetric encoding: all ordered quadruples / 4, labels `I6 ≃ ZMod 6`, `|arg|`)
  and `ScoreFormula.ΓFpaper` (literal: i<k, j<l, permutations with a₁=b₁=0, distance to 2πℤ);
  equal by `ΓF_exp_eq_ΓFpaper`.

## Certificate hypotheses (`TripleCertificate piece ordering`, all explicit Props)

* (H1) `covered`: every Hadamard H not in Tao's orbit is, after an element of
  Γ = {id, conj, ᵀ, conj∘ᵀ}, equivalent to some matrix of some piece (2,775 seed balls + Fourier
  chart). Same shape as `NoFourMUBs.Inputs.covered` (discharged there by the seed-atlas certificate +
  connectedness; not importable here).
* (H2) `classified`: for every piece p, H ∈ piece p and K with `{I, H/√6, K/√6}` MUB — and, if
  `ordering p` (balls 1035, 1217, 1622, 2705), with Γ_F(H) ≤ Γ_F(K), Γ_F(H) ≤ Γ_F(HᴴK/√6) — the
  triple has an order-3 symmetry (= the 3.3 GB interval certificates + Fourier-chart crossings).
* (H3) `taoNoThird`: Tao's matrix admits no third basis (Brierley–Weigert 2009).

## Proved pieces of the recognition (all sorry-free)
normal form from the symmetry incl. eigenvalue multiplicities 2/2/2 (`normalForm_of_symmetric`),
flatness ⇔ (Σ|d|²=6, autocorrelation 0) (`flat_iff`), nonvanishing amplitudes (`flat_ne_zero`),
independent case, dependent case (|pₜ|²=2, equilateral triples), constant w ⇒ family
(`family_of_w_const`), non-constant w ⇒ isolated, including the ζ=ω² sign via the explicit
common unitary (F₂⊗F₃)ᴴ/√6 + exchange of the first two bases (`plus_to_isolated`).

## Not formalized (remaining)
1. The (θ₁,θ₂) seed parametrization of D,R,S (SM §"Seeds", cubic t³+σt²−σ̄t−1, domain inequality)
   and its identification with `IsFamilyMember`; two-parameter dimension count; non-equivalence of the
   isolated triple to family members (~500–1000 lines).
2. Theorem all-mubs items 1–2 (pairs via H₊(θ)); linking the 72/96-variable phase equations F and
   the affine action to `HasOrder3Symmetry` (left inside (H2)).
3. (H1)–(H3) themselves (computational / literature).

Done since the previous status: the Γ_F literal formula (`MUBTriples/ScoreFormula.lean`).

## Remarks on the paper
No error found. Simplifications: nonvanishing of αₜ, βₜ follows directly (a zero entry forces a
second zero, then |third|² = 6 > 4) without the bound q ≤ 6√3−9; transporting the *symmetry* (which is
conjugation/equivalence invariant) instead of the recognized types makes "conjugation preserves both
types" unnecessary in Lemma minimum-transition; the 2/2/2 eigenvalue multiplicity is derivable from
unbiasedness and need not be part of the symmetry's definition.
