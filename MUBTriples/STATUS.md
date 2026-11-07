# MUBTriples — status (2026-11-07)

Lean 4 formalization of the classification of MUB triples in C^6, arXiv:2611.06917v1
(Cárdenes Wuttig & Tindall), Theorem `all-mubs` item 3 (+ the "no four MUBs" corollary).
Standalone Lake package `mub6_triples`, depending on Mathlib and on `hadamard6_formal`
(commit 57b0302) for `Hadamard6.Mat6` (indexed by `Fin 3 ⊕ Fin 3`), `IsHadamard`, `Equivalent`,
`IsTaoOrbit`.

Build: `lake build` (18 modules, ≈5,700 lines, about a minute on top of a built Mathlib).
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
| `Seeds.seedTriple_spec`, `seedTriple_isFamilyMember` | SM §"Seeds": for (θ₁,θ₂,ℓ) in the domain `|σ|⁴+18|σ|²+8Re(σ³)−27 ≤ 0`, every ordering ρ of the roots of `t³+σt²−σ̄t−1` and all signs ε: roots unimodular, λₖμₖ ≠ 0, D,R,S unit, the triple is MUB and `IsFamilyMember`, `√6U₂†U₃ = H = [[A,B],[B†,−A†]]`, H Hadamard | none |
| `Seeds.construct_spec` | abstract form: any unit circulant first rows a, b with `Σa_{s+1}āₛ + Σb_{s+1}b̄ₛ = 0` | none |
| `Seeds.exists_isRootTriple`, `domainPoly_eq_disc`, `IsRootTriple.normSq_of_domain`, `domainPoly_nonpos_iff` | the cubic has three roots; the domain polynomial is its discriminant; domain ⇔ all roots unimodular (proved, not assumed) | none |
| `Seeds.seedσ_center`, `exists_familyMember` | non-vacuity: (2π/3, −2π/3, 1) gives σ = 0 in the domain; family members exist | none |
| `Seeds.inDomain_iff` | "the allowed parameter pairs are exactly the domain": domain ⇔ ∃ circulant B (first entry 1) with `[[A,B],[B†,−A†]]` Hadamard ⇔ unit roots | none |
| `Seeds.seedOf_seedTriple_corner`, `seedOf_corner142`, `Inequivalence.seedOf_isolatedTriple` | the specified seeds: (θ₁,θ₂,θ₁−θ₂,θ₁) of the upper-left corner of `√6U₂†U₃`; (θ'₁,θ'₂,−2π/3,2π/3) of rows (1,4,2), cols (1,2,3) of `√6U₃†`; the isolated triple's (2π/3,−2π/3,−2π/3,2π/3) and (0,0,−2π/3,2π/3) | none |
| `Seeds.familyMember_tripleEquiv_seedTriple`, `exists_familyMember_iff_seed` | converse: every `IsFamilyMember` triple is equivalent (column phases only) to a seed triple with ℓ = 1; "equivalent to a family member" ⇔ "equivalent to a seed triple in the domain" | none |
| `Inequivalence.not_tripleEquiv_isolatedTriple_of_familyMember`, `family_and_isolated_exclusive` | the isolated triple is not equivalent to any family member; the two alternatives of the classification are exclusive | none |
| `Inequivalence.bargmann4_of_tripleEquiv`, `familyTriple_conj_frame`, `bargmann4_isolatedTriple` | the invariant `Σ_{e,f,g}(⟨e|f⟩⟨f|g⟩⟨g|e⟩)⁴` is preserved or conjugated by equivalence; every family triple is equivalent to its conjugate with the bases fixed (so the invariant is real); for the isolated triple it is `−2592(1+2ω)/6⁸ ∉ ℝ` | none |
| `Inequivalence.mubTriple_seedClassification`, `tripleClassification_iff_seedClassification`, `symmetric_seedClassification` | classification in seed form with exclusive or (`SeedClassification`): under `C`; equivalence with `TripleClassification`; hypothesis-free for symmetric triples | `C` (first only) |

## Definitions (exact statement)

* `IsUnitary`, `Unbiased` (|(Uᴴ V)ᵢⱼ|² = 1/6), `FourMUBs` — verbatim from `NoFourMUBs.Basic` (MIT);
  `IsMUBTriple`.
* `TripleEquiv U V`: `V k = W * U (π k) * M k`, W unitary, π ∈ S₃, `M k` monomial (column permutation +
  unit phases). **Complex conjugation is NOT included** (the paper's equivalence).
* `HasOrder3Symmetry`: ∃ unitary T, T³ = 1, T fixes the vectors of an anchor basis up to phase
  (`T * U m = U m * diag d`) and acts on each other basis as a phased double three-cycle.
* Family (`IsFamilyMember`): MUB triples `{I, U₂, U₃}` of the explicit form of Methods
  Eq. `methods-explicit-continuous-bases` with **arbitrary** unit diagonals D, R, S; up to equivalence
  this is exactly the image of the seed construction (`exists_familyMember_iff_seed`).
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

## Seed parametrization and inequivalence (`Seeds.lean`, `Inequivalence.lean`; sorry-free, no new hypotheses)
* Definitions follow SM §"Seeds" literally: `seedβ`, `seedγ`, `seedσ`, `domainPoly`, `InDomain`,
  `IsRootTriple σ ρ` (`(t−ρ₁)(t−ρ₂)(t−ρ₃) = t³+σt²−σ̄t−1` for all t), `circM`, `seedA`, `seedB`,
  `seedH`, `fcoef` (λₖ = (F̂₃AF̂₃†)ₖₖ/√6), `seedD/R/S` (signs `ε : I3 → ℤˣ`), `seedTriple`; ℓ ranges over ℤ
  (the paper's ℓ = 1,2,3 are the three cube roots).
* The cubic-root step is fully proved: existence from algebraic closure of ℂ; unit modulus under the
  domain inequality via the self-inversive symmetry ρ ↦ 1/ρ̄ (a non-unit root r forces the roots
  r, 1/r̄, r̄/r, whose discriminant `((N−1)(2Re r³−N²−N)/N²)²`, N = |r|², is positive). No hypothesis
  is introduced.
* Inequivalence uses the invariant `bargmann4 U = Σ_{e,f,g} (⟨e|f⟩⟨f|g⟩⟨g|e⟩)⁴` (216 three-vertex
  products), not the paper's Jacobian-rank argument (rank 55 + inverse function theorem), which is
  not formalized.

## Not formalized (remaining)
1. The two-parameter dimension count of the family (that the family is genuinely two-dimensional up to
   equivalence), and the paper's "isolated class" statement in the topological sense (Jacobian rank 55);
   only the non-equivalence of the isolated triple to every family member is proved.
2. Theorem all-mubs items 1–2 (pairs via H₊(θ)); linking the 72/96-variable phase equations F and
   the affine action to `HasOrder3Symmetry` (left inside (H2)).
3. (H1)–(H3) themselves (computational / literature).

Done since the previous status: the (θ₁,θ₂) seed parametrization and its identification with
`IsFamilyMember` in both directions (`MUBTriples/Seeds.lean`); the non-equivalence of the isolated
triple to family members and the seed form of the classification (`MUBTriples/Inequivalence.lean`).
Earlier: the Γ_F literal formula (`MUBTriples/ScoreFormula.lean`).

## Remarks on the paper
No error found.  The SM §"Seeds" claims are all confirmed in Lean as stated (domain = discriminant
≤ 0 = unimodular roots, nonvanishing denominators, unit D,R,S, √6U₂†U₃ = H, both specified seeds of
family and isolated triple).  Observation: the isolated triple's first seed (2π/3,−2π/3,−2π/3,2π/3) equals
the family seed at (θ₁,θ₂) = (2π/3,−2π/3), σ = 0, inside the domain; there all three family transitions
have Haagerup invariants in the sixth roots of unity (numerically), so the separation genuinely needs a
three-basis invariant (the paper's remark "coincident seed coordinates need not represent equivalent
triples"). Simplifications: nonvanishing of αₜ, βₜ follows directly (a zero entry forces a
second zero, then |third|² = 6 > 4) without the bound q ≤ 6√3−9; transporting the *symmetry* (which is
conjugation/equivalence invariant) instead of the recognized types makes "conjugation preserves both
types" unnecessary in Lemma minimum-transition; the 2/2/2 eigenvalue multiplicity is derivable from
unbiasedness and need not be part of the symmetry's definition.
