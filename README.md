# MUB triples in ℂ⁶: a Lean 4 formalization

[![Lean build](https://github.com/OIerYangJZ/mub6-triples-lean/actions/workflows/build.yml/badge.svg)](https://github.com/OIerYangJZ/mub6-triples-lean/actions/workflows/build.yml)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23993900.svg)](https://doi.org/10.5281/zenodo.23993900)

> **Attribution.** The theorem and its proof are due to **Mateo Cárdenes Wuttig and Joseph
> Tindall**, *Using topology to reveal all mutually unbiased bases in dimension six*,
> [arXiv:2611.06917](https://arxiv.org/abs/2611.06917), with proofs, certificates and code at
> [github.com/JoeyT1994/NoFourMUBS](https://github.com/JoeyT1994/NoFourMUBS). This repository
> formalizes their proof of the classification of MUB triples (their Theorem `all-mubs`, item 3)
> in Lean 4; it contains no new mathematics beyond the small simplifications noted below.
> It builds on their Lean classification of order-six complex Hadamard matrices,
> [all_hadamard_matrices_in_dimension_six](https://github.com/mateocardeneswuttig/all_hadamard_matrices_in_dimension_six)
> (arXiv:2608.18053). Please cite their papers when using this work.

**Formalization author:** Jinze Yang (School of Physics, Xidian University).
**AI-use statement:** This formalization was completed jointly by the author and Claude Opus 5.5 (Anthropic).
**Archived version:** [doi:10.5281/zenodo.23993901](https://doi.org/10.5281/zenodo.23993901) (v0.1.0); all versions: [doi:10.5281/zenodo.23993900](https://doi.org/10.5281/zenodo.23993900).

## Main statement

```lean
theorem MUBTriples.mubTriple_classification {ι : Type} {piece : ι → Set Mat6}
    {ordering : ι → Prop} (C : TripleCertificate piece ordering) : TripleClassification

def MUBTriples.TripleClassification : Prop :=
  ∀ U : Triple, IsMUBTriple U →
    (∃ V, IsFamilyMember V ∧ TripleEquiv U V) ∨ TripleEquiv U isolatedTriple
```

(`MUBTriples/MainTheorem.lean`, `MUBTriples/Statement.lean`.) In words: **assuming the three
certificate facts (H1)–(H3) below, every triple of mutually unbiased bases of ℂ⁶ is equivalent
to a member of the continuous family or to the isolated Fourier triple.** This is item 3 of
Theorem `all-mubs` of arXiv:2611.06917, which proves the conjecture of Matolcsi, Matszangosz,
Varga and Weiner that the known triples are the only ones.

The objects in the statement:

* A basis is the set of columns of a unitary `U : Mat6` (`Mat6 = Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℂ`,
  from `hadamard6_formal`). `Unbiased U V` means `|(Uᴴ V)ᵢⱼ|² = 1/6` for all `i, j`.
  `IsMUBTriple U` for `U : Fin 3 → Mat6` means all three are unitary and pairwise unbiased.
* `TripleEquiv U V`: `V k = W * U (π k) * M k` with one common unitary `W`, a permutation `π` of
  the three bases and, for every basis, a monomial matrix `M k` (column permutation and unit
  column phases). Complex conjugation is *not* part of the equivalence, as in the paper.
* `IsFamilyMember`: a MUB triple `{I₆, U₂, U₃}` of the explicit block form of Methods
  Eq. `methods-explicit-continuous-bases`,
  `U₂ = (1/√2)[[F̂₃, D F̂₃], [F̂₃, −D F̂₃]]`, `U₃ = (1/√2)[[R F̂₃, −D S† F̂₃], [S F̂₃, D R† F̂₃]]`,
  with arbitrary unit diagonal matrices `D, R, S`.
* `isolatedTriple`: `{I₆, F̂₂ ⊗ F̂₃, [diag(1, i) F̂₂] ⊗ [diag(1, ω², ω²) F̂₃]}` (Methods
  Eq. `methods-isolated-triple-bases`).

Corollary (`MUBTriples.no_four_mubs`): under (H1)–(H3) and the theorem of Jaming, Matolcsi, Móra,
Szöllősi and Weiner (J. Phys. A 42, 245305, 2009) that no pair `{I₆, H/√6}` with `H` in the
transposed Fourier family extends to four MUBs (hypothesis `NoQuartetThroughFourierFamily`),
there are no four MUBs in ℂ⁶ (`¬ FourMUBs`).

Equation and section names such as Eq. `gamma-score` or Prop. `tc-certificate` are the LaTeX labels
of the arXiv v1 source; "SM" is its Supplementary Information.

## The hypotheses (H1)–(H3)

`TripleCertificate piece ordering` (`MUBTriples/Assembly.lean`) is a structure of three
propositions. The cover is an arbitrary family `piece : ι → Set Mat6`; `ordering : ι → Prop`
marks the pieces whose certificate only covers the "minimum-transition" labelling.
None of these facts is proved in Lean here; in the paper they are established as follows.

| | Lean field | Informal meaning | Where the paper establishes it |
|---|---|---|---|
| (H1) | `covered` | Every complex Hadamard matrix of order 6 that is not in Tao's orbit becomes, after one of `id`, conjugation, transpose, conjugate transpose, equivalent to a matrix of some piece of the cover. In the paper the pieces are the images of the 2,775 seed balls and of the chart at F₆. | Computer-assisted: Theorem `connected` (main text §"Connectedness of non-Tao Hadamard matrices"; proof in SM §"Proofs of the reconstruction and connectedness theorems") together with SM Prop. `finite` (§"The phase-ball cover and the exclusion of quartets", including §"Boundary transfers and closed subdivisions"): the union of the certified balls is open and closed, hence everything. Same shape as `NoFourMUBs.Inputs.covered` in the NoFourMUBS Lean development, which derives it there from the seed-atlas certificate. |
| (H2) | `classified` | On every piece `p`: if `H ∈ piece p` and `{I₆, H/√6, K/√6}` is a MUB triple, and (only when `ordering p`) `H` has the least score `Γ_F` among the three transitions `H`, `K`, `Hᴴ K/√6` (ties included), then the triple has an order-three symmetry (`HasOrder3Symmetry`). Pieces with no such `K` ("excluded patterns") satisfy it vacuously. | Computer-assisted: SM §"Proof of the classification of all MUB sets" (patterns and triple equations, column tubes, basis exclusions and the symmetry criterion, normal-form localisation, the two crossings in the Fourier chart, §"Arithmetic and the global conclusion" and Prop. `tc-certificate`). The per-ball interval certificates (3.3 GB, release `tc-verification-2026-11-04` of NoFourMUBS) close all 2,775 balls, four of them (IDs 1035, 1217, 1622, 2705) with minimum-transition scope, plus a separate Fourier-chart calculation. |
| (H3) | `taoNoThird` | If `H` is in Tao's orbit, `{I₆, H/√6}` has no third unbiased basis. | Literature: S. Brierley and S. Weigert, *Constructing mutually unbiased bases in dimension six*, Phys. Rev. A 79, 052316 (2009); also re-checked in NoFourMUBS (`proof/theorems/TC_triple_classification/tao.py`). |

The score `Γ_F` in (H2) is the Lean `ΓF` (`MUBTriples/Score.lean`). It is **proved equal to the
paper's Eq. `gamma-score`**, defined literally as `ΓFpaper` in `MUBTriples/ScoreFormula.lean`
(`(1/15) min_{a,b} ‖dist_{2π}(RQ − (π/3) v(a,b))‖₂` over plaquettes `i < k`, `j < l`, permutations
`a, b` of `0, …, 5` with `a₁ = b₁ = 0`, and `dist_{2π}` the distance to `2πℤ`):

```lean
theorem ΓF_exp_eq_ΓFpaper (Q : Fin 6 → Fin 6 → ℝ) (e f : I6 ≃ Fin 6) :
    ΓF (expMat Q e f) = ΓFpaper Q                        -- ΓF (e^{iQ}) = paper's Γ_F
theorem minTransition_iff_paper {H K : Mat6} (hT : IsMUBTriple (std H K)) :
    MinTransition H K ↔ ΓFpaper (phaseArray H) ≤ ΓFpaper (phaseArray K) ∧
      ΓFpaper (phaseArray H) ≤ ΓFpaper (phaseArray (s6 • (Hᴴ * K)))
```

so (H2) may equivalently be stated with the literal formula (`classified_of_paper`).

## What is proved without hypotheses

* `symmetricRecognition`: every MUB triple with an order-three symmetry is equivalent to a family
  member or to the isolated triple (SM §"Algebraic recognition of the symmetric triples"),
  including the normal form, the 2/2/2 eigenvalue multiplicities, flatness, the independent and
  dependent cases and the sign case `ζ = ω²`.
* `every_mubTriple_hasOrder3Symmetry` / `tripleClassification_of_certificate`: the logical
  skeleton of SM Prop. `tc-certificate` and Lemma `minimum-transition` (from (H1)–(H3)).
* `Contraction.symmetry_criterion`: SM Eq. `tc-symmetry`, abstractly over real normed spaces.
* Sanity checks: the isolated triple is a MUB triple; a family block form is a MUB triple iff two
  circulants are flat; both types carry the order-three symmetry.
* Invariance of `Γ_F` under equivalence, conjugation, transpose and adjoint, and its equality
  with the paper's formula.

Small differences from the paper's write-up (no error was found): the nonvanishing of the
amplitudes follows directly without the bound `q ≤ 6√3 − 9`; transporting the symmetry (which is
invariant under conjugation and equivalence) instead of the recognized types makes "conjugation
preserves both types" unnecessary in Lemma `minimum-transition`; the 2/2/2 multiplicity is derived
from unbiasedness rather than assumed.

## What is not formalized

1. (H1)–(H3) themselves: the phase-ball cover and connectedness, the 3.3 GB interval
   certificates and the Fourier-chart crossings, and Brierley–Weigert's theorem on Tao's matrix.
   In particular the link between the paper's 72/96-variable phase equations `F` and the affine
   action on one side and `HasOrder3Symmetry` on the other is part of (H2).
2. The two-parameter seed parametrization of `D, R, S` (SM §"Seeds of all mutually unbiased
   triples": cubic `t³ + σt² − σ̄t − 1`, domain inequality) and its identification with
   `IsFamilyMember`; the dimension count of the family; the non-equivalence of the isolated
   triple to family members. Here a family member is *any* MUB triple of the explicit block form.
3. Items 1–2 of Theorem `all-mubs` (single bases and pairs, via `H₊(θ)`).
4. The quartet theorem of Jaming et al. (2009), assumed in `no_four_mubs`.

See [`MUBTriples/STATUS.md`](MUBTriples/STATUS.md) for a module-by-module status.

## Building

Requirements: [elan](https://github.com/leanprover/elan) (it installs the toolchain pinned in
`lean-toolchain`, `leanprover/lean4:v4.33.0-rc2`), git, about 10 GB of disk.

```sh
lake exe cache get     # download prebuilt Mathlib (pinned in lake-manifest.json)
lake build             # builds the 7 needed modules of hadamard6_formal and the 16 MUBTriples modules
lake env lean scripts/PrintAxioms.lean   # axiom audit of the main theorems
```

Expected axiom output for every listed theorem:
`depends on axioms: [propext, Classical.choice, Quot.sound]`. The build emits style-linter
warnings (Mathlib's standard linter set is enabled, as in `hadamard6_formal`); there are no errors,
no `sorry` and no `axiom` declarations.

Dependencies (`lakefile.toml`, `lake-manifest.json`): Mathlib tag `v4.33.0-rc2`
(commit `51e6992efd06126df61a496bebf8f49482a4e129`) and `hadamard6_formal` at commit
`57b03025ecbe259e474281f49e201ea7cb474e34`; only `Hadamard6.TaoOrbit` and its imports are used.

**Local verification record (2026-11-06, macOS arm64, elan 4.2.4).** The repository was built
with exactly the committed `lakefile.toml` and `lake-manifest.json`, without any network access:
`.lake/packages/` was pre-seeded with copy-on-write copies of the already built packages at the
manifest revisions (Mathlib and its dependencies) and with a local `git clone` of
`hadamard6_formal` checked out at `57b0302` with its `origin` set to the GitHub URL. Lake does not
fetch when a package's checkout is already at the manifest revision. All git and HTTP(S) access
was disabled during the build (`GIT_ALLOW_PROTOCOL=file`, `GIT_SSH_COMMAND=false`, proxies set to
a closed local port). `lake build` finished successfully (8,722 jobs; Mathlib up to date, the 7
`Hadamard6` modules and 16 `MUBTriples` modules compiled), and `scripts/PrintAxioms.lean` printed
only `propext, Classical.choice, Quot.sound`.

**Continuous integration.** `.github/workflows/build.yml` builds from a fresh checkout with
[`leanprover/lean-action`](https://github.com/leanprover/lean-action) (Mathlib from the official
cache, no GitHub cache of `.lake`) and runs the axiom audit. It has **not** been run yet (it
cannot be run locally).

## Layout

| Path | Content |
|---|---|
| `MUBTriples/Basic.lean` | bases, unbiasedness, triples, equivalence, standard form `{I₆, H/√6, K/√6}` |
| `MUBTriples/NormalForm.lean`, `Symmetry.lean` | `F₃`, the symmetric normal form, `HasOrder3Symmetry` |
| `MUBTriples/Statement.lean`, `KnownTriples.lean` | the family, the isolated triple, `TripleClassification` |
| `MUBTriples/Score.lean`, `ScoreFormula.lean` | the ordering score `Γ_F`, its invariances, equality with Eq. `gamma-score` |
| `MUBTriples/Assembly.lean` | `TripleCertificate` (H1)–(H3), Lemma `minimum-transition`, assembly |
| `MUBTriples/Contraction.lean` | the symmetry criterion (SM Eq. `tc-symmetry`) |
| `MUBTriples/Recognition/` | algebraic recognition of the symmetric triples |
| `MUBTriples/MainTheorem.lean` | `mubTriple_classification`, `no_four_mubs` |
| `scripts/PrintAxioms.lean` | axiom audit |

## License and citation

MIT, see [`LICENSE`](LICENSE). The definitions `IsUnitary`, `Unbiased` and `FourMUBs` are restated
verbatim from the MIT-licensed NoFourMUBS Lean development (© 2026 Joseph Tindall and Mateo
Cárdenes Wuttig); see the NOTICE section of `LICENSE`. Citation metadata: [`CITATION.cff`](CITATION.cff).
Please also cite:

* M. Cárdenes Wuttig, J. Tindall, *Using topology to reveal all mutually unbiased bases in dimension
  six*, arXiv:2611.06917 (2026).
* M. Cárdenes Wuttig, J. Tindall, *A complete classification of complex Hadamard matrices of order
  six*, arXiv:2608.18053 (2026).
