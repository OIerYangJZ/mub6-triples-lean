import Mathlib

/-!
# The symmetry contraction criterion (SM Eq. `tc-symmetry`)

Abstract version over real normed spaces (in the paper: `V = ℝ⁷²`, the joint phases
`x = (Q, V)` of `H, K`, and `W = ℝ⁹⁶`, the triple equations `F`).

* `P` is the linear part of the proposed affine symmetry action `x ↦ b + P (x - b)`
  with `P³ = 1`, `Y` the induced action on equations, with covariance
  `F (b + P (z - b)) = Y (F z)`; `Wg` is the gauge projector (`Wg P = P Wg`).
* `G = (1 + P + P²)/3`, `E = (1 - G) Wg`, `Q_Y = 1 - (1 + Y + Y²)/3`, `A = E A₀ Q_Y`.

`covariance`: for `x` in the gauge slice (`Wg (x - b) = x - b`), the average
`x̄ = b + G (x - b)` and `e = x - x̄` satisfy `E e = e` and `A (F x̄) = 0`.

`contraction`: if moreover `F x = 0` and
`‖E - A (∫₀¹ DF(x̄ + s e) ds) E‖ ≤ q < 1`, then `e = 0`, i.e. `x` is a fixed point
of the affine symmetry action ("exact physical symmetry").

The general analytic core is `eq_zero_of_contraction`: if `E e = e`, `A (F x̄) = 0`,
`F (x̄ + e) = 0` and `‖E - A M E‖ ≤ q < 1` with `M = ∫₀¹ DF(x̄ + s e) ds`, then `e = 0`.
-/

open scoped Topology
open ContinuousLinearMap

namespace MUBTriples.Contraction

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

/-- Mean value identity along a segment for a `C¹` map:
`F (x + e) - F x = (∫₀¹ DF(x + s e) ds) e`. -/
theorem sub_eq_integral_fderiv_apply {F : V → W} (hF : ContDiff ℝ 1 F) (x e : V) :
    F (x + e) - F x = (∫ s in (0 : ℝ)..1, fderiv ℝ F (x + s • e)) e := by
  have hcont : Continuous fun s : ℝ => fderiv ℝ F (x + s • e) :=
    (hF.continuous_fderiv one_ne_zero).comp (continuous_const.add (continuous_id.smul continuous_const))
  rw [ContinuousLinearMap.intervalIntegral_apply (hcont.intervalIntegrable 0 1)]
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => F (x + s • e)) (fderiv ℝ F (x + s • e) e) s := by
    intro s _
    have h1 : HasDerivAt (fun s : ℝ => x + s • e) e s := by
      simpa using ((hasDerivAt_id s).smul_const e).const_add x
    exact ((hF.differentiable one_ne_zero) (x + s • e)).hasFDerivAt.comp_hasDerivAt s h1
  have hint : IntervalIntegrable (fun s : ℝ => fderiv ℝ F (x + s • e) e)
      MeasureTheory.volume 0 1 :=
    ((ContinuousLinearMap.apply ℝ W e).continuous.comp hcont).intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

/-- **Contraction core of Eq. `tc-symmetry`.** -/
theorem eq_zero_of_contraction {F : V → W} (hF : ContDiff ℝ 1 F)
    (A : W →L[ℝ] V) (E : V →L[ℝ] V) (xbar e : V) {q : ℝ}
    (hEe : E e = e) (hAF : A (F xbar) = 0) (hzero : F (xbar + e) = 0)
    (hq : ‖E - A ∘L (∫ s in (0 : ℝ)..1, fderiv ℝ F (xbar + s • e)) ∘L E‖ ≤ q) (hq1 : q < 1) :
    e = 0 := by
  set M := ∫ s in (0 : ℝ)..1, fderiv ℝ F (xbar + s • e)
  have hMe : M e = F (xbar + e) - F xbar := (sub_eq_integral_fderiv_apply hF xbar e).symm
  have hAMe : A (M e) = 0 := by rw [hMe, map_sub, hzero, map_zero, hAF, sub_zero]
  have hfix : (E - A ∘L M ∘L E) e = e := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, hEe, hAMe, sub_zero]
  have hle : ‖e‖ ≤ q * ‖e‖ := by
    calc ‖e‖ = ‖(E - A ∘L M ∘L E) e‖ := by rw [hfix]
      _ ≤ ‖E - A ∘L M ∘L E‖ * ‖e‖ := le_opNorm _ _
      _ ≤ q * ‖e‖ := by gcongr
  have : ‖e‖ = 0 := by
    have h0 := norm_nonneg e
    nlinarith
  exact norm_eq_zero.mp this

variable (P : V →L[ℝ] V) (Y : W →L[ℝ] W)

/-- The averaging projector `G = (1 + P + P²)/3`. -/
noncomputable def avg : V →L[ℝ] V := (3⁻¹ : ℝ) • (1 + P + P * P)

lemma mul_avg (hP : P * P * P = 1) : P * avg P = avg P := by
  simp only [avg, mul_smul_comm, mul_add, mul_one]
  congr 1
  rw [← mul_assoc, hP]; abel

lemma avg_mul_avg (hP : P * P * P = 1) : avg P * avg P = avg P := by
  have h4 : P * (P * (P * P)) = P := by rw [← mul_assoc, ← mul_assoc, hP, one_mul]
  have h3 : P * (P * P) = 1 := by rw [← mul_assoc, hP]
  simp only [avg, smul_mul_smul_comm, mul_add, add_mul, one_mul, mul_one, mul_assoc, h3, h4]
  ext v
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.mul_apply, smul_add]
  module

lemma comm_avg {Wg : V →L[ℝ] V} (hW : Wg * P = P * Wg) : Wg * avg P = avg P * Wg := by
  have h2 : Wg * (P * P) = P * P * Wg := by
    rw [← mul_assoc, hW, mul_assoc, hW, ← mul_assoc]
  simp only [avg, mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one, one_mul, hW, h2]

/-- **Covariance part of Eq. `tc-symmetry`.**  With `x̄ = b + G (x - b)`, `e = x - x̄`,
`E = (1 - G) Wg` and `A = E A₀ Q_Y`, one has `E e = e` and `A (F x̄) = 0`. -/
theorem covariance {F : V → W} (b x : V) (Wg : V →L[ℝ] V) (A₀ : W →L[ℝ] V)
    (hP : P * P * P = 1)
    (hcov : ∀ z, F (b + P (z - b)) = Y (F z))
    (hW : Wg * P = P * Wg) (hx : Wg (x - b) = x - b) :
    let G := avg P
    let xbar := b + G (x - b)
    let E := (1 - G) * Wg
    let QY := 1 - avg Y
    let A := E ∘L A₀ ∘L QY
    E (x - xbar) = x - xbar ∧ A (F xbar) = 0 := by
  intro G xbar E QY A
  have hPG := mul_avg P hP
  have hGG := avg_mul_avg P hP
  have he : x - xbar = (1 - G) (x - b) := by
    simp only [xbar, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]; abel
  constructor
  · rw [he]
    have hWG : Wg * G = G * Wg := comm_avg P hW
    have h1 : Wg ((1 - G) (x - b)) = (1 - G) (x - b) := by
      have : Wg * (1 - G) = (1 - G) * Wg := by rw [mul_sub, sub_mul, mul_one, one_mul, hWG]
      rw [← ContinuousLinearMap.mul_apply, this, ContinuousLinearMap.mul_apply, hx]
    have h2 : (1 - G) * (1 - G) = 1 - G := by
      rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, hGG]; abel
    simp only [E, ContinuousLinearMap.mul_apply, h1]
    rw [← ContinuousLinearMap.mul_apply, h2]
  · -- `x̄` is a fixed point of the affine action, hence `F x̄` is `Y`-invariant
    have hfix : b + P (xbar - b) = xbar := by
      simp only [xbar, add_sub_cancel_left]
      rw [← ContinuousLinearMap.mul_apply, hPG]
    have hYF : Y (F xbar) = F xbar := by rw [← hcov, hfix]
    have hYY : (Y * Y) (F xbar) = F xbar := by
      rw [ContinuousLinearMap.mul_apply, hYF, hYF]
    have hQ : QY (F xbar) = 0 := by
      simp only [QY, avg, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, hYF, hYY]
      module
    simp only [A, ContinuousLinearMap.comp_apply, hQ, map_zero]

/-- **Symmetry criterion (SM Eq. `tc-symmetry`).**  Under the covariance hypotheses, a zero
`x` of `F` in the gauge slice with
`‖E - A (∫₀¹ DF(x̄ + s(x - x̄)) ds) E‖ ≤ q < 1` is a fixed point of the affine symmetry
action: `b + P (x - b) = x`. -/
theorem symmetry_criterion {F : V → W} (hF : ContDiff ℝ 1 F) (b x : V) (Wg : V →L[ℝ] V)
    (A₀ : W →L[ℝ] V) (hP : P * P * P = 1)
    (hcov : ∀ z, F (b + P (z - b)) = Y (F z))
    (hW : Wg * P = P * Wg) (hx : Wg (x - b) = x - b) (hzero : F x = 0) {q : ℝ}
    (hq : ‖(1 - avg P) * Wg - (((1 - avg P) * Wg) ∘L A₀ ∘L (1 - avg Y)) ∘L
        (∫ s in (0 : ℝ)..1, fderiv ℝ F ((b + avg P (x - b)) + s • (x - (b + avg P (x - b)))))
          ∘L ((1 - avg P) * Wg)‖ ≤ q)
    (hq1 : q < 1) :
    b + P (x - b) = x := by
  obtain ⟨hEe, hAF⟩ := covariance P Y b x Wg A₀ hP hcov hW hx
  have he := eq_zero_of_contraction hF _ _ _ _ hEe hAF (by rwa [add_sub_cancel]) hq hq1
  have hxx : x = b + avg P (x - b) := (sub_eq_zero.mp he)
  conv_rhs => rw [hxx]
  conv_lhs => rw [hxx]
  simp only [add_sub_cancel_left]
  rw [← ContinuousLinearMap.mul_apply, mul_avg P hP]

end MUBTriples.Contraction
