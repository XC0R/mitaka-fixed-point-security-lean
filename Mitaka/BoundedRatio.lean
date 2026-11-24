/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import ToMathlib.Probability.Divergence.Renyi
public import Mathlib.Probability.Moments.Tilted
public import Mathlib.Probability.Moments.SubGaussian

/-! # Second-order Rényi bound for a bounded likelihood ratio

If `P = μ.tilted f` (density `exp f / E_μ[exp f]`) and `f` takes values in an interval of length
`ℓ`, then for every `v > 1`, `log R_v(P ‖ μ) ≤ vℓ²/8`.

Proof: with `Z(t) = E_μ[exp(t f)]` and `E = E_P[f]`,
`(v - 1) log R_v(P ‖ μ) = log Z(v) - v log Z(1)`. Hoeffding's lemma
(`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`) under `P` at `s = v - 1` gives
`log Z(v) ≤ log Z(1) + (v - 1)E + (v - 1)²ℓ²/8`, and at `s = -1` gives `E ≤ log Z(1) + ℓ²/8`;
together `log Z(v) - v log Z(1) ≤ v(v - 1)ℓ²/8`.

[ZKLY26] (ePrint 2026/2521), Lemma 4 (p. 7, l. 237; proof p. 19, l. 610-612) applies it with
`P(z) = Q_e(z) a_z / E_{Q_e}[a_z]` and `a_z ∈ [κ⁻¹, κ²]`, i.e. `ℓ = 3 log κ`:
`log R_v(P ‖ Q_e) ≤ (9v/8)(log κ)²` (`renyiDiv_withDensity_le`). A first-order bound
(`renyiDiv_le_of_le_smul`) gives `3 log κ` instead. -/

@[expose] public section

open Real MeasureTheory InformationTheory
open scoped ENNReal

namespace Mitaka.BoundedRatio

variable {α : Type*} [MeasurableSpace α]

/-- **Second-order bounded-ratio bound.** If `f ∈ [m, m + ℓ]` `μ`-a.e., then for `v > 1`,
`R_v(μ.tilted f ‖ μ) ≤ exp(vℓ²/8)`. -/
theorem renyiDiv_tilted_le (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf : AEMeasurable f μ) {m ℓ : ℝ} (hfm : ∀ᵐ x ∂μ, f x ∈ Set.Icc m (m + ℓ)) {v : ℝ}
    (hv : 1 < v) :
    renyiDiv v (μ.tilted f) μ ≤ ENNReal.ofReal (Real.exp (v * ℓ ^ 2 / 8)) := by
  have hv1 : 0 < v - 1 := by linarith
  have hv1' : v - 1 ≠ 0 := hv1.ne'
  have hint : ∀ t : ℝ, Integrable (fun x => Real.exp (t * f x)) μ :=
    fun t => ProbabilityTheory.integrable_exp_mul_of_mem_Icc hf hfm
  have hint1 : Integrable (fun x => Real.exp (f x)) μ := by simpa using hint 1
  have hZ1pos : 0 < ∫ x, Real.exp (f x) ∂μ := integral_exp_pos hint1
  have hZ1 : ∫ x, Real.exp (f x) ∂μ = Real.exp (Real.log (∫ x, Real.exp (f x) ∂μ)) :=
    (Real.exp_log hZ1pos).symm
  set L := Real.log (∫ x, Real.exp (f x) ∂μ) with hL
  have : IsProbabilityMeasure (μ.tilted f) := isProbabilityMeasure_tilted hint1
  have hfν : AEMeasurable f (μ.tilted f) := hf.mono_ac (tilted_absolutelyContinuous μ f)
  have hν : ∀ᵐ x ∂(μ.tilted f), f x ∈ Set.Icc m (m + ℓ) :=
    (tilted_absolutelyContinuous μ f).ae_le hfm
  set E := ∫ x, f x ∂(μ.tilted f) with hE
  have H := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc hfν hν
  have hc : (((‖m + ℓ - m‖₊ / 2) ^ 2 : NNReal) : ℝ) = ℓ ^ 2 / 4 := by
    rw [add_sub_cancel_left]
    simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnNorm, Real.norm_eq_abs, div_pow, sq_abs,
      NNReal.coe_ofNat]
    norm_num
  have hmgf : ∀ s : ℝ, ProbabilityTheory.mgf (fun x => f x - E) (μ.tilted f) s =
      (∫ x, Real.exp ((s + 1) * f x) ∂μ) * (Real.exp (-(s * E)) / Real.exp L) := by
    intro s
    rw [ProbabilityTheory.mgf, integral_tilted, ← integral_mul_const, ← hZ1]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [smul_eq_mul]
    rw [div_mul_eq_mul_div, mul_div_assoc', ← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  have h1 := H.mgf_le (v - 1)
  rw [hmgf, sub_add_cancel, hc, ← Real.exp_sub] at h1
  have h1' := (le_div_iff₀ (Real.exp_pos _)).2 h1
  rw [← Real.exp_sub] at h1'
  have h2 := H.mgf_le (-1)
  have hZ0 : ∫ x, Real.exp ((-1 + 1) * f x) ∂μ = 1 := by simp
  rw [hmgf, hZ0, one_mul, hc, ← Real.exp_sub, Real.exp_le_exp] at h2
  have hQ : (∫ x, Real.exp (v * f x) ∂μ) / Real.exp (v * L) ≤
      Real.exp (v * (v - 1) * ℓ ^ 2 / 8) := by
    rw [div_le_iff₀ (Real.exp_pos _), ← Real.exp_add]
    refine h1'.trans (Real.exp_le_exp.2 ?_)
    nlinarith [mul_le_mul_of_nonneg_left h2 hv1.le]
  have hMGF : renyiMGF v (μ.tilted f) μ =
      ENNReal.ofReal ((∫ x, Real.exp (v * f x) ∂μ) / Real.exp (v * L)) := by
    rw [renyiMGF_of_ac (tilted_absolutelyContinuous μ f),
      lintegral_congr_ae ((rnDeriv_tilted_left_self hf).mono fun x hx => by rw [hx]), hZ1,
      ← integral_div, ofReal_integral_eq_lintegral_ofReal ((hint v).div_const _)
        (ae_of_all _ fun x => div_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith), ← Real.exp_sub,
      ← Real.exp_sub, ← Real.exp_mul]
    congr 2
    ring
  rw [renyiDiv_eq_rpow hv, hMGF]
  calc ENNReal.ofReal ((∫ x, Real.exp (v * f x) ∂μ) / Real.exp (v * L)) ^ (v - 1)⁻¹
      ≤ ENNReal.ofReal (Real.exp (v * (v - 1) * ℓ ^ 2 / 8)) ^ (v - 1)⁻¹ :=
        ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hQ) (inv_nonneg.2 hv1.le)
    _ = _ := by
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (inv_nonneg.2 hv1.le),
          ← Real.exp_mul]
        congr 2
        field_simp

/-- **The step of [ZKLY26, Lemma 4].** If `w ∈ [κ⁻¹, κ²]` `μ`-a.e. with `κ ≥ 1`, then for
`v > 1` the law with density `w / E_μ[w]` has `R_v ≤ exp((9v/8)(log κ)²)`. -/
theorem renyiDiv_withDensity_le (μ : Measure α) [IsProbabilityMeasure μ] {w : α → ℝ}
    (hw : AEMeasurable w μ) {κ : ℝ} (hκ : 1 ≤ κ) (hwκ : ∀ᵐ x ∂μ, w x ∈ Set.Icc κ⁻¹ (κ ^ 2))
    {v : ℝ} (hv : 1 < v) :
    renyiDiv v (μ.withDensity fun x => ENNReal.ofReal (w x / ∫ y, w y ∂μ)) μ ≤
      ENNReal.ofReal (Real.exp (9 * v / 8 * Real.log κ ^ 2)) := by
  have hκ0 : 0 < κ := by linarith
  have hpos : ∀ᵐ x ∂μ, 0 < w x :=
    hwκ.mono fun x hx => lt_of_lt_of_le (inv_pos.2 hκ0) hx.1
  have heq : μ.withDensity (fun x => ENNReal.ofReal (w x / ∫ y, w y ∂μ)) =
      μ.tilted fun x => Real.log (w x) := by
    have hi : ∫ y, Real.exp (Real.log (w y)) ∂μ = ∫ y, w y ∂μ :=
      integral_congr_ae (hpos.mono fun x hx => Real.exp_log hx)
    rw [Measure.tilted, hi]
    exact withDensity_congr_ae (hpos.mono fun x hx => by simp only [Real.exp_log hx])
  rw [heq]
  have hlog : ∀ᵐ x ∂μ, Real.log (w x) ∈ Set.Icc (-Real.log κ) (-Real.log κ + 3 * Real.log κ) := by
    filter_upwards [hwκ, hpos] with x hx hx0
    constructor
    · rw [← Real.log_inv]
      exact Real.log_le_log (inv_pos.2 hκ0) hx.1
    · have h := Real.log_le_log hx0 hx.2
      rw [Real.log_pow] at h
      push_cast at h
      linarith
  refine (renyiDiv_tilted_le μ hw.log hlog hv).trans
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (le_of_eq ?_)))
  ring

end Mitaka.BoundedRatio
