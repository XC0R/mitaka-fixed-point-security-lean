/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Lemma4
public import FalconPrecision.NumTail

/-! # Lemma 5 of [ZKLY26] with an explicit constant, at Mitaka's online widths

[ZKLY26] (ePrint 2026/2521) writes `D_{ℤ,r,c}` for the Gaussian with weight `exp(-π(x-c)²/r²)`
(p. 3, l. 98-100); VCVio's `discreteGaussianMeasure σ c` has weight `exp(-(x-c)²/(2σ²))`. The two
agree at `σ = r/√(2π)` (`stdDev`).

[ZKLY26, Lemma 5] (p. 8, l. 274-276; [DFLP26, Lemma 4], ePrint 2026/1531, p. 13): for
`r ≥ η_ϵ(ℤ)`, `0 < ϵ ≤ 1/4`, `a > 1` and `|c^fp - c| ≤ Δ`,
`log R_a(D_{ℤ,r,c^fp} ‖ D_{ℤ,r,c}) ≤ (πa(a+1)/(a-1)) (Δ²/r²) (1 + O(ϵ))`.

The results here hold for `r/√(2π) ≥ 1.277`, i.e. `r ≥ 1.277·√(2π) ≈ 3.20`: this is the paper's
lemma restricted to that range of widths (the paper needs only `r ≥ η_ϵ(ℤ)` with `ϵ ≤ 1/4`, which
allows smaller widths). Mitaka's online widths `r = 3.305` and `r = 3.34` ([ZKLY26, Table 2], p. 9;
`σ = 1.3185…`, `σ = 1.3324…`) are in range. On that range the explicit theta tail of
`FalconPrecision.NumTail` replaces the smoothing condition, and `O(ϵ)` becomes `(r/√(2π))² · 2⁻³⁰`:

* `renyiDiv_shift_le`: `R_a ≤ exp(aπδ²/r² + a(a+1)δ²/(2³¹(a-1)))` (`Lemma4.renyiDiv_shift_le`
  with `M ≤ 2⁻³⁰` from `NumTail.falcon_tail`);
* `renyiDiv_le_of_abs_sub_le`: the paper's form with `1 + O(ϵ)` replaced by
  `1 + (r/√(2π))²/2³⁰`;
* `renyiDiv_le_of_abs_sub_le_mitaka512`, `renyiDiv_le_of_abs_sub_le_mitaka1024`: the paper's form
  with `1 + 2⁻²⁹` at `r = 3.305` and `r = 3.34`. -/

@[expose] public section

open Real MeasureTheory InformationTheory LatticeCrypto
open scoped ENNReal

namespace Mitaka.Lemma5

/-- The standard deviation `r/√(2π)` of the Gaussian of width `r` in the convention of
[ZKLY26]. -/
noncomputable def stdDev (r : ℝ) : ℝ := r / √(2 * π)

/-- `2σ² = r²/π` at `σ = r/√(2π)`. -/
theorem two_mul_stdDev_sq (r : ℝ) : 2 * stdDev r ^ 2 = r ^ 2 / π := by
  rw [stdDev, div_pow, Real.sq_sqrt (by positivity)]
  ring

/-- `σ² = r²/(2π)` at `σ = r/√(2π)`. -/
theorem stdDev_sq (r : ℝ) : stdDev r ^ 2 = r ^ 2 / (2 * π) := by
  rw [stdDev, div_pow, Real.sq_sqrt (by positivity)]

/-- A positive standard deviation comes from a positive width. -/
theorem pos_of_pos_stdDev {r : ℝ} (h : 0 < stdDev r) : 0 < r := by
  have hs : 0 < √(2 * π) := Real.sqrt_pos.2 (by positivity)
  have h' := mul_pos h hs
  rwa [stdDev, div_mul_cancel₀ _ hs.ne'] at h'

/-- A positive width has a positive standard deviation. -/
theorem stdDev_pos {r : ℝ} (hr : 0 < r) : 0 < stdDev r :=
  div_pos hr (Real.sqrt_pos.2 (by positivity))

/-- `r ≥ 1.277 · 2.51` gives `r/√(2π) ≥ 1.277`. -/
private theorem le_stdDev_of_le {r : ℝ} (h : 1277 / 1000 * (251 / 100) ≤ r) :
    1277 / 1000 ≤ stdDev r := by
  have hpi := Real.pi_lt_d2
  have hs : √(2 * π) ≤ 251 / 100 := by
    calc √(2 * π) ≤ √((251 / 100) ^ 2) := Real.sqrt_le_sqrt (by linarith)
      _ = 251 / 100 := Real.sqrt_sq (by norm_num)
  rw [stdDev, le_div_iff₀ (Real.sqrt_pos.2 (by positivity))]
  linarith

/-- `r² ≤ 12.56` gives `(r/√(2π))² ≤ 2`. -/
theorem stdDev_sq_le_two {r : ℝ} (h : r ^ 2 ≤ 1256 / 100) : stdDev r ^ 2 ≤ 2 := by
  have hpi := Real.pi_gt_d2
  rw [stdDev_sq, div_le_iff₀ (by positivity)]
  linarith

/-- At `σ = r/√(2π)` the Gaussian weight is `exp(-π(z-c)²/r²)`. -/
theorem discreteGaussianWeight_stdDev (r c : ℝ) (z : ℤ) :
    discreteGaussianWeight (stdDev r) c z = Real.exp (-(π * (z - c) ^ 2 / r ^ 2)) := by
  rw [discreteGaussianWeight, two_mul_stdDev_sq, div_div_eq_mul_div]
  congr 1
  ring

/-- The online width of Mitaka-512, `r = 3.305`, has `r/√(2π) ≥ 1.277`. -/
theorem stdDev_mitaka512 : 1277 / 1000 ≤ stdDev (3305 / 1000) :=
  le_stdDev_of_le (by norm_num)

/-- The online width of Mitaka-1024, `r = 3.34`, has `r/√(2π) ≥ 1.277`. -/
theorem stdDev_mitaka1024 : 1277 / 1000 ≤ stdDev (334 / 100) :=
  le_stdDev_of_le (by norm_num)

/-- **Lemma 5, explicit** (the paper's lemma restricted to `r ≥ 1.277·√(2π) ≈ 3.20`). For
`r/√(2π) ≥ 1.277`, `a > 1` and every shift `δ`:
`R_a(D_{ℤ,r,c+δ} ‖ D_{ℤ,r,c}) ≤ exp(aπδ²/r² + a(a+1)δ²/(2³¹(a-1)))`. -/
theorem renyiDiv_shift_le (r c δ a : ℝ) (hr : 1277 / 1000 ≤ stdDev r) (ha : 1 < a) :
    renyiDiv a (discreteGaussianMeasure (stdDev r) (c + δ))
        (discreteGaussianMeasure (stdDev r) c) ≤
      ENNReal.ofReal
        (Real.exp (a * π * δ ^ 2 / r ^ 2 + a * (a + 1) * δ ^ 2 / (2 ^ 31 * (a - 1)))) := by
  have hσ : 0 < stdDev r := lt_of_lt_of_le (by norm_num) hr
  obtain ⟨hT, hM⟩ := FalconPrecision.NumTail.falcon_tail _ hr
  refine (FalconPrecision.Lemma4.renyiDiv_shift_le _ c δ a hσ ha hT).trans
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
  have hK : 0 ≤ a * (a + 1) * δ ^ 2 / (2 * (a - 1)) :=
    div_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg δ))
      (by linarith)
  have e1 : a * δ ^ 2 / (2 * stdDev r ^ 2) = a * π * δ ^ 2 / r ^ 2 := by
    rw [two_mul_stdDev_sq, div_div_eq_mul_div]
    ring
  have e2 : a * (a + 1) * δ ^ 2 * FalconPrecision.ThetaTail.M (stdDev r) / (2 * (a - 1)) =
      a * (a + 1) * δ ^ 2 / (2 * (a - 1)) * FalconPrecision.ThetaTail.M (stdDev r) := by ring
  have e3 : a * (a + 1) * δ ^ 2 / (2 ^ 31 * (a - 1)) =
      a * (a + 1) * δ ^ 2 / (2 * (a - 1)) * (1 / 2 ^ 30) := by
    rw [div_mul_div_comm, mul_one]
    congr 1
    ring
  rw [e1, e2, e3]
  linarith [mul_le_mul_of_nonneg_left hM hK]

/-- The exponent of `renyiDiv_shift_le` is monotone in `δ²`. -/
theorem explicit_exponent_le_of_sq_le {r a δ Δ : ℝ} (ha : 1 < a) (h : δ ^ 2 ≤ Δ ^ 2) :
    a * π * δ ^ 2 / r ^ 2 + a * (a + 1) * δ ^ 2 / (2 ^ 31 * (a - 1)) ≤
      a * π * Δ ^ 2 / r ^ 2 + a * (a + 1) * Δ ^ 2 / (2 ^ 31 * (a - 1)) := by
  have ha0 : 0 ≤ a := by linarith
  exact add_le_add
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h (mul_nonneg ha0 Real.pi_pos.le))
      (sq_nonneg _))
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h (mul_nonneg ha0 (by linarith)))
      (mul_pos (by norm_num) (by linarith)).le)

/-- The exponent of `renyiDiv_shift_le` is at most the paper's
`(πa(a+1)/(a-1)) (Δ²/r²) (1 + (r/√(2π))²/2³⁰)`. -/
theorem explicit_exponent_le_paper {r a Δ : ℝ} (hr : r ≠ 0) (ha : 1 < a) :
    a * π * Δ ^ 2 / r ^ 2 + a * (a + 1) * Δ ^ 2 / (2 ^ 31 * (a - 1)) ≤
      π * a * (a + 1) / (a - 1) * (Δ ^ 2 / r ^ 2) * (1 + stdDev r ^ 2 / 2 ^ 30) := by
  have ha1 : 0 < a - 1 := by linarith
  have ha1' : a - 1 ≠ 0 := ha1.ne'
  have hpi : π ≠ 0 := Real.pi_ne_zero
  have hR : π * a * (a + 1) / (a - 1) * (Δ ^ 2 / r ^ 2) * (1 + stdDev r ^ 2 / 2 ^ 30) =
      a * π * (Δ ^ 2 / r ^ 2) * ((a + 1) / (a - 1)) +
        a * (a + 1) * Δ ^ 2 / (2 ^ 31 * (a - 1)) := by
    rw [stdDev_sq]
    field_simp
  have hap : 0 ≤ a * π := mul_nonneg (by linarith) Real.pi_pos.le
  have h1 : a * π * Δ ^ 2 / r ^ 2 ≤ a * π * (Δ ^ 2 / r ^ 2) * ((a + 1) / (a - 1)) := by
    rw [mul_div_assoc]
    exact le_mul_of_one_le_right (mul_nonneg hap (by positivity))
      ((one_le_div ha1).2 (by linarith))
  rw [hR]
  linarith

/-- For `r² ≤ 12.56`, the exponent of `renyiDiv_shift_le` is at most
`(πa(a+1)/(a-1)) (Δ²/r²) (1 + 2⁻²⁹)`. -/
theorem explicit_exponent_le_paper_of_sq_le {r a Δ : ℝ} (hr : r ≠ 0) (hr2 : r ^ 2 ≤ 1256 / 100)
    (ha : 1 < a) :
    a * π * Δ ^ 2 / r ^ 2 + a * (a + 1) * Δ ^ 2 / (2 ^ 31 * (a - 1)) ≤
      π * a * (a + 1) / (a - 1) * (Δ ^ 2 / r ^ 2) * (1 + 1 / 2 ^ 29) := by
  have hs := stdDev_sq_le_two hr2
  have hK : 0 ≤ π * a * (a + 1) / (a - 1) * (Δ ^ 2 / r ^ 2) :=
    mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg Real.pi_pos.le (by linarith)) (by linarith))
      (by linarith)) (by positivity)
  exact (explicit_exponent_le_paper hr ha).trans (mul_le_mul_of_nonneg_left (by linarith) hK)

/-- **Lemma 5, the paper's form** (restricted to `r ≥ 1.277·√(2π) ≈ 3.20`). For
`r/√(2π) ≥ 1.277`, `a > 1` and `|c^fp - c| ≤ Δ`:
`log R_a(D_{ℤ,r,c^fp} ‖ D_{ℤ,r,c}) ≤ (πa(a+1)/(a-1)) (Δ²/r²) (1 + (r/√(2π))²/2³⁰)`. -/
theorem renyiDiv_le_of_abs_sub_le (r c cfp Δ a : ℝ) (hr : 1277 / 1000 ≤ stdDev r) (ha : 1 < a)
    (hΔ : |cfp - c| ≤ Δ) :
    renyiDiv a (discreteGaussianMeasure (stdDev r) cfp) (discreteGaussianMeasure (stdDev r) c) ≤
      ENNReal.ofReal (Real.exp
        (π * a * (a + 1) / (a - 1) * (Δ ^ 2 / r ^ 2) * (1 + stdDev r ^ 2 / 2 ^ 30))) := by
  have h := renyiDiv_shift_le r c (cfp - c) a hr ha
  rw [add_sub_cancel] at h
  have hδ : (cfp - c) ^ 2 ≤ Δ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hΔ 2
  exact h.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
    ((explicit_exponent_le_of_sq_le ha hδ).trans (explicit_exponent_le_paper
      (pos_of_pos_stdDev (lt_of_lt_of_le (by norm_num) hr)).ne' ha))))

/-- **Lemma 5 at Mitaka-512** (`r = 3.305`): `log R_a ≤ (πa(a+1)/(a-1)) (Δ²/r²) (1 + 2⁻²⁹)`. -/
theorem renyiDiv_le_of_abs_sub_le_mitaka512 (c cfp Δ a : ℝ) (ha : 1 < a) (hΔ : |cfp - c| ≤ Δ) :
    renyiDiv a (discreteGaussianMeasure (stdDev (3305 / 1000)) cfp)
        (discreteGaussianMeasure (stdDev (3305 / 1000)) c) ≤
      ENNReal.ofReal (Real.exp
        (π * a * (a + 1) / (a - 1) * (Δ ^ 2 / (3305 / 1000) ^ 2) * (1 + 1 / 2 ^ 29))) := by
  have h := renyiDiv_shift_le _ c (cfp - c) a stdDev_mitaka512 ha
  rw [add_sub_cancel] at h
  have hδ : (cfp - c) ^ 2 ≤ Δ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hΔ 2
  exact h.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
    ((explicit_exponent_le_of_sq_le ha hδ).trans
      (explicit_exponent_le_paper_of_sq_le (by norm_num) (by norm_num) ha))))

/-- **Lemma 5 at Mitaka-1024** (`r = 3.34`): `log R_a ≤ (πa(a+1)/(a-1)) (Δ²/r²) (1 + 2⁻²⁹)`. -/
theorem renyiDiv_le_of_abs_sub_le_mitaka1024 (c cfp Δ a : ℝ) (ha : 1 < a) (hΔ : |cfp - c| ≤ Δ) :
    renyiDiv a (discreteGaussianMeasure (stdDev (334 / 100)) cfp)
        (discreteGaussianMeasure (stdDev (334 / 100)) c) ≤
      ENNReal.ofReal (Real.exp
        (π * a * (a + 1) / (a - 1) * (Δ ^ 2 / (334 / 100) ^ 2) * (1 + 1 / 2 ^ 29))) := by
  have h := renyiDiv_shift_le _ c (cfp - c) a stdDev_mitaka1024 ha
  rw [add_sub_cancel] at h
  have hδ : (cfp - c) ^ 2 ≤ Δ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hΔ 2
  exact h.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
    ((explicit_exponent_le_of_sq_le ha hδ).trans
      (explicit_exponent_le_paper_of_sq_le (by norm_num) (by norm_num) ha))))

end Mitaka.Lemma5
