/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.RenyiHybrid

/-! # Weak triangle inequality for the Rényi divergence

For probability measures `μ, ν, ρ` on a countable space, `a > 1` and a Hölder exponent `p > 1`,

`log R_a(μ ‖ ρ) ≤ ((a - 1/p)/(a - 1)) log R_{pa}(μ ‖ ν) + log R_{(pa-1)/(p-1)}(ν ‖ ρ)`.

Proof idea: Hölder's inequality with exponents `p`, `p/(p-1)` on
`∑ μ^a ρ^{1-a} = ∑ (μ^a ν^{1/p-a}) (ν^{a-1/p} ρ^{1-a})`. VCVio's `renyiDiv` is the
multiplicative divergence `R_a`, so the statements are products of powers.

[ZKLY26] (ePrint 2026/2521), proof of Theorem 1 (p. 7, l. 239) uses the instance
`p = (2a-1)/a`: `log R_a(P ‖ Q₀) ≤ (2a/(2a-1)) log R_{2a-1}(P ‖ Q_e) + log R_{2a}(Q_e ‖ Q₀)`
(`renyiDiv_le_rpow_mul_renyiDiv_two_mul`). -/

@[expose] public section

open MeasureTheory InformationTheory
open scoped ENNReal

namespace Mitaka.RenyiTriangle

variable {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]

/-- For `b > 1`, the Hellinger sum of a probability measure against a finite measure is not `0`. -/
private theorem tsum_rpow_mul_rpow_ne_zero {b : ℝ} (hb : 1 < b) (ν ρ : Measure α)
    [IsProbabilityMeasure ν] [IsFiniteMeasure ρ] :
    ∑' x, ν {x} ^ b * ρ {x} ^ (1 - b) ≠ 0 := by
  obtain ⟨y, hy⟩ : ∃ y, ν {y} ≠ 0 := by
    by_contra h
    push Not at h
    have h1 : ∑' x, ν {x} = ν Set.univ := by rw [← lintegral_one, lintegral_countable']; simp
    simp [h] at h1
  rw [Ne, tsum_eq_zero_iff, not_forall]
  refine ⟨y, mul_ne_zero (ENNReal.rpow_pos (pos_iff_ne_zero.2 hy) (measure_ne_top _ _)).ne' ?_⟩
  rw [Ne, ENNReal.rpow_eq_zero_iff]
  rintro (⟨-, h⟩ | ⟨h, -⟩)
  · linarith
  · exact measure_ne_top _ _ h

/-- Hölder's inequality for Rényi MGFs: `M_a(μ ‖ ρ) ≤ M_{pa}(μ ‖ ν)^{1/p}
M_{(pa-1)/(p-1)}(ν ‖ ρ)^{(p-1)/p}`. -/
theorem renyiMGF_le_rpow_mul_rpow {a p : ℝ} (ha : 1 < a) (hp : 1 < p) (μ ν ρ : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] :
    renyiMGF a μ ρ ≤
      renyiMGF (p * a) μ ν ^ (1 / p) * renyiMGF ((p * a - 1) / (p - 1)) ν ρ ^ ((p - 1) / p) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hpa : 1 < p * a := by nlinarith
  have hb : 1 < (p * a - 1) / (p - 1) := by rw [lt_div_iff₀ hp1]; nlinarith
  rw [FalconPrecision.RenyiHybrid.renyiMGF_eq_tsum ha,
    FalconPrecision.RenyiHybrid.renyiMGF_eq_tsum hpa,
    FalconPrecision.RenyiHybrid.renyiMGF_eq_tsum hb]
  by_cases hac : ∃ x, μ {x} ≠ 0 ∧ ν {x} = 0
  · obtain ⟨x, hμx, hνx⟩ := hac
    have htop : ∑' y, μ {y} ^ (p * a) * ν {y} ^ (1 - p * a) = ⊤ := by
      refine top_le_iff.1 (le_trans (le_of_eq ?_)
        (le_tsum (fun y => μ {y} ^ (p * a) * ν {y} ^ (1 - p * a)) x))
      change ⊤ = μ {x} ^ (p * a) * ν {x} ^ (1 - p * a)
      rw [hνx, ENNReal.zero_rpow_of_neg (by linarith),
        ENNReal.mul_top (ENNReal.rpow_pos (pos_iff_ne_zero.2 hμx) (measure_ne_top _ _)).ne']
    have hne : (∑' y, ν {y} ^ ((p * a - 1) / (p - 1)) * ρ {y} ^ (1 - (p * a - 1) / (p - 1))) ^
        ((p - 1) / p) ≠ 0 := by
      rw [Ne, ENNReal.rpow_eq_zero_iff]
      rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact tsum_rpow_mul_rpow_ne_zero hb ν ρ h
      · exact absurd h (not_lt.2 (div_nonneg hp1.le hp0.le))
    rw [htop, ENNReal.top_rpow_of_pos (one_div_pos.2 hp0), ENNReal.top_mul hne]
    exact le_top
  · push Not at hac
    have hpq : p.HolderConjugate (p / (p - 1)) := Real.HolderConjugate.conjExponent hp
    have e2 : (1 / p - a) * p = 1 - p * a := by
      rw [sub_mul, one_div_mul_cancel hp0.ne']
      ring
    have e3 : (a - 1 / p) * (p / (p - 1)) = (p * a - 1) / (p - 1) := by
      rw [← mul_div_assoc, sub_mul, one_div_mul_cancel hp0.ne', mul_comm a p]
    have e4 : (1 - a) * (p / (p - 1)) = 1 - (p * a - 1) / (p - 1) := by
      rw [← mul_div_assoc, eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hp1.ne']
      ring
    have hle : ∑' x, μ {x} ^ a * ρ {x} ^ (1 - a) ≤
        ∑' x, μ {x} ^ a * ν {x} ^ (1 / p - a) * (ν {x} ^ (a - 1 / p) * ρ {x} ^ (1 - a)) := by
      refine tsum_le_tsum fun x => ?_
      by_cases hμx : μ {x} = 0
      · rw [hμx, ENNReal.zero_rpow_of_pos (by linarith), zero_mul]
        positivity
      · have e : ν {x} ^ (1 / p - a) * ν {x} ^ (a - 1 / p) = 1 := by
          rw [← ENNReal.rpow_add _ _ (hac x hμx) (measure_ne_top _ _), sub_add_sub_cancel,
            sub_self, ENNReal.rpow_zero]
        refine le_of_eq ?_
        calc μ {x} ^ a * ρ {x} ^ (1 - a) =
            μ {x} ^ a * (ν {x} ^ (1 / p - a) * ν {x} ^ (a - 1 / p)) * ρ {x} ^ (1 - a) := by
              rw [e, mul_one]
          _ = _ := by ring
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq Measure.count hpq
      (f := fun x => μ {x} ^ a * ν {x} ^ (1 / p - a))
      (g := fun x => ν {x} ^ (a - 1 / p) * ρ {x} ^ (1 - a))
      (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable
    simp only [lintegral_count, Pi.mul_apply] at hH
    refine hle.trans (hH.trans (le_of_eq ?_))
    have hF : ∀ x, (μ {x} ^ a * ν {x} ^ (1 / p - a)) ^ p = μ {x} ^ (p * a) * ν {x} ^ (1 - p * a) :=
      fun x => by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, e2,
          mul_comm a p]
    have hG : ∀ x, (ν {x} ^ (a - 1 / p) * ρ {x} ^ (1 - a)) ^ (p / (p - 1)) =
        ν {x} ^ ((p * a - 1) / (p - 1)) * ρ {x} ^ (1 - (p * a - 1) / (p - 1)) := fun x => by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (div_nonneg hp0.le hp1.le), ← ENNReal.rpow_mul,
        ← ENNReal.rpow_mul, e3, e4]
    simp only [hF, hG, one_div_div]

/-- **Weak triangle inequality.** `R_a(μ ‖ ρ) ≤ R_{pa}(μ ‖ ν)^{(a-1/p)/(a-1)}
R_{(pa-1)/(p-1)}(ν ‖ ρ)`. -/
theorem renyiDiv_le_rpow_mul_renyiDiv {a p : ℝ} (ha : 1 < a) (hp : 1 < p) (μ ν ρ : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] :
    renyiDiv a μ ρ ≤
      renyiDiv (p * a) μ ν ^ ((a - 1 / p) / (a - 1)) * renyiDiv ((p * a - 1) / (p - 1)) ν ρ := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have ha1 : 0 < a - 1 := by linarith
  have hpa : 1 < p * a := by nlinarith
  have hpa1 : 0 < p * a - 1 := by linarith
  have hp0' := hp0.ne'
  have ha1' := ha1.ne'
  have hpa1' := hpa1.ne'
  have hb : 1 < (p * a - 1) / (p - 1) := by rw [lt_div_iff₀ hp1]; nlinarith
  have hb1 : (p * a - 1) / (p - 1) - 1 = p * (a - 1) / (p - 1) := by
    rw [eq_div_iff hp1.ne', sub_mul, div_mul_cancel₀ _ hp1.ne']
    ring
  rw [renyiDiv_eq_rpow ha, renyiDiv_eq_rpow hpa, renyiDiv_eq_rpow hb, ← ENNReal.rpow_mul, hb1,
    inv_div]
  calc renyiMGF a μ ρ ^ (a - 1)⁻¹
      ≤ (renyiMGF (p * a) μ ν ^ (1 / p) *
          renyiMGF ((p * a - 1) / (p - 1)) ν ρ ^ ((p - 1) / p)) ^ (a - 1)⁻¹ :=
        ENNReal.rpow_le_rpow (renyiMGF_le_rpow_mul_rpow ha hp μ ν ρ) (inv_nonneg.2 ha1.le)
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 ha1.le), ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        congr 2
        · field_simp
        · field_simp

/-- **Weak triangle inequality at `p = (2a-1)/a`** ([ZKLY26, p. 7, l. 239]):
`R_a(μ ‖ ρ) ≤ R_{2a-1}(μ ‖ ν)^{2a/(2a-1)} R_{2a}(ν ‖ ρ)`. -/
theorem renyiDiv_le_rpow_mul_renyiDiv_two_mul {a : ℝ} (ha : 1 < a) (μ ν ρ : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] :
    renyiDiv a μ ρ ≤
      renyiDiv (2 * a - 1) μ ν ^ (2 * a / (2 * a - 1)) * renyiDiv (2 * a) ν ρ := by
  have ha0 : 0 < a := by linarith
  have ha1 : a - 1 ≠ 0 := by linarith
  have h2a : 2 * a - 1 ≠ 0 := by linarith
  have hp : 1 < (2 * a - 1) / a := by rw [lt_div_iff₀ ha0]; linarith
  have h := renyiDiv_le_rpow_mul_renyiDiv ha hp μ ν ρ
  have e1 : (2 * a - 1) / a * a = 2 * a - 1 := div_mul_cancel₀ _ ha0.ne'
  have e4 : (2 * a - 1) / a - 1 = (a - 1) / a := by
    rw [eq_div_iff ha0.ne', sub_mul, div_mul_cancel₀ _ ha0.ne']
    ring
  have e2 : ((2 * a - 1) / a * a - 1) / ((2 * a - 1) / a - 1) = 2 * a := by
    rw [e1, e4, div_div_eq_mul_div, div_eq_iff ha1]
    ring
  have e3 : (a - 1 / ((2 * a - 1) / a)) / (a - 1) = 2 * a / (2 * a - 1) := by
    rw [one_div_div, div_eq_div_iff ha1 h2a, sub_mul, div_mul_cancel₀ _ h2a]
    ring
  rwa [e2, e3, e1] at h

end Mitaka.RenyiTriangle
