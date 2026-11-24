/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.RenyiPath

/-! # Probability preservation with a real bit loss

`FalconPrecision.RenyiPath.lemma15` turns a joint Rényi bound at order `2λ − 1` with the budget
`R ≤ √2` into success `> T·2^{−(λ−1)}` ⇒ success `> T·2^{−λ}`: an integer loss of one bit. The
headline of [ZKLY26] (ePrint 2026/2521, p. 9, l. 289-292) is a loss of 1.5 bits. This file states
the general form, for any order `a > 1`, any real `λ` and any real loss `L`:

* `measure_lt_of_renyiDiv_le`: if `R_a(μ‖ν) ≤ exp D` and `λ + (a − 1)·D/ln 2 ≤ a·L`, then
  `T·2^{−(λ−L)} < μ s` implies `T·2^{−λ} < ν s` for every `T ≥ 1`. The condition is the loss
  `λ/a + ((a − 1)/a)·D/ln 2 ≤ L` (in bits) of the probability-preservation inequality
  `ν s ≥ μ s^{a/(a−1)} / R_a(μ‖ν)`.
* `renyiDiv_simulateQ_le_path`: per-query bounds `R_a ≤ exp(X·w t)` (`X ≥ 0`) and a path budget
  `Σ w ≤ S` along every execution give `R_a ≤ exp(X·S)` for the simulated outputs
  (`RenyiPath.renyiMGF_simulateQ_le_path`, Lemma 16 of ePrint 2026/1531 in budget form).
* `measure_simulateQ_lt_path`: the transfer along an oracle computation, with `D = X·S`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory OracleSpec OracleComp
open scoped ENNReal

namespace Mitaka.RealExponent

/-- **Probability preservation with a real exponent.** If `R_a(μ‖ν) ≤ exp D` and
`λ + (a − 1)·D/ln 2 ≤ a·L`, then success `> T·2^{−(λ−L)}` under `μ` gives success `> T·2^{−λ}`
under `ν`, for every `T ≥ 1`. -/
theorem measure_lt_of_renyiDiv_le {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {a D lam L : ℝ} (ha : 1 < a)
    (hD : renyiDiv a μ ν ≤ ENNReal.ofReal (Real.exp D))
    (hL : lam + (a - 1) * D / Real.log 2 ≤ a * L) (T : ℝ≥0∞) (hT : 1 ≤ T) {s : Set α}
    (hs : MeasurableSet s) (hwin : T * (2 : ℝ≥0∞) ^ (-(lam - L)) < μ s) :
    T * (2 : ℝ≥0∞) ^ (-lam) < ν s := by
  have ha1 : 0 < a - 1 := sub_pos.2 ha
  have he : 0 < a / (a - 1) := div_pos (by linarith) ha1
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set E := ENNReal.ofReal (Real.exp D) with hE
  have hE0 : E ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos D)).ne'
  have hEt : E ≠ ⊤ := ENNReal.ofReal_ne_top
  have hE2 : E = (2 : ℝ≥0∞) ^ (D / Real.log 2) := by
    rw [hE, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ENNReal.ofReal_rpow_of_pos two_pos,
      Real.rpow_def_of_pos two_pos, mul_div_cancel₀ _ hl2.ne']
  -- the exponent: `−λ + D/ln 2 ≤ −(λ − L)·a/(a − 1)`, i.e. `hL` multiplied out
  have hexp : -lam + D / Real.log 2 ≤ -(lam - L) * (a / (a - 1)) := by
    rw [mul_div_assoc', le_div_iff₀ ha1]
    have key : (-lam + D / Real.log 2) * (a - 1) =
        -lam * a + (lam + (a - 1) * D / Real.log 2) := by ring
    linarith
  have hTe : T ≤ T ^ (a / (a - 1)) := by
    have : 1 ≤ a / (a - 1) := by rw [le_div_iff₀ ha1]; linarith
    calc T = T ^ (1 : ℝ) := (ENNReal.rpow_one T).symm
      _ ≤ T ^ (a / (a - 1)) := ENNReal.rpow_le_rpow_of_exponent_le hT this
  have hQ := ENNReal.rpow_lt_rpow hwin he
  rw [ENNReal.mul_rpow_of_nonneg _ _ he.le, ← ENNReal.rpow_mul] at hQ
  have hQ' : T * (2 : ℝ≥0∞) ^ (-lam) * E < μ s ^ (a / (a - 1)) := by
    refine lt_of_le_of_lt ?_ hQ
    rw [hE2, mul_assoc, ← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
    exact mul_le_mul' hTe (ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
  calc T * (2 : ℝ≥0∞) ^ (-lam) = T * (2 : ℝ≥0∞) ^ (-lam) * E / E :=
        (ENNReal.mul_div_cancel_right hE0 hEt).symm
    _ < μ s ^ (a / (a - 1)) / E := ENNReal.div_lt_div_right hE0 hEt hQ'
    _ ≤ μ s ^ (a / (a - 1)) / renyiDiv a μ ν := ENNReal.div_le_div_left hD _
    _ ≤ ν s := measure_rpow_div_renyiDiv_le ha μ ν hs

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} [∀ t, Countable (spec.Range t)]
  {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- A Rényi divergence bound `exp E` is a Rényi MGF bound `exp((a − 1)E)` (a copy of the private
helper of `Mitaka.Sampler`). -/
private theorem renyiMGF_le_of_renyiDiv_le {β : Type*} [MeasurableSpace β] {a : ℝ} (ha : 1 < a)
    {μ ν : Measure β} {E : ℝ} (h : renyiDiv a μ ν ≤ ENNReal.ofReal (Real.exp E)) :
    renyiMGF a μ ν ≤ ENNReal.ofReal (Real.exp ((a - 1) * E)) := by
  have ham : a - 1 ≠ 0 := by linarith
  rw [renyiDiv_eq_rpow ha] at h
  calc renyiMGF a μ ν = (renyiMGF a μ ν ^ (a - 1)⁻¹) ^ (a - 1) :=
        (ENNReal.rpow_inv_rpow ham _).symm
    _ ≤ ENNReal.ofReal (Real.exp E) ^ (a - 1) := ENNReal.rpow_le_rpow h (by linarith)
    _ = _ := by
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by linarith), ← Real.exp_mul,
          mul_comm]

/-- **Rényi divergence along executions.** If every query has `R_a(implQ t ‖ implP t) ≤ exp(X·w t)`
(`X ≥ 0`) and the weights of the queries made along every execution sum to at most `S`, then
`R_a(𝒟[simulateQ implQ oa] ‖ 𝒟[simulateQ implP oa]) ≤ exp(X·S)`
(`RenyiPath.renyiMGF_simulateQ_le_path` at `c = (a − 1)X`). -/
theorem renyiDiv_simulateQ_le_path {a X : ℝ} (ha : 1 < a) (hX : 0 ≤ X)
    (implQ implP : QueryImpl spec m) (w : ι → ℝ)
    (hB : ∀ t, @renyiDiv _ ⊤ a (@evalDist m _ (spec.Range t) ⊤ (implQ t))
      (@evalDist m _ (spec.Range t) ⊤ (implP t)) ≤ ENNReal.ofReal (Real.exp (X * w t)))
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    {oa : OracleComp spec α} {S : ℝ} (hS : FalconPrecision.RenyiPath.PathSum w oa S) :
    renyiDiv a 𝒟[simulateQ implQ oa] 𝒟[simulateQ implP oa] ≤
      ENNReal.ofReal (Real.exp (X * S)) := by
  have ham : 0 < a - 1 := sub_pos.2 ha
  have h := FalconPrecision.RenyiPath.renyiMGF_simulateQ_le_path ha implQ implP
    (mul_nonneg ham.le hX) w (fun t => (@renyiMGF_le_of_renyiDiv_le _ ⊤ a ha _ _ _ (hB t)).trans_eq
      (by rw [mul_assoc])) hS
  rw [renyiDiv_eq_rpow ha]
  calc renyiMGF a 𝒟[simulateQ implQ oa] 𝒟[simulateQ implP oa] ^ (a - 1)⁻¹
      ≤ ENNReal.ofReal (Real.exp ((a - 1) * X * S)) ^ (a - 1)⁻¹ :=
        ENNReal.rpow_le_rpow h (inv_nonneg.2 ham.le)
    _ = _ := by
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (inv_nonneg.2 ham.le),
          ← Real.exp_mul]
        congr 2
        field_simp

/-- **Probability preservation along executions, real exponent.** If every query has
`R_a(implQ t ‖ implP t) ≤ exp(X·w t)` and the weights of the queries made along every execution
sum to at most `S`, and `λ + (a − 1)·X·S/ln 2 ≤ a·L`, then success `> T·2^{−(λ−L)}` under `implQ`
gives success `> T·2^{−λ}` under `implP`, for every `T ≥ 1`. -/
theorem measure_simulateQ_lt_path {a X lam L : ℝ} (ha : 1 < a) (hX : 0 ≤ X)
    (implQ implP : QueryImpl spec m) (w : ι → ℝ)
    (hB : ∀ t, @renyiDiv _ ⊤ a (@evalDist m _ (spec.Range t) ⊤ (implQ t))
      (@evalDist m _ (spec.Range t) ⊤ (implP t)) ≤ ENNReal.ofReal (Real.exp (X * w t)))
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    {oa : OracleComp spec α} {S : ℝ} (hS : FalconPrecision.RenyiPath.PathSum w oa S)
    (hL : lam + (a - 1) * (X * S) / Real.log 2 ≤ a * L) (T : ℝ≥0∞) (hT : 1 ≤ T) {s : Set α}
    (hs : MeasurableSet s) (hwin : T * (2 : ℝ≥0∞) ^ (-(lam - L)) < 𝒟[simulateQ implQ oa] s) :
    T * (2 : ℝ≥0∞) ^ (-lam) < 𝒟[simulateQ implP oa] s :=
  measure_lt_of_renyiDiv_le _ _ ha (renyiDiv_simulateQ_le_path ha hX implQ implP w hB hS) hL T hT
    hs hwin

end Mitaka.RealExponent
