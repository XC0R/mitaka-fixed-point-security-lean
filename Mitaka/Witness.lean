/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import Mitaka.Sampler
public import VCVio.OracleComp.EvalDist.AnswerMeasure

/-! # Perfect samplers exist, and the fixed-point step at Table 2

The world hypotheses of the theorems of `Mitaka.Sampler` are satisfiable. Over the oracle
specification `wspec` of a perfect discrete Gaussian sampler (queries `(σ, c)` with `σ > 0`, answer
measure `D_{ℤ,σ,c}`), `world P fp` answers a perturbation query by `D_{ℤ,Lr,0}` and an online query
at `c` by `D_{ℤ,r,fp c}` (`evalDist_world`, `worlds_exist`). The construction follows
`FalconPrecision.FalconWitness` of FalconPrecision 0.4.0 (`FalconPrecision/Witness.lean`). The
worlds are idealised samplers (an oracle that answers exactly `D_{ℤ,σ,c}`), so no `ProbComp`
implementation is claimed.

`renyiDiv_sample_le_mitaka512`, `renyiDiv_sample_le_mitaka1024`: the fixed-point step of [ZKLY26]
(ePrint 2026/2521, p. 8-9, l. 277-282) at the parameters of Table 2 (p. 9), in the paper's form
`log R_a(P_fp ‖ P) ≤ (2πna(a+1)/(a-1)) (Δ²/r²) (1 + 2⁻²⁹)`. `renyiDiv_sample_world_mitaka512` and
`renyiDiv_sample_world_mitaka1024` state it for the worlds `world`. -/

@[expose] public section

open Real MeasureTheory InformationTheory OracleSpec OracleComp LatticeCrypto
open scoped ENNReal

namespace Mitaka

/-- A query to a perfect discrete Gaussian sampler: a positive standard deviation and a centre. -/
abbrev GaussianQuery := {p : ℝ × ℝ // 0 < p.1}

/-- The oracle of a perfect discrete Gaussian sampler, answered in `ℤ`. -/
@[reducible] def wspec : OracleSpec GaussianQuery := fun _ => ℤ

/-- Query `(σ, c)` of `wspec` is answered by `D_{ℤ,σ,c}`. -/
noncomputable instance instAnswerMeasureWspec : OracleSpec.AnswerMeasure wspec :=
  @PFunctor.AnswerMeasure.mk wspec.toPFunctor (fun _ => ⊤)
    (fun p => discreteGaussianMeasure p.1.1 p.1.2)
    (fun p => isProbabilityMeasure_discreteGaussianMeasure p.1.1 p.1.2 p.2)

/-- One query to the perfect sampler at standard deviation `σ > 0` and centre `c`. -/
def gaussian (σ c : ℝ) (hσ : 0 < σ) : OracleComp wspec ℤ :=
  liftM (OracleSpec.query (spec := wspec) ⟨(σ, c), hσ⟩)

/-- The law of `gaussian σ c` is `D_{ℤ,σ,c}`. -/
theorem evalDist_gaussian (σ c : ℝ) (hσ : 0 < σ) :
    @evalDist _ _ ℤ ⊤ (gaussian σ c hσ) = discreteGaussianMeasure σ c :=
  (@evalDist_liftM_query _ wspec _ ⟨(σ, c), hσ⟩ ⊤).trans (@MeasureTheory.trim_eq_self _ ⊤ _)

/-- The world with perfect samplers in which online centres are converted by `fp`. -/
noncomputable def world (P : Params) (fp : ℝ → ℝ) (hr : 0 < P.r) (hL : 0 < P.L) :
    QueryImpl samplerSpec (OracleComp wspec)
  | .perturb => gaussian (Lemma5.stdDev (P.L * P.r)) 0
      (Lemma5.stdDev_pos (mul_pos (by exact_mod_cast hL) hr))
  | .online c => gaussian (Lemma5.stdDev P.r) (fp c) (Lemma5.stdDev_pos hr)

/-- The answers of `world P fp` have the laws `answer P fp`. -/
theorem evalDist_world (P : Params) (fp : ℝ → ℝ) (hr : 0 < P.r) (hL : 0 < P.L) (t : Query) :
    @evalDist _ _ (samplerSpec.Range t) ⊤ (world P fp hr hL t) = answer P fp t := by
  cases t with
  | perturb => exact evalDist_gaussian _ _ _
  | online c => exact evalDist_gaussian _ _ _

/-- **The world hypotheses are satisfiable.** For positive widths there are an exact and a
fixed-point world with the answer laws `answer P id` and `answer P fp`. -/
theorem worlds_exist (P : Params) (fp : ℝ → ℝ) (hr : 0 < P.r) (hL : 0 < P.L) :
    ∃ implE implF : QueryImpl samplerSpec (OracleComp wspec),
      (∀ t, @evalDist _ _ (samplerSpec.Range t) ⊤ (implE t) = answer P id t) ∧
        (∀ t, @evalDist _ _ (samplerSpec.Range t) ⊤ (implF t) = answer P fp t) :=
  ⟨world P id hr hL, world P fp hr hL, evalDist_world P id hr hL, evalDist_world P fp hr hL⟩

/-- The online width of Mitaka-512 is positive. -/
theorem Params.mitaka512_r_pos : 0 < Params.mitaka512.r := by norm_num [Params.mitaka512]

/-- The perturbation scaling factor of Mitaka-512 is positive. -/
theorem Params.mitaka512_L_pos : 0 < Params.mitaka512.L := by norm_num [Params.mitaka512]

/-- The online width of Mitaka-1024 is positive. -/
theorem Params.mitaka1024_r_pos : 0 < Params.mitaka1024.r := by norm_num [Params.mitaka1024]

/-- The perturbation scaling factor of Mitaka-1024 is positive. -/
theorem Params.mitaka1024_L_pos : 0 < Params.mitaka1024.L := by norm_num [Params.mitaka1024]

variable {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m] {n : ℕ}

/-- **The fixed-point step at Mitaka-512** ([ZKLY26, p. 9, l. 282] at `r = 3.305`), for every `n`
(Table 2: `n = 512`): if every online centre is converted within `Δ`, then
`log R_a(P_fp ‖ P) ≤ (2πna(a+1)/(a-1)) (Δ²/r²) (1 + 2⁻²⁹)`. -/
theorem renyiDiv_sample_le_mitaka512 (K : Key n) (c : Fin 2 → Fin n → ℝ) (fp : ℝ → ℝ) {Δ : ℝ}
    (hfp : ∀ x, |fp x - x| ≤ Δ) {a : ℝ} (ha : 1 < a) (implE implF : QueryImpl samplerSpec m)
    (hE : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implE t) = answer Params.mitaka512 id t)
    (hF : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implF t) = answer Params.mitaka512 fp t) :
    renyiDiv a 𝒟[simulateQ implF (sample Params.mitaka512 K c)]
        𝒟[simulateQ implE (sample Params.mitaka512 K c)] ≤
      ENNReal.ofReal (Real.exp (2 * π * n * a * (a + 1) / (a - 1) *
        (Δ ^ 2 / (3305 / 1000) ^ 2) * (1 + 1 / 2 ^ 29))) := by
  refine (renyiDiv_sample_le Params.mitaka512 K c fp hfp Lemma5.stdDev_mitaka512 ha implE implF hE
    hF).trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
  calc _ ≤ 2 * n * (π * a * (a + 1) / (a - 1) * (Δ ^ 2 / (3305 / 1000) ^ 2) * (1 + 1 / 2 ^ 29)) :=
        mul_le_mul_of_nonneg_left
          (Lemma5.explicit_exponent_le_paper_of_sq_le (by norm_num) (by norm_num) ha)
          (by positivity)
    _ = _ := by ring

/-- **The fixed-point step at Mitaka-1024** ([ZKLY26, p. 9, l. 282] at `r = 3.34`), for every `n`
(Table 2: `n = 1024`): if every online centre is converted within `Δ`, then
`log R_a(P_fp ‖ P) ≤ (2πna(a+1)/(a-1)) (Δ²/r²) (1 + 2⁻²⁹)`. -/
theorem renyiDiv_sample_le_mitaka1024 (K : Key n) (c : Fin 2 → Fin n → ℝ) (fp : ℝ → ℝ) {Δ : ℝ}
    (hfp : ∀ x, |fp x - x| ≤ Δ) {a : ℝ} (ha : 1 < a) (implE implF : QueryImpl samplerSpec m)
    (hE : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implE t) = answer Params.mitaka1024 id t)
    (hF : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implF t) = answer Params.mitaka1024 fp t) :
    renyiDiv a 𝒟[simulateQ implF (sample Params.mitaka1024 K c)]
        𝒟[simulateQ implE (sample Params.mitaka1024 K c)] ≤
      ENNReal.ofReal (Real.exp (2 * π * n * a * (a + 1) / (a - 1) *
        (Δ ^ 2 / (334 / 100) ^ 2) * (1 + 1 / 2 ^ 29))) := by
  refine (renyiDiv_sample_le Params.mitaka1024 K c fp hfp Lemma5.stdDev_mitaka1024 ha implE implF
    hE hF).trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
  calc _ ≤ 2 * n * (π * a * (a + 1) / (a - 1) * (Δ ^ 2 / (334 / 100) ^ 2) * (1 + 1 / 2 ^ 29)) :=
        mul_le_mul_of_nonneg_left
          (Lemma5.explicit_exponent_le_paper_of_sq_le (by norm_num) (by norm_num) ha)
          (by positivity)
    _ = _ := by ring

/-- The fixed-point step at Mitaka-512, for every `n` (Table 2: `n = 512`), between the worlds
with perfect samplers. -/
theorem renyiDiv_sample_world_mitaka512 (K : Key n) (c : Fin 2 → Fin n → ℝ) (fp : ℝ → ℝ)
    {Δ : ℝ} (hfp : ∀ x, |fp x - x| ≤ Δ) {a : ℝ} (ha : 1 < a) :
    renyiDiv a
        𝒟[simulateQ (world Params.mitaka512 fp Params.mitaka512_r_pos Params.mitaka512_L_pos)
          (sample Params.mitaka512 K c)]
        𝒟[simulateQ (world Params.mitaka512 id Params.mitaka512_r_pos Params.mitaka512_L_pos)
          (sample Params.mitaka512 K c)] ≤
      ENNReal.ofReal (Real.exp (2 * π * n * a * (a + 1) / (a - 1) *
        (Δ ^ 2 / (3305 / 1000) ^ 2) * (1 + 1 / 2 ^ 29))) :=
  renyiDiv_sample_le_mitaka512 K c fp hfp ha _ _ (evalDist_world _ _ _ _)
    (evalDist_world _ _ _ _)

/-- The fixed-point step at Mitaka-1024, for every `n` (Table 2: `n = 1024`), between the worlds
with perfect samplers. -/
theorem renyiDiv_sample_world_mitaka1024 (K : Key n) (c : Fin 2 → Fin n → ℝ) (fp : ℝ → ℝ)
    {Δ : ℝ} (hfp : ∀ x, |fp x - x| ≤ Δ) {a : ℝ} (ha : 1 < a) :
    renyiDiv a
        𝒟[simulateQ (world Params.mitaka1024 fp Params.mitaka1024_r_pos Params.mitaka1024_L_pos)
          (sample Params.mitaka1024 K c)]
        𝒟[simulateQ (world Params.mitaka1024 id Params.mitaka1024_r_pos Params.mitaka1024_L_pos)
          (sample Params.mitaka1024 K c)] ≤
      ENNReal.ofReal (Real.exp (2 * π * n * a * (a + 1) / (a - 1) *
        (Δ ^ 2 / (334 / 100) ^ 2) * (1 + 1 / 2 ^ 29))) :=
  renyiDiv_sample_le_mitaka1024 K c fp hfp ha _ _ (evalDist_world _ _ _ _)
    (evalDist_world _ _ _ _)

end Mitaka
