/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import Mitaka.Table2
public import Mitaka.RealExponent
public import Mitaka.Witness

/-! # The headline of [ZKLY26]: at most 1.5 bits of Rényi loss

[ZKLY26] (ePrint 2026/2521), p. 9, l. 289-292 (introduction, p. 2, l. 80-82): "the Rényi loss
incurred by using the new sampler is at most 1.5 bits for up to `Q_s = 2⁶⁴` signatures", for
Mitaka-512 (`λ = 128`) and Mitaka-1024 (`λ = 256`) at Table 2.

**The experiment.** For a fixed key `K` (key generation is outside the experiment), one
computation `oa : OracleComp (gameSpec aux n) α`: auxiliary oracles `aux` (adversary coins, salts,
the hash; everything other than the sampler) and sampler calls `c : Fin 2 → Fin n → ℝ` (the
target centre, computed by `oa` from its history), answered by a lattice point
`Fin 2 → Fin n → ℤ`. Signing (Algorithm 1, p. 4: hash, sample, norm check, retry) is part of
`oa`; each attempt is one sampler call. Two worlds:
* `fpWorld P K implA implF`, the fixed-point world: a sampler call at `c` runs Algorithm 3
  (`Mitaka.sample`) with the integer samplers `implF`, which answer online queries at the
  Algorithm 4 centre `q64Round c` (`hF`, perfect samplers);
* `implI`, the ideal world: a sampler call at `c` is answered by `𝒬₀ = D_{L(B),rs,c}`
  (`Key.gaussianQ0`, `hI`, stated on single points of the discrete answer type).
Auxiliary queries are answered by the same `implA` in both worlds (`hIA`). "At most `K` sampler
calls along every execution" is `PathSum samplerWeight oa K` (weight `1` per sampler call, `0`
per auxiliary query). Success is the probability of a measurable event `s` of the output.

**Statements.**
* `renyiDiv_game_le` (composition over `K` calls along every execution; per-call bound uniform in
  the centre).
* `Key.renyiDiv_call_le_mitaka512`, `…1024`: the per-call bound at Table 2 in the game's form
  (the corollaries `Key.renyiDiv_sample_q64Round_gaussianQ0_le_mitaka512`, `…1024`).
* `Key.headline_of_mitaka512`, `…1024`: success `> T·2^{−(λ−L)}` in the fixed-point world implies
  success `> T·2^{−λ}` in the ideal world, for every `T ≥ 1`, under the explicit condition
  `λ + (a − 1)·K·X/ln 2 ≤ a·L` (`RealExponent.measure_simulateQ_lt_path`).
* `headline_arith_*`: that condition, certified, at `a = 198` (512), `a = 738` (1024), `p = 1024`.
* `Key.headline_mitaka512`, `Key.headline_mitaka1024` (**M18**): `L = 1.5` bits with at most
  `(4/3)·2⁶⁴` (512) and `3·2⁶⁴` (1024) sampler calls along every execution.
* `Key.headline_tableRate_mitaka512`, `…1024`: `L = 1.3` and `L = 0.7` bits with at most
  `2⁶⁴(1 + c)` calls, `c = f/(1 − f)` rounded up at the upper ends of the rounding intervals of
  Table 2's measured per-attempt failure rates `f = 1.196%`, `0.0722%` (`f ≤ 1.1965%`,
  `f ≤ 0.07225%`; empirical; not proved).
* `headlineWorlds_exist`: the world hypotheses are jointly satisfiable (idealised oracles).

**Not proved here** (disclosed): that the number of sampler calls of Mitaka signing is bounded
along every execution, or by `Q_s(1 + c)` (Table 2's retry rates are measured; the theorems take
the bound as a hypothesis); the per-key hypotheses at `n = 512, 1024` (shown satisfiable only
at `n = 1`, `Mitaka.witness_hypotheses`); perfect integer samplers and the CDT truncation; the
implementation of the centres (§4.3, NTT, CRT); the modular norm check (Lemma 6); UF-CMA
security; that `T` is a running time (no cost model ties `T` to `oa`); a statement averaged
over key generation (the theorems hold for one fixed key with the per-key hypotheses). -/

@[expose] public section

open Real MeasureTheory InformationTheory OracleSpec OracleComp LatticeCrypto
  Mitaka.LatticeGaussian Mitaka.Algorithm4 FalconPrecision.RenyiPath
open scoped Matrix MatrixOrder ENNReal

namespace Mitaka

variable {n : ℕ}

/-- The experiment's oracles: auxiliary oracles and sampler calls at a target centre, answered by
a lattice point. -/
@[reducible] def gameSpec {ιA : Type} (aux : OracleSpec.{0, 0} ιA) (n : ℕ) :
    OracleSpec (ιA ⊕ (Fin 2 → Fin n → ℝ)) :=
  Sum.elim aux fun _ => Fin 2 → Fin n → ℤ

/-- Weight `1` on sampler calls, `0` on auxiliary queries. -/
def samplerWeight {ιA : Type} {n : ℕ} : ιA ⊕ (Fin 2 → Fin n → ℝ) → ℝ :=
  Sum.elim (fun _ => 0) fun _ => 1

variable {ιA : Type} {aux : OracleSpec.{0, 0} ιA} [hA : ∀ t, Countable (aux.Range t)]

/-- Every answer type of `gameSpec` is countable. -/
instance instCountableGameSpecRange : ∀ x, Countable ((gameSpec aux n).Range x)
  | .inl t => hA t
  | .inr _ => inferInstanceAs (Countable (Fin 2 → Fin n → ℤ))

variable {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m]

/-- The fixed-point world: auxiliary queries by `implA`; a sampler call at `c` runs Algorithm 3
with the integer samplers `implF`. -/
noncomputable def fpWorld (P : Params) (K : Key n) (implA : QueryImpl aux m)
    (implF : QueryImpl samplerSpec m) : QueryImpl (gameSpec aux n) m
  | .inl t => implA t
  | .inr c => simulateQ implF (sample P K c)

/-- The mass of a point under `pure`. -/
private theorem evalDist_pure_singleton {m₀ : Type → Type*} [Monad m₀] [EvalDistSemantics m₀]
    [LawfulPureEvalDistSemantics m₀] {β : Type} [ms : MeasurableSpace β]
    [MeasurableSingletonClass β] (y x : β) :
    evalDist (pure y : m₀ β) {x} = Set.indicator {x} 1 y := by
  rw [evalDist_pure, Measure.dirac_apply' _ (measurableSet_singleton x)]

/-- The mass of a point under a bind with a countable intermediate type (discrete structure). -/
private theorem evalDist_bind_singleton {m₀ : Type → Type*} [Monad m₀] [EvalDistSemantics m₀]
    [LawfulEvalDistSemantics m₀] {γ : Type} [Countable γ] {β : Type} [ms : MeasurableSpace β]
    [MeasurableSingletonClass β] (mx : m₀ γ) (f : γ → m₀ β) (x : β) :
    evalDist (mx >>= f) {x} = ∫⁻ u, evalDist (f u) {x} ∂(@evalDist m₀ _ γ ⊤ mx) := by
  let : MeasurableSpace γ := ⊤
  have : MeasurableSingletonClass γ := ⟨fun _ => trivial⟩
  rw [evalDist_bind_of_discrete, Measure.bind_apply (measurableSet_singleton x)
    measurable_from_top.aemeasurable]

/-- The point masses of a simulated computation depend only on the laws of the query answers, in
any monad and for any measurable structure with measurable singletons on the output. -/
theorem evalDist_simulateQ_singleton_eq {ι : Type} {spec : OracleSpec.{0, 0} ι}
    [∀ t, Countable (spec.Range t)] {m₁ m₂ : Type → Type*} [Monad m₁] [LawfulMonad m₁]
    [EvalDistSemantics m₁] [LawfulEvalDistSemantics m₁] [Monad m₂] [LawfulMonad m₂]
    [EvalDistSemantics m₂] [LawfulEvalDistSemantics m₂] (impl₁ : QueryImpl spec m₁)
    (impl₂ : QueryImpl spec m₂)
    (h : ∀ t, @evalDist m₁ _ (spec.Range t) ⊤ (impl₁ t) = @evalDist m₂ _ (spec.Range t) ⊤ (impl₂ t))
    {α : Type} (ms₁ ms₂ : MeasurableSpace α) [@MeasurableSingletonClass α ms₁]
    [@MeasurableSingletonClass α ms₂] (oa : OracleComp spec α) (x : α) :
    @evalDist m₁ _ α ms₁ (simulateQ impl₁ oa) {x} =
      @evalDist m₂ _ α ms₂ (simulateQ impl₂ oa) {x} := by
  induction oa using OracleComp.inductionOn with
  | pure y =>
    simp only [simulateQ_pure]
    rw [evalDist_pure_singleton (ms := ms₁), evalDist_pure_singleton (ms := ms₂)]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    rw [evalDist_bind_singleton (ms := ms₁), evalDist_bind_singleton (ms := ms₂), h t]
    exact lintegral_congr fun u => ih u

/-- On a countable type, Rényi divergences of finite measures depend only on the point masses, so
they agree across two measurable structures with measurable singletons. -/
private theorem renyiDiv_eq_of_singleton {β : Type} [Countable β] (ms₁ ms₂ : MeasurableSpace β)
    [@MeasurableSingletonClass β ms₁] [@MeasurableSingletonClass β ms₂] {a : ℝ} (ha : 1 < a)
    (μ₁ ν₁ : @Measure β ms₁) (μ₂ ν₂ : @Measure β ms₂) [@IsFiniteMeasure β ms₁ μ₁]
    [@IsFiniteMeasure β ms₁ ν₁] [@IsFiniteMeasure β ms₂ μ₂] [@IsFiniteMeasure β ms₂ ν₂]
    (hμ : ∀ x, μ₁ {x} = μ₂ {x}) (hν : ∀ x, ν₁ {x} = ν₂ {x}) :
    @renyiDiv β ms₁ a μ₁ ν₁ = @renyiDiv β ms₂ a μ₂ ν₂ := by
  rw [@renyiDiv_eq_rpow β ms₁ a ha, @renyiDiv_eq_rpow β ms₂ a ha,
    @FalconPrecision.RenyiHybrid.renyiMGF_eq_tsum β ms₁ _ _ a ha μ₁ ν₁ _ _,
    @FalconPrecision.RenyiHybrid.renyiMGF_eq_tsum β ms₂ _ _ a ha μ₂ ν₂ _ _]
  simp only [hμ, hν]

/-- A subprobability measure on a countable type has `R_a(μ‖μ) ≤ 1`. -/
private theorem renyiDiv_self_le_one {β : Type} [MeasurableSpace β] [Countable β]
    [MeasurableSingletonClass β] {a : ℝ} (ha : 1 < a) (μ : Measure β) [IsFiniteMeasure μ]
    (h1 : μ Set.univ ≤ 1) : renyiDiv a μ μ ≤ 1 := by
  rw [renyiDiv_eq_rpow ha]
  exact ENNReal.rpow_le_one (renyiMGF_self_le ha μ h1) (inv_nonneg.2 (by linarith))

/-- **Composition over the sampler calls of an experiment.** If every sampler call has
`R_a(fixed point ‖ ideal) ≤ exp X`, uniformly in the centre, auxiliary queries are answered
identically, and `oa` makes at most `S` sampler calls along every execution, then
`R_a(𝒟_fp[oa] ‖ 𝒟_ideal[oa]) ≤ exp(X·S)`. -/
theorem renyiDiv_game_le {a X : ℝ} (ha : 1 < a) (hX : 0 ≤ X) (P : Params) (K : Key n)
    (implA : QueryImpl aux m) (implF : QueryImpl samplerSpec m)
    (implI : QueryImpl (gameSpec aux n) m) (hIA : ∀ t, implI (.inl t) = implA t)
    (hcall : ∀ c, @renyiDiv _ ⊤ a
      (@evalDist m _ (Fin 2 → Fin n → ℤ) ⊤ (simulateQ implF (sample P K c)))
      (@evalDist m _ (Fin 2 → Fin n → ℤ) ⊤ (implI (.inr c))) ≤ ENNReal.ofReal (Real.exp X))
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oa : OracleComp (gameSpec aux n) α) {S : ℝ} (hS : PathSum samplerWeight oa S) :
    renyiDiv a 𝒟[simulateQ (fpWorld P K implA implF) oa] 𝒟[simulateQ implI oa] ≤
      ENNReal.ofReal (Real.exp (X * S)) := by
  refine RealExponent.renyiDiv_simulateQ_le_path ha hX _ _ samplerWeight (fun t => ?_) hS
  cases t with
  | inl t =>
    let : MeasurableSpace ((gameSpec aux n).Range (.inl t)) := ⊤
    have : MeasurableSingletonClass ((gameSpec aux n).Range (.inl t)) := ⟨fun _ => trivial⟩
    have h0 : X * samplerWeight (.inl t : ιA ⊕ (Fin 2 → Fin n → ℝ)) = 0 := by
      simp [samplerWeight]
    rw [h0, Real.exp_zero, ENNReal.ofReal_one, hIA t]
    exact renyiDiv_self_le_one ha _ (evalDist_apply_univ_le_one _)
  | inr c =>
    have h0 : X * samplerWeight (.inr c : ιA ⊕ (Fin 2 → Fin n → ℝ)) = X := by
      simp [samplerWeight]
    rw [h0]
    exact hcall c

namespace Key

/-- **One sampler call at Mitaka-512, in the game's form**: Algorithm 3 with Algorithm 4's centres
against any answer with the point masses of `𝒬₀` (`hI`), for `2 ≤ a ≤ 2¹⁹`, `2 ≤ p ≤ 2¹⁰`:
`log R_a ≤ 2⁻⁸⁸ + b·1.216·10⁻²²`, `b = (pa − 1)/(p − 1)`
(`Key.renyiDiv_sample_q64Round_gaussianQ0_le_mitaka512`).
Assumed, per key: `Key.Annular` (`α = 1.15`), `Key.NTRU`, `Key.GSCoeff`, `Key.UClose`,
`Key.CholeskyRoot`, `Key.AClose`; perfect integer samplers with `q64Round` centres (`hF`). -/
theorem renyiDiv_call_le_mitaka512 (K : Key 512) (u : Fin 512 → ℝ)
    (A : Fin 2 → Fin 2 → Fin 512 → ℝ) (hK : K.Annular Params.mitaka512)
    (hN : K.NTRU Params.mitaka512) (hu : K.GSCoeff u) (hr : K.UClose Params.mitaka512 u)
    (hC : K.CholeskyRoot Params.mitaka512 A) (hAc : K.AClose Params.mitaka512 A) {a p : ℝ}
    (ha : 2 ≤ a) (ha' : a ≤ 2 ^ 19) (hp : 2 ≤ p) (hp' : p ≤ 2 ^ 10)
    (implF : QueryImpl samplerSpec m)
    (hF : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implF t) =
      answer Params.mitaka512 q64Round t)
    (c : Fin 2 → Fin 512 → ℝ) (mI : m (Fin 2 → Fin 512 → ℤ))
    (hI : ∀ x, @evalDist m _ _ ⊤ mI {x} = K.gaussianQ0 Params.mitaka512 c {x}) :
    @renyiDiv _ ⊤ a
        (@evalDist m _ _ ⊤ (simulateQ implF (sample Params.mitaka512 K c)))
        (@evalDist m _ _ ⊤ mI) ≤
      ENNReal.ofReal (Real.exp (1 / 2 ^ 88 + (p * a - 1) / (p - 1) * (1216 / 10 ^ 25))) := by
  have hq : 0 < Params.mitaka512.q := by norm_num [Params.mitaka512]
  have hs0 : 0 < Params.mitaka512.s := by norm_num [Params.mitaka512]
  have := K.isProbabilityMeasure_gaussianQ0 Params.mitaka512 hq hN Params.mitaka512_r_pos hs0 c
  refine le_of_eq_of_le ?_ (renyiDiv_sample_q64Round_gaussianQ0_le_mitaka512 K u A hK hN hu hr hC
    hAc ha ha' hp hp' c (world Params.mitaka512 id Params.mitaka512_r_pos Params.mitaka512_L_pos)
    (world Params.mitaka512 q64Round Params.mitaka512_r_pos Params.mitaka512_L_pos)
    (evalDist_world _ _ _ _) (evalDist_world _ _ _ _))
  refine renyiDiv_eq_of_singleton ⊤ _ (by linarith) _ _ _ _ (fun x => ?_) hI
  exact evalDist_simulateQ_singleton_eq implF _
    (fun t => (hF t).trans (evalDist_world _ _ _ _ t).symm) ⊤ _ _ x

/-- **One sampler call at Mitaka-1024, in the game's form**: `log R_a ≤ 2⁻⁸⁸ + b·1.774·10⁻²³`
(`Key.renyiDiv_sample_q64Round_gaussianQ0_le_mitaka1024`). Assumed, per key: `Key.Annular`
(`α = 1.23`), `Key.NTRU`, `Key.GSCoeff`, `Key.UClose`, `Key.CholeskyRoot`, `Key.AClose`; perfect
integer samplers with `q64Round` centres (`hF`); the answer `mI` has the point masses of `𝒬₀`
(`hI`). -/
theorem renyiDiv_call_le_mitaka1024 (K : Key 1024) (u : Fin 1024 → ℝ)
    (A : Fin 2 → Fin 2 → Fin 1024 → ℝ) (hK : K.Annular Params.mitaka1024)
    (hN : K.NTRU Params.mitaka1024) (hu : K.GSCoeff u) (hr : K.UClose Params.mitaka1024 u)
    (hC : K.CholeskyRoot Params.mitaka1024 A) (hAc : K.AClose Params.mitaka1024 A) {a p : ℝ}
    (ha : 2 ≤ a) (ha' : a ≤ 2 ^ 19) (hp : 2 ≤ p) (hp' : p ≤ 2 ^ 10)
    (implF : QueryImpl samplerSpec m)
    (hF : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implF t) =
      answer Params.mitaka1024 q64Round t)
    (c : Fin 2 → Fin 1024 → ℝ) (mI : m (Fin 2 → Fin 1024 → ℤ))
    (hI : ∀ x, @evalDist m _ _ ⊤ mI {x} = K.gaussianQ0 Params.mitaka1024 c {x}) :
    @renyiDiv _ ⊤ a
        (@evalDist m _ _ ⊤ (simulateQ implF (sample Params.mitaka1024 K c)))
        (@evalDist m _ _ ⊤ mI) ≤
      ENNReal.ofReal (Real.exp (1 / 2 ^ 88 + (p * a - 1) / (p - 1) * (1774 / 10 ^ 26))) := by
  have hq : 0 < Params.mitaka1024.q := by norm_num [Params.mitaka1024]
  have hs0 : 0 < Params.mitaka1024.s := by norm_num [Params.mitaka1024]
  have := K.isProbabilityMeasure_gaussianQ0 Params.mitaka1024 hq hN Params.mitaka1024_r_pos hs0 c
  refine le_of_eq_of_le ?_ (renyiDiv_sample_q64Round_gaussianQ0_le_mitaka1024 K u A hK hN hu hr hC
    hAc ha ha' hp hp' c (world Params.mitaka1024 id Params.mitaka1024_r_pos Params.mitaka1024_L_pos)
    (world Params.mitaka1024 q64Round Params.mitaka1024_r_pos Params.mitaka1024_L_pos)
    (evalDist_world _ _ _ _) (evalDist_world _ _ _ _))
  refine renyiDiv_eq_of_singleton ⊤ _ (by linarith) _ _ _ _ (fun x => ?_) hI
  exact evalDist_simulateQ_singleton_eq implF _
    (fun t => (hF t).trans (evalDist_world _ _ _ _ t).symm) ⊤ _ _ x

/-- **The headline at Mitaka-512, general form.** For every order `2 ≤ a ≤ 2¹⁹`, Hölder exponent
`2 ≤ p ≤ 2¹⁰`, call budget `S`, `λ` and loss `L` with
`λ + (a − 1)·(2⁻⁸⁸ + b·1.216·10⁻²²)·S/ln 2 ≤ a·L`, `b = (pa − 1)/(p − 1)`: if `oa` makes at most
`S` sampler calls along every execution, success `> T·2^{−(λ−L)}` in the fixed-point world
implies success `> T·2^{−λ}` in the ideal world, for every `T ≥ 1`.
Assumed, per key: `Key.Annular` (`α = 1.15`), `Key.NTRU`, `Key.GSCoeff`, `Key.UClose`,
`Key.CholeskyRoot`, `Key.AClose`; the worlds: perfect integer samplers with `q64Round` centres
(`hF`), the ideal world answering sampler calls by `𝒬₀` (`hI`), auxiliary queries answered
identically (`hIA`); the call budget (`hS`). -/
theorem headline_of_mitaka512 (K : Key 512) (u : Fin 512 → ℝ)
    (A : Fin 2 → Fin 2 → Fin 512 → ℝ) (hK : K.Annular Params.mitaka512)
    (hN : K.NTRU Params.mitaka512) (hu : K.GSCoeff u) (hr : K.UClose Params.mitaka512 u)
    (hC : K.CholeskyRoot Params.mitaka512 A) (hAc : K.AClose Params.mitaka512 A)
    (implA : QueryImpl aux m) (implF : QueryImpl samplerSpec m)
    (hF : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implF t) =
      answer Params.mitaka512 q64Round t)
    (implI : QueryImpl (gameSpec aux 512) m) (hIA : ∀ t, implI (.inl t) = implA t)
    (hI : ∀ c x, @evalDist m _ _ ⊤ (implI (.inr c)) {x} = K.gaussianQ0 Params.mitaka512 c {x})
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oa : OracleComp (gameSpec aux 512) α) {a p S lam L : ℝ} (ha : 2 ≤ a) (ha' : a ≤ 2 ^ 19)
    (hp : 2 ≤ p) (hp' : p ≤ 2 ^ 10) (hS : PathSum samplerWeight oa S)
    (hL : lam + (a - 1) * ((1 / 2 ^ 88 + (p * a - 1) / (p - 1) * (1216 / 10 ^ 25)) * S) /
      Real.log 2 ≤ a * L)
    (T : ℝ≥0∞) (hT : 1 ≤ T) {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(lam - L)) <
      𝒟[simulateQ (fpWorld Params.mitaka512 K implA implF) oa] s) :
    T * (2 : ℝ≥0∞) ^ (-lam) < 𝒟[simulateQ implI oa] s := by
  have ha1 : (1 : ℝ) < a := by linarith
  have hpa : 0 ≤ p * a - 1 := by
    have := mul_le_mul hp ha (by norm_num) (by linarith)
    linarith
  have hX : (0 : ℝ) ≤ 1 / 2 ^ 88 + (p * a - 1) / (p - 1) * (1216 / 10 ^ 25) :=
    add_nonneg (by positivity) (mul_nonneg (div_nonneg hpa (by linarith)) (by positivity))
  exact RealExponent.measure_lt_of_renyiDiv_le _ _ ha1
    (renyiDiv_game_le ha1 hX _ K implA implF implI hIA
      (fun c => renyiDiv_call_le_mitaka512 K u A hK hN hu hr hC hAc ha ha' hp hp' implF hF c _
        (hI c)) oa hS) hL T hT hs hwin

/-- **The headline at Mitaka-1024, general form**: as `headline_of_mitaka512`, with the per-call
constant `1.774·10⁻²³`. Assumed, per key: `Key.Annular` (`α = 1.23`), `Key.NTRU`, `Key.GSCoeff`,
`Key.UClose`, `Key.CholeskyRoot`, `Key.AClose`; the worlds (`hF`, `hI`, `hIA`); the call budget
(`hS`). -/
theorem headline_of_mitaka1024 (K : Key 1024) (u : Fin 1024 → ℝ)
    (A : Fin 2 → Fin 2 → Fin 1024 → ℝ) (hK : K.Annular Params.mitaka1024)
    (hN : K.NTRU Params.mitaka1024) (hu : K.GSCoeff u) (hr : K.UClose Params.mitaka1024 u)
    (hC : K.CholeskyRoot Params.mitaka1024 A) (hAc : K.AClose Params.mitaka1024 A)
    (implA : QueryImpl aux m) (implF : QueryImpl samplerSpec m)
    (hF : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implF t) =
      answer Params.mitaka1024 q64Round t)
    (implI : QueryImpl (gameSpec aux 1024) m) (hIA : ∀ t, implI (.inl t) = implA t)
    (hI : ∀ c x, @evalDist m _ _ ⊤ (implI (.inr c)) {x} = K.gaussianQ0 Params.mitaka1024 c {x})
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oa : OracleComp (gameSpec aux 1024) α) {a p S lam L : ℝ} (ha : 2 ≤ a) (ha' : a ≤ 2 ^ 19)
    (hp : 2 ≤ p) (hp' : p ≤ 2 ^ 10) (hS : PathSum samplerWeight oa S)
    (hL : lam + (a - 1) * ((1 / 2 ^ 88 + (p * a - 1) / (p - 1) * (1774 / 10 ^ 26)) * S) /
      Real.log 2 ≤ a * L)
    (T : ℝ≥0∞) (hT : 1 ≤ T) {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(lam - L)) <
      𝒟[simulateQ (fpWorld Params.mitaka1024 K implA implF) oa] s) :
    T * (2 : ℝ≥0∞) ^ (-lam) < 𝒟[simulateQ implI oa] s := by
  have ha1 : (1 : ℝ) < a := by linarith
  have hpa : 0 ≤ p * a - 1 := by
    have := mul_le_mul hp ha (by norm_num) (by linarith)
    linarith
  have hX : (0 : ℝ) ≤ 1 / 2 ^ 88 + (p * a - 1) / (p - 1) * (1774 / 10 ^ 26) :=
    add_nonneg (by positivity) (mul_nonneg (div_nonneg hpa (by linarith)) (by positivity))
  exact RealExponent.measure_lt_of_renyiDiv_le _ _ ha1
    (renyiDiv_game_le ha1 hX _ K implA implF implI hIA
      (fun c => renyiDiv_call_le_mitaka1024 K u A hK hN hu hr hC hAc ha ha' hp hp' implF hF c _
        (hI c)) oa hS) hL T hT hs hwin

end Key

/-! ### The bit-loss arithmetic, certified (`a = 198` / `738`, `p = 1024`) -/

/-- **1.5 bits at Mitaka-512** for `(4/3)·2⁶⁴` sampler calls: `λ = 128`, `a = 198`, `p = 1024`,
`128 + 197·(2⁻⁸⁸ + b·1.216·10⁻²²)·(4/3)·2⁶⁴/ln 2 ≤ 198·1.5` (loss about 1.4973 bits). -/
theorem headline_arith_mitaka512 :
    (128 : ℝ) + (198 - 1) * ((1 / 2 ^ 88 + (1024 * 198 - 1) / (1024 - 1) * (1216 / 10 ^ 25)) *
      (4 / 3 * 2 ^ 64)) / Real.log 2 ≤ 198 * (3 / 2) := by
  rw [← le_sub_iff_add_le', div_le_iff₀ (Real.log_pos one_lt_two)]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (by norm_num))
  norm_num

/-- **1.5 bits at Mitaka-1024** for `3·2⁶⁴` sampler calls: `λ = 256`, `a = 738`, `p = 1024`
(loss about 1.3917 bits). -/
theorem headline_arith_mitaka1024 :
    (256 : ℝ) + (738 - 1) * ((1 / 2 ^ 88 + (1024 * 738 - 1) / (1024 - 1) * (1774 / 10 ^ 26)) *
      (3 * 2 ^ 64)) / Real.log 2 ≤ 738 * (3 / 2) := by
  rw [← le_sub_iff_add_le', div_le_iff₀ (Real.log_pos one_lt_two)]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (by norm_num))
  norm_num

/-- **1.3 bits at Mitaka-512** for `2⁶⁴(1 + 0.01211)` sampler calls (Table 2's measured
per-attempt failure rate `1.196%`, so `f ≤ 1.1965%` and `c = f/(1 − f) ≤ 0.01211`; loss about
1.2923 bits). -/
theorem headline_arith_tableRate_mitaka512 :
    (128 : ℝ) + (198 - 1) * ((1 / 2 ^ 88 + (1024 * 198 - 1) / (1024 - 1) * (1216 / 10 ^ 25)) *
      (2 ^ 64 * (1 + 1211 / 10 ^ 5))) / Real.log 2 ≤ 198 * (13 / 10) := by
  rw [← le_sub_iff_add_le', div_le_iff₀ (Real.log_pos one_lt_two)]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (by norm_num))
  norm_num

/-- **0.7 bits at Mitaka-1024** for `2⁶⁴(1 + 0.0007231)` sampler calls (Table 2's measured
per-attempt failure rate `0.0722%`, so `f ≤ 0.07225%` and `c = f/(1 − f) ≤ 0.0007231`; loss about
0.6954 bits). -/
theorem headline_arith_tableRate_mitaka1024 :
    (256 : ℝ) + (738 - 1) * ((1 / 2 ^ 88 + (1024 * 738 - 1) / (1024 - 1) * (1774 / 10 ^ 26)) *
      (2 ^ 64 * (1 + 7231 / 10 ^ 7))) / Real.log 2 ≤ 738 * (7 / 10) := by
  rw [← le_sub_iff_add_le', div_le_iff₀ (Real.log_pos one_lt_two)]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (by norm_num))
  norm_num

namespace Key

/-- **M18, the headline at Mitaka-512** ([ZKLY26, p. 9, l. 289-292], Falcon form, sampler calls
counted): for every key satisfying the per-key hypotheses and every experiment `oa` that makes at
most `(4/3)·2⁶⁴` sampler calls along every execution, success `> T·2^{−(128−1.5)}` with the
fixed-point sampler (Algorithm 3 with Algorithm 4's centres) implies success `> T·2^{−128}` with
the ideal `D_{L(B),rs,c}`, for every `T ≥ 1`.
Assumed, per key: condition 1 (`Key.Annular`, `α = 1.15`), `fG − gF = q` (`Key.NTRU`), the
Gram–Schmidt coefficient `u` (`Key.GSCoeff`), the key-expansion facts `Key.UClose`,
`Key.CholeskyRoot`, `Key.AClose`. Assumed about the experiment: perfect integer samplers with
`q64Round` centres (`hF`); the ideal world answers sampler calls by `𝒬₀` (`hI`); auxiliary
queries answered identically in both worlds (`hIA`); at most `(4/3)·2⁶⁴` sampler calls along
every execution (`hcalls`; Mitaka signing retries without a hard cap, so a signer satisfies this
only with a global call budget; Table 2's measured retry rate gives about `1.0121·2⁶⁴` calls on
average for `2⁶⁴` signatures, empirical, not proved). Conditions 2-4, `n = 2⁹`, the Lemma 5
width and `|q64Round c − c| ≤ 2⁻⁶⁴` are discharged inside. -/
theorem headline_mitaka512 (K : Key 512) (u : Fin 512 → ℝ)
    (A : Fin 2 → Fin 2 → Fin 512 → ℝ) (hK : K.Annular Params.mitaka512)
    (hN : K.NTRU Params.mitaka512) (hu : K.GSCoeff u) (hr : K.UClose Params.mitaka512 u)
    (hC : K.CholeskyRoot Params.mitaka512 A) (hAc : K.AClose Params.mitaka512 A)
    (implA : QueryImpl aux m) (implF : QueryImpl samplerSpec m)
    (hF : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implF t) =
      answer Params.mitaka512 q64Round t)
    (implI : QueryImpl (gameSpec aux 512) m) (hIA : ∀ t, implI (.inl t) = implA t)
    (hI : ∀ c x, @evalDist m _ _ ⊤ (implI (.inr c)) {x} = K.gaussianQ0 Params.mitaka512 c {x})
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oa : OracleComp (gameSpec aux 512) α) (hcalls : PathSum samplerWeight oa (4 / 3 * 2 ^ 64))
    (T : ℝ≥0∞) (hT : 1 ≤ T) {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(128 - 3 / 2 : ℝ)) <
      𝒟[simulateQ (fpWorld Params.mitaka512 K implA implF) oa] s) :
    T * (2 : ℝ≥0∞) ^ (-(128 : ℝ)) < 𝒟[simulateQ implI oa] s :=
  headline_of_mitaka512 K u A hK hN hu hr hC hAc implA implF hF implI hIA hI oa (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hcalls headline_arith_mitaka512 T hT hs hwin

/-- **M18, the headline at Mitaka-1024**: at most `3·2⁶⁴` sampler calls along every execution,
success `> T·2^{−(256−1.5)}` with the fixed-point sampler implies success `> T·2^{−256}` with
`D_{L(B),rs,c}`, for every `T ≥ 1`. Assumed, per key: `Key.Annular` (`α = 1.23`), `Key.NTRU`,
`Key.GSCoeff`, `Key.UClose`, `Key.CholeskyRoot`, `Key.AClose`; about the experiment: `hF`, `hI`,
`hIA`, and the call budget `hcalls` (no hard cap on retries in Mitaka signing; Table 2's measured
retry rate: about `1.0007·2⁶⁴` calls on average for `2⁶⁴` signatures, empirical, not proved).
Discharged inside: conditions 2-4, `n = 2¹⁰`, the Lemma 5 width, `|q64Round c − c| ≤ 2⁻⁶⁴`. -/
theorem headline_mitaka1024 (K : Key 1024) (u : Fin 1024 → ℝ)
    (A : Fin 2 → Fin 2 → Fin 1024 → ℝ) (hK : K.Annular Params.mitaka1024)
    (hN : K.NTRU Params.mitaka1024) (hu : K.GSCoeff u) (hr : K.UClose Params.mitaka1024 u)
    (hC : K.CholeskyRoot Params.mitaka1024 A) (hAc : K.AClose Params.mitaka1024 A)
    (implA : QueryImpl aux m) (implF : QueryImpl samplerSpec m)
    (hF : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implF t) =
      answer Params.mitaka1024 q64Round t)
    (implI : QueryImpl (gameSpec aux 1024) m) (hIA : ∀ t, implI (.inl t) = implA t)
    (hI : ∀ c x, @evalDist m _ _ ⊤ (implI (.inr c)) {x} = K.gaussianQ0 Params.mitaka1024 c {x})
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oa : OracleComp (gameSpec aux 1024) α) (hcalls : PathSum samplerWeight oa (3 * 2 ^ 64))
    (T : ℝ≥0∞) (hT : 1 ≤ T) {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(256 - 3 / 2 : ℝ)) <
      𝒟[simulateQ (fpWorld Params.mitaka1024 K implA implF) oa] s) :
    T * (2 : ℝ≥0∞) ^ (-(256 : ℝ)) < 𝒟[simulateQ implI oa] s :=
  headline_of_mitaka1024 K u A hK hN hu hr hC hAc implA implF hF implI hIA hI oa (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hcalls headline_arith_mitaka1024 T hT hs hwin

/-- **The headline at Table 2's measured retry rate, Mitaka-512**: at most `2⁶⁴(1 + 0.01211)`
sampler calls along every execution, a loss of 1.3 bits. Assumed: the per-key hypotheses
`Key.Annular` (`α = 1.15`), `Key.NTRU`, `Key.GSCoeff`, `Key.UClose`, `Key.CholeskyRoot`,
`Key.AClose`; `hF`, `hI`, `hIA`; and the call budget `hcalls`, the expected count for `2⁶⁴`
signatures at the measured failure rate `1.196%` (`f ≤ 1.1965%`; empirical, not proved),
required here along every execution. -/
theorem headline_tableRate_mitaka512 (K : Key 512) (u : Fin 512 → ℝ)
    (A : Fin 2 → Fin 2 → Fin 512 → ℝ) (hK : K.Annular Params.mitaka512)
    (hN : K.NTRU Params.mitaka512) (hu : K.GSCoeff u) (hr : K.UClose Params.mitaka512 u)
    (hC : K.CholeskyRoot Params.mitaka512 A) (hAc : K.AClose Params.mitaka512 A)
    (implA : QueryImpl aux m) (implF : QueryImpl samplerSpec m)
    (hF : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implF t) =
      answer Params.mitaka512 q64Round t)
    (implI : QueryImpl (gameSpec aux 512) m) (hIA : ∀ t, implI (.inl t) = implA t)
    (hI : ∀ c x, @evalDist m _ _ ⊤ (implI (.inr c)) {x} = K.gaussianQ0 Params.mitaka512 c {x})
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oa : OracleComp (gameSpec aux 512) α)
    (hcalls : PathSum samplerWeight oa (2 ^ 64 * (1 + 1211 / 10 ^ 5)))
    (T : ℝ≥0∞) (hT : 1 ≤ T) {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(128 - 13 / 10 : ℝ)) <
      𝒟[simulateQ (fpWorld Params.mitaka512 K implA implF) oa] s) :
    T * (2 : ℝ≥0∞) ^ (-(128 : ℝ)) < 𝒟[simulateQ implI oa] s :=
  headline_of_mitaka512 K u A hK hN hu hr hC hAc implA implF hF implI hIA hI oa (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hcalls headline_arith_tableRate_mitaka512 T hT hs hwin

/-- **The headline at Table 2's measured retry rate, Mitaka-1024**: at most
`2⁶⁴(1 + 0.0007231)` sampler calls along every execution, a loss of 0.7 bits. Assumed: the
per-key hypotheses `Key.Annular` (`α = 1.23`), `Key.NTRU`, `Key.GSCoeff`, `Key.UClose`,
`Key.CholeskyRoot`, `Key.AClose`; `hF`, `hI`, `hIA`; and the call budget `hcalls`, the expected
count for `2⁶⁴` signatures at the measured failure rate `0.0722%` (`f ≤ 0.07225%`; empirical,
not proved), required here along every execution. -/
theorem headline_tableRate_mitaka1024 (K : Key 1024) (u : Fin 1024 → ℝ)
    (A : Fin 2 → Fin 2 → Fin 1024 → ℝ) (hK : K.Annular Params.mitaka1024)
    (hN : K.NTRU Params.mitaka1024) (hu : K.GSCoeff u) (hr : K.UClose Params.mitaka1024 u)
    (hC : K.CholeskyRoot Params.mitaka1024 A) (hAc : K.AClose Params.mitaka1024 A)
    (implA : QueryImpl aux m) (implF : QueryImpl samplerSpec m)
    (hF : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implF t) =
      answer Params.mitaka1024 q64Round t)
    (implI : QueryImpl (gameSpec aux 1024) m) (hIA : ∀ t, implI (.inl t) = implA t)
    (hI : ∀ c x, @evalDist m _ _ ⊤ (implI (.inr c)) {x} = K.gaussianQ0 Params.mitaka1024 c {x})
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (oa : OracleComp (gameSpec aux 1024) α)
    (hcalls : PathSum samplerWeight oa (2 ^ 64 * (1 + 7231 / 10 ^ 7)))
    (T : ℝ≥0∞) (hT : 1 ≤ T) {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-(256 - 7 / 10 : ℝ)) <
      𝒟[simulateQ (fpWorld Params.mitaka1024 K implA implF) oa] s) :
    T * (2 : ℝ≥0∞) ^ (-(256 : ℝ)) < 𝒟[simulateQ implI oa] s :=
  headline_of_mitaka1024 K u A hK hN hu hr hC hAc implA implF hF implI hIA hI oa (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hcalls headline_arith_tableRate_mitaka1024 T hT hs
    hwin

/-- `𝒬₀` on the discrete measurable structure of its (countable) output type. -/
noncomputable def gaussianQ0Top (P : Params) (K : Key n) (c : Fin 2 → Fin n → ℝ) :
    @Measure (Fin 2 → Fin n → ℤ) ⊤ :=
  @Measure.map _ _ _ ⊤ id (K.gaussianQ0 P c)

end Key

/-! ### The world hypotheses are satisfiable (idealised oracles) -/

/-- An ideal lattice-Gaussian oracle: a query is a centre, the answer a lattice point. -/
@[reducible] def latticeSpec (n : ℕ) : OracleSpec (Fin 2 → Fin n → ℝ) :=
  fun _ => Fin 2 → Fin n → ℤ

/-- The ideal lattice-Gaussian oracle answers `c` by `𝒬₀ = D_{L(B),rs,c}` (for an NTRU key and
positive widths, so that `𝒬₀` is a probability measure). -/
@[instance_reducible]
noncomputable def latticeAnswerMeasure (P : Params) (K : Key n) (hq : 0 < P.q) (hN : K.NTRU P)
    (hr : 0 < P.r) (hs : 0 < P.s) : OracleSpec.AnswerMeasure (latticeSpec n) :=
  @PFunctor.AnswerMeasure.mk (latticeSpec n).toPFunctor (fun _ => ⊤)
    (fun c => K.gaussianQ0Top P c) (fun c => by
      have := K.isProbabilityMeasure_gaussianQ0 P hq hN hr hs c
      unfold Key.gaussianQ0Top
      infer_instance)

/-- The witness oracles: the auxiliary oracles, a perfect integer Gaussian sampler and an ideal
lattice-Gaussian oracle. -/
@[reducible] def witnessSpec {ιA : Type} (aux : OracleSpec.{0, 0} ιA) (n : ℕ) :
    OracleSpec ((ιA ⊕ GaussianQuery) ⊕ (Fin 2 → Fin n → ℝ)) :=
  aux + wspec + latticeSpec n

/-- **The headline's world hypotheses are jointly satisfiable.** Over the idealised oracles
`witnessSpec aux n` (auxiliary oracles with any answer measures, a perfect integer Gaussian sampler,
an ideal lattice-Gaussian oracle), there are `implA`, `implF`, `implI` with the hypotheses `hF`,
`hIA`, `hI` of the headline (the auxiliary answers keep their measures). No `ProbComp`
implementation is claimed. -/
theorem headlineWorlds_exist {ιA : Type} (aux : OracleSpec.{0, 0} ιA)
    [OracleSpec.AnswerMeasure aux] (P : Params) (K : Key n) (hq : 0 < P.q) (hN : K.NTRU P)
    (hr : 0 < P.r) (hs : 0 < P.s) (hL : 0 < P.L) :
    letI := latticeAnswerMeasure P K hq hN hr hs
    ∃ (implA : QueryImpl aux (OracleComp (witnessSpec aux n)))
      (implF : QueryImpl samplerSpec (OracleComp (witnessSpec aux n)))
      (implI : QueryImpl (gameSpec aux n) (OracleComp (witnessSpec aux n))),
      (∀ t, @evalDist _ _ (aux.Range t) ⊤ (implA t) = OracleSpec.AnswerMeasure.toMeasure t) ∧
      (∀ t, @evalDist _ _ (samplerSpec.Range t) ⊤ (implF t) = answer P q64Round t) ∧
      (∀ t, implI (.inl t) = implA t) ∧
      (∀ c x, @evalDist _ _ _ ⊤ (implI (.inr c)) {x} = K.gaussianQ0 P c {x}) := by
  let := latticeAnswerMeasure P K hq hN hr hs
  let implA : QueryImpl aux (OracleComp (witnessSpec aux n)) := fun t =>
    liftM (OracleSpec.query (spec := witnessSpec aux n) (.inl (.inl t)))
  refine ⟨implA, fun
    | .perturb => liftM (OracleSpec.query (spec := witnessSpec aux n)
        (.inl (.inr ⟨(Lemma5.stdDev (P.L * P.r), 0),
          Lemma5.stdDev_pos (mul_pos (by exact_mod_cast hL) hr)⟩)))
    | .online c => liftM (OracleSpec.query (spec := witnessSpec aux n)
        (.inl (.inr ⟨(Lemma5.stdDev P.r, q64Round c), Lemma5.stdDev_pos hr⟩))),
    fun
    | .inl t => implA t
    | .inr c => liftM (OracleSpec.query (spec := witnessSpec aux n) (.inr c)),
    fun t => (evalDist_liftM_query _).trans (@MeasureTheory.trim_eq_self _ ⊤ _),
    fun t => ?_, fun _ => rfl, fun c x => ?_⟩
  · cases t <;> exact (evalDist_liftM_query _).trans (@MeasureTheory.trim_eq_self _ ⊤ _)
  · change @evalDist _ _ _ ⊤ (liftM (OracleSpec.query (spec := witnessSpec aux n) (.inr c))) {x} = _
    rw [evalDist_liftM_query_apply _ MeasurableSpace.measurableSet_top]
    exact @Measure.map_apply _ _ _ ⊤ _ _ (fun _ _ => (Set.to_countable _).measurableSet) _
      MeasurableSpace.measurableSet_top

end Mitaka
