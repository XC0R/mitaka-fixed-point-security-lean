/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import Mitaka.Algorithm4
public import Mitaka.Theorem1

/-! # The fixed-point step with the centres of Algorithm 4

[ZKLY26] (ePrint 2026/2521) converts each online centre `c` to `c^fp = k + R2⁻⁶⁴` with `k = ⌊c⌋`
and `R = max{1, ⌊2⁶⁴(c − k)⌋}` (Algorithm 4, p. 12), and claims `|c^fp − c| ≤ 2⁻⁶⁴`
(p. 13, l. 388-391), which "meets the precision requirement of Lemma 5" (l. 392-393).

The rule `Algorithm4.q64Round` is a function of the real centre alone, and its error bound
`Algorithm4.abs_q64Round_sub_le` holds for every real `c`. So the fixed-point world of
`Mitaka.Sampler` with `fp = q64Round` meets the hypothesis `|fp x − x| ≤ Δ` of the fixed-point step
for every `x`, at `Δ = 2⁻⁶⁴`, with no restriction on the centres:

* `renyiDiv_sample_q64Round_le`: the fixed-point step (`renyiDiv_sample_le`) at `Δ = 2⁻⁶⁴`;
* `renyiDiv_sample_world_q64Round_mitaka512`, `renyiDiv_sample_world_q64Round_mitaka1024`: at the
  Table 2 parameters, between the perfect-sampler worlds, with no hypotheses left;
* `Key.renyiDiv_sample_q64Round_gaussianQ0_le`: the fixed-point sampler with Algorithm 4's centres
  against `𝒬₀ = D_{L(B),rs,c}` (Theorem 1 combined with the fixed-point step).

That the 64-bit program of Algorithm 4 computes `q64Round` is `Algorithm4.run_fp` (on `ℤ`, every
input) and `Algorithm4.runBV_fp` (on words, when `h + ⌊ℓ/2^b⌋` is a signed 64-bit integer, in
particular under the §4.3 bounds `Algorithm4.Table4Input`). Not proved here: that the
implementation's exact centre pipeline (§4.3: NTT, CRT, the low and high parts `L_j`, `H₂`, `H′₁`)
yields `(ℓ, h)` with `(2^b h + ℓ)/(q 2^{b+t})` equal to the centre of `Mitaka.sample` and within
those bounds. The bounds hold for the truncated CDT samplers (`T_offline`, `T_online`,
p. 11-12, l. 343-354), not for the perfect samplers of this model. -/

@[expose] public section

open Real MeasureTheory InformationTheory OracleSpec OracleComp LatticeCrypto
  Mitaka.LatticeGaussian Mitaka.Algorithm4
open scoped Matrix MatrixOrder ENNReal

namespace Mitaka

variable {n : ℕ} {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m]

/-- **The fixed-point step with Algorithm 4's centres** ([ZKLY26, p. 8-9, l. 277-282] with
`Δ_c = 2⁻⁶⁴`, p. 13, l. 391): `log R_a(P_fp ‖ P) ≤ 2n (aπ2⁻¹²⁸/r² + a(a+1)2⁻¹²⁸/(2³¹(a−1)))`.
Assumed: perfect integer samplers (`hE`, `hF`) and `1.277 ≤ r/√(2π)` (`hr`). -/
theorem renyiDiv_sample_q64Round_le (P : Params) (K : Key n) (c : Fin 2 → Fin n → ℝ)
    (hr : 1277 / 1000 ≤ Lemma5.stdDev P.r) {a : ℝ} (ha : 1 < a)
    (implE implF : QueryImpl samplerSpec m)
    (hE : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implE t) = answer P id t)
    (hF : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implF t) = answer P q64Round t) :
    renyiDiv a 𝒟[simulateQ implF (sample P K c)] 𝒟[simulateQ implE (sample P K c)] ≤
      ENNReal.ofReal (Real.exp (2 * n * (a * π * (1 / 2 ^ 64) ^ 2 / P.r ^ 2 +
        a * (a + 1) * (1 / 2 ^ 64) ^ 2 / (2 ^ 31 * (a - 1))))) :=
  renyiDiv_sample_le P K c q64Round abs_q64Round_sub_le hr ha implE implF hE hF

/-- The fixed-point step with Algorithm 4's centres at Mitaka-512 (Table 2, `r = 3.305`), between
the worlds with perfect samplers: `log R_a(P_fp ‖ P) ≤ (2πna(a+1)/(a−1)) (2⁻¹²⁸/r²)(1 + 2⁻²⁹)`. -/
theorem renyiDiv_sample_world_q64Round_mitaka512 (K : Key n) (c : Fin 2 → Fin n → ℝ) {a : ℝ}
    (ha : 1 < a) :
    renyiDiv a
        𝒟[simulateQ (world Params.mitaka512 q64Round Params.mitaka512_r_pos
          Params.mitaka512_L_pos) (sample Params.mitaka512 K c)]
        𝒟[simulateQ (world Params.mitaka512 id Params.mitaka512_r_pos Params.mitaka512_L_pos)
          (sample Params.mitaka512 K c)] ≤
      ENNReal.ofReal (Real.exp (2 * π * n * a * (a + 1) / (a - 1) *
        ((1 / 2 ^ 64) ^ 2 / (3305 / 1000) ^ 2) * (1 + 1 / 2 ^ 29))) :=
  renyiDiv_sample_world_mitaka512 K c q64Round abs_q64Round_sub_le ha

/-- The fixed-point step with Algorithm 4's centres at Mitaka-1024 (Table 2, `r = 3.34`), between
the worlds with perfect samplers. -/
theorem renyiDiv_sample_world_q64Round_mitaka1024 (K : Key n) (c : Fin 2 → Fin n → ℝ) {a : ℝ}
    (ha : 1 < a) :
    renyiDiv a
        𝒟[simulateQ (world Params.mitaka1024 q64Round Params.mitaka1024_r_pos
          Params.mitaka1024_L_pos) (sample Params.mitaka1024 K c)]
        𝒟[simulateQ (world Params.mitaka1024 id Params.mitaka1024_r_pos Params.mitaka1024_L_pos)
          (sample Params.mitaka1024 K c)] ≤
      ENNReal.ofReal (Real.exp (2 * π * n * a * (a + 1) / (a - 1) *
        ((1 / 2 ^ 64) ^ 2 / (334 / 100) ^ 2) * (1 + 1 / 2 ^ 29))) :=
  renyiDiv_sample_world_mitaka1024 K c q64Round abs_q64Round_sub_le ha

namespace Key

/-- **The fixed-point sampler with Algorithm 4's centres against `𝒬₀`**:
`Key.renyiDiv_sample_fp_gaussianQ0_le` at `fp = q64Round`, `Δ = 2⁻⁶⁴`.
Assumed: `Key.GSCoeff u`, the key-expansion facts `Key.UClose`, `Key.CholeskyRoot`, `Key.AClose`,
perfect integer samplers (`hE`, `hF`) and `1.277 ≤ r/√(2π)` (`hσ`). -/
theorem renyiDiv_sample_q64Round_gaussianQ0_le {ℓ : ℕ} (hn : n = 2 ^ ℓ) (P : Params) (K : Key n)
    (u : Fin n → ℝ) (A : Fin 2 → Fin 2 → Fin n → ℝ) (hq : 0 < P.q) (hK : K.Annular P)
    (hN : K.NTRU P) (hu : K.GSCoeff u) (hr : K.UClose P u) (hC : K.CholeskyRoot P A)
    (hAc : K.AClose P A) {ϵ a p : ℝ} (hϵ₀ : 0 < ϵ) (hϵ : ϵ ≤ 1 / 2) (ha : 1 < a) (hp : 1 < p)
    (hs : beta P n < P.s)
    (h3r : smoothingParam ϵ (1 : Matrix (Fin n) (Fin n) ℝ) ≤ P.r)
    (h3L : beta P n * P.s * √(1 + tauBar P n) / (P.q * P.r) *
      smoothingParam ϵ (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ) ≤ P.L)
    (h4a : (2 * ((p * a - 1) / (p - 1)) - 1) * tauBar P n < 1)
    (h4η : smoothingParam ϵ K.basisMat ≤
      P.r * P.s * √((1 - √(ϵ / 2)) * (1 - tauBar P n) /
        (1 + (2 * ((p * a - 1) / (p - 1)) - 1) * tauBar P n)))
    (c : Fin 2 → Fin n → ℝ) (hσ : 1277 / 1000 ≤ Lemma5.stdDev P.r)
    (implE implF : QueryImpl samplerSpec m)
    (hE : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implE t) = answer P id t)
    (hF : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implF t) = answer P q64Round t) :
    renyiDiv a 𝒟[simulateQ implF (sample P K c)] (K.gaussianQ0 P c) ≤
      ENNReal.ofReal (Real.exp ((a - 1 / p) / (a - 1) *
          (2 * n * (p * a * π * (1 / 2 ^ 64) ^ 2 / P.r ^ 2 +
            p * a * (p * a + 1) * (1 / 2 ^ 64) ^ 2 / (2 ^ 31 * (p * a - 1)))) +
        renyiBound P n ϵ ((p * a - 1) / (p - 1)))) :=
  renyiDiv_sample_fp_gaussianQ0_le hn P K u A hq hK hN hu hr hC hAc hϵ₀ hϵ ha hp hs h3r h3L h4a
    h4η c q64Round abs_q64Round_sub_le hσ implE implF hE hF

end Key

end Mitaka
