/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import Mitaka.Lemma4
public import Mitaka.ScaleChange
public import Mitaka.Witness

/-! # Theorem 1 of [ZKLY26]: correctness of Algorithm 3

[ZKLY26] (ePrint 2026/2521), Theorem 1 (p. 7, l. 223-229): "Let `0 < ϵ ≤ 1/2` and `a > 1`.
Suppose that the following conditions hold: 1. `q/α² ≤ |f(ζ)|² + |g(ζ)|² ≤ α²q` for every primitive
`2n`-th root of unity `ζ`, with `α ≥ 1`; 2. `s > β(p_u)`; 3. `r ≥ η_ϵ(ℤⁿ)` and
`L ≥ (β(p_u)s√(1 + τ̄)/(qr)) η_ϵ(ℤ^{2n})`; 4. `(2a − 1)τ̄ < 1` and
`rs √((1 − √(ϵ/2))(1 − τ̄)/(1 + (2a − 1)τ̄)) ≥ η_ϵ(L(B))`. Then `log R_a(𝒫‖𝒬₀) ≤ ℰ_a`", with
(p. 6, l. 220-222) `𝒬₀ = D_{L(B),rs,c}`, `κ = (1 + ϵ)/(1 − ϵ)` and
`ℰ_a = (9a/4)(log κ)² + 3an² sin²(π/(2n)) τ̄²/((3 + √5)(1 + τ̄)(1 − (2a − 1)τ̄))
+ 5aτ̄²/(1 − (2a − 1)τ̄)²` (`renyiBound`).

Proof (p. 7, l. 238-259): the weak triangle inequality at `p = (2a − 1)/a`
(`RenyiTriangle.renyiDiv_le_rpow_mul_renyiDiv_two_mul`), Lemma 4 at order `2a − 1`
(`Key.renyiDiv_sample_gaussianQe_le`), and the scale change at order `2a`
(`Key.renyiDiv_gaussianQe_le_tauBar`, with Lemma 3).

`𝒫` is the law of `Mitaka.sample` in the perfect-sampler world (`implE` answers with
`answer P id`; `Mitaka.worlds_exist` shows such worlds exist). Beyond the paper's conditions the
statement assumes what the paper takes from its setting: `n = 2^ℓ` (p. 3, l. 116), `0 < q`, the
NTRU equation `fG − gF = q` (p. 4, l. 136), the Gram–Schmidt coefficient `u` of `B` (p. 4,
l. 139-141), and the key-expansion facts that Lemmas 2-3 use, `‖u − û‖∞ ≤ 1/(2p_u)` and a
lower-triangular root `A` of `Σ_p` with every coefficient of `A − Â` at most `1/(2p_A)`
(p. 18, l. 567, 578). Condition 1 is `Key.Annular` (the paper's wording implies it,
`Key.Annular.of_isPrimitiveRoot`); `η_ϵ` is `smoothingParam`, always used with `0 < ϵ` and an
invertible basis (`det_basisMat_ne_zero`).

* `Key.renyiDiv_sample_gaussianQ0_le`: Theorem 1.
* `Key.renyiDiv_sample_gaussianQ0_le_of_sqrt_log`: the three `η_ϵ` of conditions 3-4 replaced by
  their bounds `√(ln(2n(1 + 1/ϵ))/π)`, `√(ln(4n(1 + 1/ϵ))/π)` (`smoothingParam_one_le`) and
  `α√q √(ln(4n(1 + 1/ϵ))/π)` (`Key.smoothingParam_basisMat_le`), so only real inequalities remain.
* `Key.renyiDiv_sample_fp_gaussianQ0_le`: with the fixed-point step of `Mitaka.Sampler`
  (`renyiDiv_sample_le_of_renyiDiv_le`), the fixed-point sampler against `𝒬₀`.
* `witness_theorem1`: at `n = 1` the hypotheses of Theorem 1 hold together;
  `Key.renyiDiv_sample_gaussianQ0_le_witness`: Theorem 1 applied to them and a world. -/

@[expose] public section

open Real MeasureTheory InformationTheory OracleSpec OracleComp LatticeCrypto
  Mitaka.LatticeGaussian
open scoped Matrix MatrixOrder ENNReal

namespace Mitaka

variable {n : ℕ}

/-- `ℰ_a` [ZKLY26, p. 6, l. 222]. -/
noncomputable def renyiBound (P : Params) (n : ℕ) (ϵ a : ℝ) : ℝ :=
  9 * a / 4 * Real.log (kappa ϵ) ^ 2 +
    3 * a * n ^ 2 * Real.sin (π / (2 * n)) ^ 2 * tauBar P n ^ 2 /
      ((3 + √5) * (1 + tauBar P n) * (1 - (2 * a - 1) * tauBar P n)) +
    5 * a * tauBar P n ^ 2 / (1 - (2 * a - 1) * tauBar P n) ^ 2

namespace Key

variable {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m]

/-- **Theorem 1** [ZKLY26, p. 7, l. 223-229]: for `0 < ϵ ≤ 1/2`, `a > 1` and conditions 1-4
(`hK`, `hs`, `h3r` and `h3L`, `h4a` and `h4η`), `log R_a(𝒫‖𝒬₀) ≤ ℰ_a` (`renyiBound`), with `𝒫`
the law of `sample` in the world `implE`. Assumed, not proved: `Key.GSCoeff u` (the Gram–Schmidt
coefficient of `B`), the key-expansion facts `Key.UClose`, `Key.CholeskyRoot`, `Key.AClose`
(`hu`, `hr`, `hC`, `hAc`, as in Lemmas 2-3) and perfect integer samplers (`hE`; such worlds
exist, `worlds_exist`). -/
theorem renyiDiv_sample_gaussianQ0_le {ℓ : ℕ} (hn : n = 2 ^ ℓ) (P : Params) (K : Key n)
    (u : Fin n → ℝ) (A : Fin 2 → Fin 2 → Fin n → ℝ) (hq : 0 < P.q) (hK : K.Annular P)
    (hN : K.NTRU P) (hu : K.GSCoeff u) (hr : K.UClose P u) (hC : K.CholeskyRoot P A)
    (hAc : K.AClose P A) {ϵ a : ℝ} (hϵ₀ : 0 < ϵ) (hϵ : ϵ ≤ 1 / 2) (ha : 1 < a)
    (hs : beta P n < P.s)
    (h3r : smoothingParam ϵ (1 : Matrix (Fin n) (Fin n) ℝ) ≤ P.r)
    (h3L : beta P n * P.s * √(1 + tauBar P n) / (P.q * P.r) *
      smoothingParam ϵ (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ) ≤ P.L)
    (h4a : (2 * a - 1) * tauBar P n < 1)
    (h4η : smoothingParam ϵ K.basisMat ≤
      P.r * P.s * √((1 - √(ϵ / 2)) * (1 - tauBar P n) / (1 + (2 * a - 1) * tauBar P n)))
    (c : Fin 2 → Fin n → ℝ) (implE : QueryImpl samplerSpec m)
    (hE : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implE t) = answer P id t) :
    renyiDiv a 𝒟[simulateQ implE (sample P K c)] (K.gaussianQ0 P c) ≤
      ENNReal.ofReal (Real.exp (renyiBound P n ϵ a)) := by
  obtain ⟨hr0, hL0⟩ := r_pos_and_L_pos hn P K hq hK hs hϵ₀ h3r h3L
  have hs0 : 0 < P.s := (beta_pos P n hK.one_le_alpha hq).trans hs
  have := isProbabilityMeasure_evalDist_sample P K c id hr0 hL0 implE hE
  have := isProbabilityMeasure_gaussianQe P K hq hN hr0 c
  have := isProbabilityMeasure_gaussianQ0 P K hq hN hr0 hs0 c
  have h1 := renyiDiv_sample_gaussianQe_le hn P K u A hq hK hN hu hr hC hAc hs hϵ₀ (by linarith)
    h3r h3L c implE hE (v := 2 * a - 1) (by linarith)
  have h2 := renyiDiv_gaussianQe_le_tauBar hn P K u A hq hK hN hu hr hC hAc hs hϵ₀ hϵ ha h4a h4η c
  have hw : 0 ≤ 2 * a / (2 * a - 1) := div_nonneg (by linarith) (by linarith)
  refine (RenyiTriangle.renyiDiv_le_rpow_mul_renyiDiv_two_mul ha _ _ _).trans
    ((mul_le_mul' (ENNReal.rpow_le_rpow h1 hw) h2).trans (le_of_eq ?_))
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hw, ← Real.exp_mul,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, renyiBound]
  have hb : 2 * a - 1 ≠ 0 := by linarith
  congr 2
  field_simp
  ring

/-- **Theorem 1 with the smoothing parameters bounded**: conditions 3-4 with `η_ϵ(ℤⁿ)`,
`η_ϵ(ℤ^{2n})` and `η_ϵ(L(B))` replaced by `√(ln(2n(1 + 1/ϵ))/π)`, `√(ln(4n(1 + 1/ϵ))/π)` and
`α√q √(ln(4n(1 + 1/ϵ))/π)` (sufficient, not the paper's conditions). Assumed, as in Theorem 1:
`Key.GSCoeff u` (the Gram–Schmidt coefficient of `B`), the key-expansion facts `Key.UClose`,
`Key.CholeskyRoot`, `Key.AClose` and perfect integer samplers (`hE`). -/
theorem renyiDiv_sample_gaussianQ0_le_of_sqrt_log {ℓ : ℕ} (hn : n = 2 ^ ℓ) (P : Params)
    (K : Key n) (u : Fin n → ℝ) (A : Fin 2 → Fin 2 → Fin n → ℝ) (hq : 0 < P.q)
    (hK : K.Annular P) (hN : K.NTRU P) (hu : K.GSCoeff u) (hr : K.UClose P u)
    (hC : K.CholeskyRoot P A) (hAc : K.AClose P A) {ϵ a : ℝ} (hϵ₀ : 0 < ϵ) (hϵ : ϵ ≤ 1 / 2)
    (ha : 1 < a) (hs : beta P n < P.s)
    (h3r : √(Real.log (2 * n * (1 + 1 / ϵ)) / π) ≤ P.r)
    (h3L : beta P n * P.s * √(1 + tauBar P n) / (P.q * P.r) *
      √(Real.log (4 * n * (1 + 1 / ϵ)) / π) ≤ P.L)
    (h4a : (2 * a - 1) * tauBar P n < 1)
    (h4η : P.alpha * √(P.q : ℝ) * √(Real.log (4 * n * (1 + 1 / ϵ)) / π) ≤
      P.r * P.s * √((1 - √(ϵ / 2)) * (1 - tauBar P n) / (1 + (2 * a - 1) * tauBar P n)))
    (c : Fin 2 → Fin n → ℝ) (implE : QueryImpl samplerSpec m)
    (hE : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implE t) = answer P id t) :
    renyiDiv a 𝒟[simulateQ implE (sample P K c)] (K.gaussianQ0 P c) ≤
      ENNReal.ofReal (Real.exp (renyiBound P n ϵ a)) := by
  have hn0 : 0 < n := by
    rw [hn]
    positivity
  have hs0 : 0 < P.s := (beta_pos P n hK.one_le_alpha hq).trans hs
  have hr0 : 0 ≤ P.r := (Real.sqrt_nonneg _).trans h3r
  have hco : 0 ≤ beta P n * P.s * √(1 + tauBar P n) / (P.q * P.r) :=
    div_nonneg (mul_nonneg (mul_nonneg (beta_pos P n hK.one_le_alpha hq).le hs0.le)
      (Real.sqrt_nonneg _)) (mul_nonneg (Nat.cast_nonneg _) hr0)
  have hη2 := smoothingParam_one_le (m := n + n) (by omega) hϵ₀
  rw [show (2 : ℝ) * ((n + n : ℕ) : ℝ) * (1 + 1 / ϵ) = 4 * n * (1 + 1 / ϵ) by push_cast; ring]
    at hη2
  exact renyiDiv_sample_gaussianQ0_le hn P K u A hq hK hN hu hr hC hAc hϵ₀ hϵ ha hs
    ((smoothingParam_one_le hn0 hϵ₀).trans h3r)
    ((mul_le_mul_of_nonneg_left hη2 hco).trans h3L) h4a
    ((Key.smoothingParam_basisMat_le P K u hq hK hN hu hϵ₀).trans h4η) c implE hE

/-- **The fixed-point sampler against `𝒬₀`**: Theorem 1 at order `b = (pa − 1)/(p − 1)` combined
with the fixed-point step (`renyiDiv_sample_le_of_renyiDiv_le`, [ZKLY26, p. 8-9, l. 277-282]):
`log R_a(𝒫_fp‖𝒬₀) ≤ ((a − 1/p)/(a − 1)) · 2n (paπΔ²/r² + pa(pa + 1)Δ²/(2³¹(pa − 1))) + ℰ_b`.
Assumed: `Key.GSCoeff u` (the Gram–Schmidt coefficient of `B`), the key-expansion facts
`Key.UClose`, `Key.CholeskyRoot`, `Key.AClose`, perfect integer samplers (`hE`), the fixed-point
world (`hF`), `|fp x − x| ≤ Δ` (`hfp`) and `1.277 ≤ r/√(2π)` (`hσ`). -/
theorem renyiDiv_sample_fp_gaussianQ0_le {ℓ : ℕ} (hn : n = 2 ^ ℓ) (P : Params) (K : Key n)
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
    (c : Fin 2 → Fin n → ℝ) (fp : ℝ → ℝ) {Δ : ℝ} (hfp : ∀ x, |fp x - x| ≤ Δ)
    (hσ : 1277 / 1000 ≤ Lemma5.stdDev P.r) (implE implF : QueryImpl samplerSpec m)
    (hE : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implE t) = answer P id t)
    (hF : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implF t) = answer P fp t) :
    renyiDiv a 𝒟[simulateQ implF (sample P K c)] (K.gaussianQ0 P c) ≤
      ENNReal.ofReal (Real.exp ((a - 1 / p) / (a - 1) *
          (2 * n * (p * a * π * Δ ^ 2 / P.r ^ 2 +
            p * a * (p * a + 1) * Δ ^ 2 / (2 ^ 31 * (p * a - 1)))) +
        renyiBound P n ϵ ((p * a - 1) / (p - 1)))) := by
  obtain ⟨hr0, hL0⟩ := r_pos_and_L_pos hn P K hq hK hs hϵ₀ h3r h3L
  have hs0 : 0 < P.s := (beta_pos P n hK.one_le_alpha hq).trans hs
  have := isProbabilityMeasure_gaussianQ0 P K hq hN hr0 hs0 c
  have hb : 1 < (p * a - 1) / (p - 1) := by
    rw [lt_div_iff₀ (by linarith)]
    have := mul_lt_mul_of_pos_left ha (by linarith : (0 : ℝ) < p)
    linarith
  exact renyiDiv_sample_le_of_renyiDiv_le P K c fp hfp hσ hL0 ha hp implE implF hE hF
    (K.gaussianQ0 P c) (renyiDiv_sample_gaussianQ0_le hn P K u A hq hK hN hu hr hC hAc hϵ₀ hϵ hb
      hs h3r h3L h4a h4η c implE hE)

end Key

/-- The parameters of the Theorem 1 witness: `Params.witness` with `r = 3`, `L = 2`. -/
noncomputable def Params.witness1 : Params :=
  { Params.witness with r := 3, L := 2 }

/-- **Satisfiability of Theorem 1**: at `n = 1 = 2⁰`, `Params.witness1`, `Key.witness`, `u = 0`,
`witnessA`, `ϵ = 1/2` and `a = 11/10` satisfy every hypothesis of
`Key.renyiDiv_sample_gaussianQ0_le` other than the world hypothesis (`worlds_exist`). -/
theorem witness_theorem1 :
    0 < Params.witness1.q ∧ Key.witness.Annular Params.witness1 ∧
      Key.witness.NTRU Params.witness1 ∧ Key.witness.GSCoeff 0 ∧
      Key.witness.UClose Params.witness1 0 ∧ Key.witness.CholeskyRoot Params.witness1 witnessA ∧
      Key.witness.AClose Params.witness1 witnessA ∧ beta Params.witness1 1 < Params.witness1.s ∧
      smoothingParam (1 / 2) (1 : Matrix (Fin 1) (Fin 1) ℝ) ≤ Params.witness1.r ∧
      beta Params.witness1 1 * Params.witness1.s * √(1 + tauBar Params.witness1 1) /
          (Params.witness1.q * Params.witness1.r) *
        smoothingParam (1 / 2) (1 : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℝ) ≤ Params.witness1.L ∧
      (2 * (11 / 10) - 1) * tauBar Params.witness1 1 < 1 ∧
      smoothingParam (1 / 2) Key.witness.basisMat ≤
        Params.witness1.r * Params.witness1.s *
          √((1 - √((1 / 2) / 2)) * (1 - tauBar Params.witness1 1) /
            (1 + (2 * (11 / 10) - 1) * tauBar Params.witness1 1)) := by
  obtain ⟨hq, hK₀, hN₀, hu, hr₀, hC₀, hAc₀, hs⟩ := witness_hypotheses
  have hK : Key.witness.Annular Params.witness1 :=
    ⟨hK₀.one_le_alpha, hK₀.le_normSq, hK₀.normSq_le⟩
  have hN : Key.witness.NTRU Params.witness1 := ⟨hN₀.eq⟩
  have hr : Key.witness.UClose Params.witness1 0 := ⟨hr₀.abs_sub_le⟩
  have hC : Key.witness.CholeskyRoot Params.witness1 witnessA := ⟨hC₀.lower, hC₀.mul_adjM⟩
  have hAc : Key.witness.AClose Params.witness1 witnessA := ⟨hAc₀.lower, hAc₀.abs_sub_le⟩
  have hcsc : cscN 1 = 1 := by simp [cscN]
  have h5 : √5 ≤ 22361 / 10000 := by
    rw [show (22361 / 10000 : ℝ) = √((22361 / 10000) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  set T := tauBar Params.witness1 1 with hTdef
  have hT0 : 0 ≤ T := tauBar_nonneg _ 1 (by norm_num [Params.witness1, Params.witness])
  have hT1 : T ≤ 6121 / 10000 := by
    have hsq : √(1 - (Params.witness1.q : ℝ) ^ 2 / (Params.witness1.s ^ 2 *
        beta Params.witness1 1 ^ 2)) ≤ 1 :=
      Real.sqrt_le_one.2 (sub_le_self _ (by positivity))
    rw [hTdef, tauBar, hcsc]
    have e : Params.witness1.s = 3 := rfl
    have e2 : ((Params.witness1.pA : ℕ) : ℝ) = 1 := by norm_num [Params.witness1, Params.witness]
    rw [e, e2] at *
    have h6 : (1 + √5) * 1 / (2 * 3 * 1) * √(1 - (Params.witness1.q : ℝ) ^ 2 / (3 ^ 2 *
        beta Params.witness1 1 ^ 2)) ≤ (1 + √5) * 1 / (2 * 3 * 1) :=
      mul_le_of_le_one_right (by positivity) hsq
    have h7 : (3 + √5) * 1 ^ 2 / (8 * 3 ^ 2 * 1 ^ 2) ≤ (3 + 22361 / 10000) / 72 := by
      norm_num
      linarith
    have h8 : (1 + √5) * 1 / (2 * 3 * 1) ≤ (1 + 22361 / 10000) / 6 := by
      norm_num
      linarith
    linarith
  have hlog : Real.log 12 ≤ 3 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he := Real.exp_one_gt_d9
    have e : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [e]
    have h27 : (27 / 10 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
    linarith [show (12 : ℝ) ≤ (27 / 10) ^ 3 by norm_num]
  have hpi := Real.pi_gt_three
  have hη : √(Real.log 12 / π) ≤ 1 :=
    Real.sqrt_le_one.2 ((div_le_one Real.pi_pos).2 (by linarith))
  have hη6 : √(Real.log 6 / π) ≤ 1 :=
    (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right
      (Real.log_le_log (by norm_num) (by norm_num)) Real.pi_pos.le)).trans hη
  have e1 := smoothingParam_one_le (m := 1) one_pos (ϵ := 1 / 2) (by norm_num)
  have e2 := smoothingParam_one_le (m := 1 + 1) (by norm_num) (ϵ := 1 / 2) (by norm_num)
  have e4 := Key.smoothingParam_basisMat_le Params.witness1 Key.witness 0 hq hK hN hu
    (ϵ := 1 / 2) (by norm_num)
  norm_num at e1 e2 e4
  have hα : Params.witness1.alpha * √(Params.witness1.q : ℝ) = 2 := by
    change √2 * √((2 : ℕ) : ℝ) = 2
    rw [Nat.cast_ofNat, Real.mul_self_sqrt (by norm_num)]
  have hη2 : 0 ≤ smoothingParam (1 / 2) (1 : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℝ) :=
    Real.sInf_nonneg fun x hx => hx.1.le
  refine ⟨hq, hK, hN, hu, hr, hC, hAc, hs, ?_, ?_, by linarith, ?_⟩
  · refine e1.trans (hη6.trans ?_)
    change (1 : ℝ) ≤ 3
    norm_num
  · have hβ : beta Params.witness1 1 < 3 := hs
    have hβ0 : 0 < beta Params.witness1 1 := beta_pos _ 1 hK.one_le_alpha hq
    have hsqT : √(1 + T) ≤ 127 / 100 :=
      (Real.sqrt_le_sqrt (by linarith : 1 + T ≤ (127 / 100) ^ 2)).trans_eq
        (Real.sqrt_sq (by norm_num))
    change beta Params.witness1 1 * 3 * √(1 + T) / ((2 : ℕ) * 3) *
      smoothingParam (1 / 2) (1 : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℝ) ≤ ((2 : ℕ) : ℝ)
    have hA : beta Params.witness1 1 * 3 * √(1 + T) / ((2 : ℕ) * 3) ≤ 3 * 3 * (127 / 100) / 6 := by
      push_cast
      rw [show (2 : ℝ) * 3 = 6 by norm_num, div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 6)]
      exact mul_le_mul (mul_le_mul_of_nonneg_right hβ.le (by norm_num)) hsqT
        (Real.sqrt_nonneg _) (by norm_num)
    have hηle := e2.trans hη
    calc beta Params.witness1 1 * 3 * √(1 + T) / ((2 : ℕ) * 3) *
          smoothingParam (1 / 2) (1 : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℝ)
        ≤ 3 * 3 * (127 / 100) / 6 * 1 :=
          mul_le_mul hA hηle hη2 (by norm_num)
      _ ≤ ((2 : ℕ) : ℝ) := by norm_num
  · have hhalf : √((1 / 2 : ℝ) / 2) = 1 / 2 := by
      rw [show (1 / 2 : ℝ) / 2 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hX : 11 / 100 ≤ (1 - √((1 / 2 : ℝ) / 2)) * (1 - T) /
        (1 + (2 * (11 / 10) - 1) * T) := by
      rw [hhalf, le_div_iff₀ (by linarith)]
      linarith
    have hsX : 33 / 100 ≤ √((1 - √((1 / 2 : ℝ) / 2)) * (1 - T) /
        (1 + (2 * (11 / 10) - 1) * T)) :=
      (Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 33 / 100)).symm.trans_le
        (Real.sqrt_le_sqrt (by linarith))
    have hlhs : smoothingParam (1 / 2) Key.witness.basisMat ≤ 2 := by
      refine e4.trans ?_
      rw [hα]
      linarith
    change smoothingParam (1 / 2) Key.witness.basisMat ≤ 3 * 3 * _
    nlinarith [hsX, hlhs]

/-- **Theorem 1 at the witness**: at `n = 1 = 2⁰`, `Params.witness1`, `Key.witness`, `u = 0`,
`witnessA`, `ϵ = 1/2` and `a = 11/10`, `Key.renyiDiv_sample_gaussianQ0_le` applies with the
hypotheses of `witness_theorem1` and a world with perfect integer samplers from `worlds_exist`:
`log R_{11/10}(𝒫‖𝒬₀) ≤ ℰ_{11/10}` for every centre `c`. -/
theorem Key.renyiDiv_sample_gaussianQ0_le_witness :
    ∃ implE : QueryImpl samplerSpec (OracleComp wspec),
      (∀ t, @evalDist _ _ (samplerSpec.Range t) ⊤ (implE t) = answer Params.witness1 id t) ∧
        ∀ c : Fin 2 → Fin 1 → ℝ,
          renyiDiv (11 / 10) 𝒟[simulateQ implE (sample Params.witness1 Key.witness c)]
              (Key.witness.gaussianQ0 Params.witness1 c) ≤
            ENNReal.ofReal (Real.exp (renyiBound Params.witness1 1 (1 / 2) (11 / 10))) := by
  obtain ⟨hq, hK, hN, hu, hr, hC, hAc, hs, h3r, h3L, h4a, h4η⟩ := witness_theorem1
  obtain ⟨implE, -, hE, -⟩ := worlds_exist Params.witness1 id
    (by norm_num [Params.witness1, Params.witness]) (by norm_num [Params.witness1, Params.witness])
  exact ⟨implE, hE, fun c => Key.renyiDiv_sample_gaussianQ0_le (ℓ := 0) rfl Params.witness1
    Key.witness 0 witnessA hq hK hN hu hr hC hAc (by norm_num) (by norm_num) (by norm_num) hs h3r
    h3L h4a h4η c implE hE⟩

end Mitaka
