/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import Mitaka.FixedPointCentre

/-! # Certified arithmetic at Table 2 of [ZKLY26]

[ZKLY26] (ePrint 2026/2521), Table 2 (p. 9) fixes, for Mitaka-512 and Mitaka-1024, `λ = 128, 256`,
`n = 512, 1024`, `q = 12289`, `α = 1.15, 1.23`, the smoothing error `ϵ = 2⁻³⁸, 2⁻³⁹·⁵`,
`p_u = 2¹⁶`, `p_A = 2⁴², 2⁴³`, `L = 2`, `s = 127.49, 138` and `r = 3.305, 3.34`
(`Params.mitaka512`, `Params.mitaka1024`, `eps512`, `eps1024`). This file checks, as real-number
theorems with certified bounds (Mathlib's bounds on `π` and `log 2`, `sin x > x − x³/6`,
`sin² x ≤ x²`, `log x ≤ x − 1`, square roots by squaring), that these decimals satisfy conditions
2-4 of Theorem 1 (p. 7, l. 223-229) in the closed form of
`Key.renyiDiv_sample_gaussianQ0_le_of_sqrt_log`, and it bounds `τ̄` (p. 6, l. 219), `ℰ_a` (p. 6,
l. 222) and the fixed-point term of the step at `Δ = 2⁻⁶⁴` (p. 8-9, l. 277-282; p. 13, l. 391).

Condition 4 uses the bound `η_ϵ(L(B)) ≤ α√q √(ln(4n(1 + 1/ϵ))/π)` of
`Key.smoothingParam_basisMat_le` (ours, not the paper's; the paper does not bound `η_ϵ(L(B))`),
and conditions 3-4 use `η_ϵ(ℤᵐ) ≤ √(ln(2m(1 + 1/ϵ))/π)` (`smoothingParam_one_le`). These are
sufficient conditions; the paper does not say which bound on `η_ϵ` it uses.

* Condition 2: `beta_lt_mitaka512`, `beta_lt_mitaka1024`.
* Condition 3: `sqrt_log_le_r_mitaka512`, `sqrt_log_le_r_mitaka1024`, `cond3L_mitaka512`,
  `cond3L_mitaka1024`.
* Condition 4: `cond4a_mitaka512`, `cond4a_mitaka1024`, `cond4_mitaka512`, `cond4_mitaka1024`, for
  every order `a ≤ 2²⁰`.
* `τ̄` and `ℰ_a`: `tauBar_le_mitaka512`, `tauBar_le_mitaka1024`, `renyiBound_le_mitaka512`,
  `renyiBound_le_mitaka1024` (`ℰ_a ≤ a · C` for `1 < a ≤ 2²⁰`).
* The fixed-point term: `fpTerm_le_mitaka512`, `fpTerm_le_mitaka1024` (at order `a`), and
  `holderFpTerm_le_mitaka512`, `holderFpTerm_le_mitaka1024` (as it enters
  `Key.renyiDiv_sample_q64Round_gaussianQ0_le`).
* Instances: `Key.renyiDiv_sample_gaussianQ0_le_mitaka512`, `…_mitaka1024` (Theorem 1) and
  `Key.renyiDiv_sample_q64Round_gaussianQ0_le_mitaka512`, `…_mitaka1024` (the fixed-point sampler
  with Algorithm 4's centres against `𝒬₀`). Their remaining hypotheses are the per-key ones
  (`Key.Annular`, `Key.NTRU`, `Key.GSCoeff`, `Key.UClose`, `Key.CholeskyRoot`, `Key.AClose`) and the
  worlds (perfect integer samplers). The per-key hypotheses are shown jointly satisfiable only at
  `n = 1` (`Mitaka.witness_hypotheses`), not for a key with `n = 512` or `1024`.

Not proved here: the composition over sampler calls and the bit-loss headline (both in
`Mitaka/Headline.lean`); that the implementation's `s`, `r` equal Table 2's decimals. -/

@[expose] public section

open Real MeasureTheory InformationTheory OracleSpec OracleComp LatticeCrypto
  Mitaka.LatticeGaussian Mitaka.Algorithm4
open scoped Matrix MatrixOrder ENNReal

namespace Mitaka

/-- The smoothing error of Mitaka-512, `ϵ = 2⁻³⁸` [ZKLY26, Table 2]. -/
noncomputable def eps512 : ℝ := 1 / 2 ^ 38

/-- The smoothing error of Mitaka-1024, `ϵ = 2⁻³⁹·⁵` [ZKLY26, Table 2]. -/
noncomputable def eps1024 : ℝ := (2 : ℝ) ^ (-(79 / 2 : ℝ))

/-- `2⁻³⁹·⁵ = 1/(2³⁹√2)`. -/
theorem eps1024_eq : eps1024 = 1 / (2 ^ 39 * √2) := by
  rw [eps1024, show (79 / 2 : ℝ) = ((39 : ℕ) : ℝ) + 1 / 2 by norm_num, Real.rpow_neg (by norm_num),
    Real.rpow_add (by norm_num), Real.rpow_natCast, ← Real.sqrt_eq_rpow, one_div]

private theorem eps512_pos : 0 < eps512 := by norm_num [eps512]

private theorem eps1024_pos : 0 < eps1024 := by
  rw [eps1024_eq]
  positivity

private theorem eps1024_le : eps1024 ≤ 1 / 2 ^ 39 := by
  rw [eps1024_eq]
  exact one_div_le_one_div_of_le (by positivity)
    (le_mul_of_one_le_right (by positivity) ((Real.le_sqrt' one_pos).2 (by norm_num)))

private theorem eps1024_sq : eps1024 ^ 2 = 1 / 2 ^ 79 := by
  rw [eps1024_eq, div_pow, mul_pow, Real.sq_sqrt (by norm_num)]
  norm_num

private theorem log_inv_eps512 : Real.log (1 / eps512) = 38 * Real.log 2 := by
  rw [eps512, one_div_one_div, Real.log_pow]
  norm_num

private theorem log_inv_eps1024 : Real.log (1 / eps1024) = 79 / 2 * Real.log 2 := by
  rw [eps1024_eq, one_div_one_div, Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_sqrt (by norm_num)]
  push_cast
  ring

/-- `log(k(1 + 1/ϵ)) ≤ log k + log(1/ϵ) + ϵ`, with both logarithms given as multiples of
`log 2`. -/
private theorem log_mul_one_add_inv_le {k ϵ c d e : ℝ} (hk : 0 < k) (hϵ : 0 < ϵ)
    (hkc : Real.log k = c * Real.log 2) (hϵd : Real.log (1 / ϵ) = d * Real.log 2)
    (he : ϵ ≤ e) : Real.log (k * (1 + 1 / ϵ)) ≤ (c + d) * Real.log 2 + e := by
  have h1 : 0 < 1 / ϵ := one_div_pos.2 hϵ
  rw [show k * (1 + 1 / ϵ) = k * (1 / ϵ) * (1 + ϵ) by field_simp; ring,
    Real.log_mul (mul_pos hk h1).ne' (by linarith), Real.log_mul hk.ne' h1.ne']
  linarith [Real.log_le_sub_one_of_pos (show 0 < 1 + ϵ by linarith)]

private theorem log_two_mul_pow (j : ℕ) {k : ℝ} (hk : k = 2 ^ j) :
    Real.log k = j * Real.log 2 := by
  rw [hk, Real.log_pow]

/-- `√(x/π) ≤ w` from `x ≤ 3.141592 w²` (`π > 3.141592`). -/
private theorem sqrt_div_pi_le {x w : ℝ} (hw : 0 ≤ w) (h : x ≤ w ^ 2 * 3.141592) :
    √(x / π) ≤ w := by
  refine (Real.sqrt_le_left hw).2 ?_
  rw [div_le_iff₀ Real.pi_pos]
  linarith [mul_le_mul_of_nonneg_left Real.pi_gt_d6.le (sq_nonneg w)]

/-- `(2a − 1)t ≤ 2²¹T` for `a ≤ 2²⁰`, `0 ≤ t ≤ T`. -/
private theorem two_mul_sub_one_mul_le {a t T : ℝ} (ha : a ≤ 2 ^ 20) (ht : 0 ≤ t) (hT : t ≤ T) :
    (2 * a - 1) * t ≤ 2 ^ 21 * T :=
  (mul_le_mul_of_nonneg_right (by linarith) ht).trans (mul_le_mul_of_nonneg_left hT (by norm_num))

/-! ### `csc(π/(2n))` -/

/-- `csc(π/(2n)) ≤ C` from `sin x > x − x³/6` and `3.141592 < π < 3.141593`. -/
private theorem cscN_le_of {n : ℕ} {C : ℝ} (hn : 0 < n) (hC : 0 ≤ C)
    (h0 : 0 < (3.141592 : ℝ) / (2 * n) - ((3.141593 : ℝ) / (2 * n)) ^ 3 / 6)
    (h : 1 ≤ C * ((3.141592 : ℝ) / (2 * n) - ((3.141593 : ℝ) / (2 * n)) ^ 3 / 6)) :
    cscN n ≤ C := by
  have h2n : (0 : ℝ) < 2 * n := mul_pos two_pos (Nat.cast_pos.2 hn)
  have hx : 0 < π / (2 * n) := div_pos Real.pi_pos h2n
  have hlo : 3.141592 / (2 * n) < π / (2 * n) := (div_lt_div_iff_of_pos_right h2n).2 Real.pi_gt_d6
  have hhi : (π / (2 * n)) ^ 3 < (3.141593 / (2 * n)) ^ 3 :=
    pow_lt_pow_left₀ ((div_lt_div_iff_of_pos_right h2n).2 Real.pi_lt_d6) hx.le (by norm_num)
  have hs : 3.141592 / (2 * n) - (3.141593 / (2 * n)) ^ 3 / 6 < Real.sin (π / (2 * n)) := by
    linarith [Real.sin_gt_sub_cube hx]
  rw [cscN, div_le_iff₀ (h0.trans hs)]
  exact h.trans (mul_le_mul_of_nonneg_left hs.le hC)

/-- `csc(π/1024) ≤ 325.95` (`csc(π/1024) = 325.9498…`). -/
theorem cscN_512_le : cscN 512 ≤ 32595 / 100 :=
  cscN_le_of (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `csc(π/2048) ≤ 651.9` (`csc(π/2048) = 651.8989…`). -/
theorem cscN_1024_le : cscN 1024 ≤ 6519 / 10 :=
  cscN_le_of (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ### Condition 2: `s > β(p_u)` -/

/-- `β(p_u) ≤ Q(u₁ + u₂)/2` from `csc(π/(2n)) ≤ c`, `q ≤ Q²` and the two radicands `≤ u₁²`,
`≤ u₂²`. -/
private theorem beta_le_of (P : Params) (n : ℕ) {c Q u₁ u₂ : ℝ} (hc : cscN n ≤ c) (hQ0 : 0 ≤ Q)
    (hQ : (P.q : ℝ) ≤ Q ^ 2) (hu₁ : 0 ≤ u₁) (hu₂ : 0 ≤ u₂)
    (h₁ : (P.alpha + P.alpha⁻¹) ^ 2 + P.alpha ^ 2 * c ^ 2 / (4 * (P.pu : ℝ) ^ 2) ≤ u₁ ^ 2)
    (h₂ : (P.alpha - P.alpha⁻¹) ^ 2 + P.alpha ^ 2 * c ^ 2 / (4 * (P.pu : ℝ) ^ 2) ≤ u₂ ^ 2) :
    beta P n ≤ Q / 2 * (u₁ + u₂) := by
  have hd : P.alpha ^ 2 * cscN n ^ 2 / (4 * (P.pu : ℝ) ^ 2) ≤
      P.alpha ^ 2 * c ^ 2 / (4 * (P.pu : ℝ) ^ 2) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (cscN_nonneg n) hc 2) (sq_nonneg _)) (by positivity)
  unfold beta
  gcongr
  · exact (Real.sqrt_le_left hQ0).2 hQ
  · exact (Real.sqrt_le_left hu₁).2 (by linarith)
  · exact (Real.sqrt_le_left hu₂).2 (by linarith)

/-- **Condition 2 at Mitaka-512**: `β(p_u) < s = 127.49` (`β(p_u) = 127.48504…`). -/
theorem beta_lt_mitaka512 : beta Params.mitaka512 512 < Params.mitaka512.s :=
  (beta_le_of _ _ cscN_512_le (Q := 110855763 / 1000000) (u₁ := 8078269 / 4000000)
    (u₂ := 28044937 / 100000000) (by norm_num) (by norm_num [Params.mitaka512]) (by norm_num)
    (by norm_num) (by norm_num [Params.mitaka512]) (by norm_num [Params.mitaka512])).trans_lt
    (by norm_num [Params.mitaka512])

/-- **Condition 2 at Mitaka-1024**: `β(p_u) < s = 138` (`β(p_u) = 136.3555…`). -/
theorem beta_lt_mitaka1024 : beta Params.mitaka1024 1024 < Params.mitaka1024.s :=
  (beta_le_of _ _ cscN_1024_le (Q := 110855763 / 1000000) (u₁ := 204301729 / 100000000)
    (u₂ := 1668147 / 4000000) (by norm_num) (by norm_num [Params.mitaka1024]) (by norm_num)
    (by norm_num) (by norm_num [Params.mitaka1024]) (by norm_num [Params.mitaka1024])).trans_lt
    (by norm_num [Params.mitaka1024])

/-! ### `τ̄` -/

/-- `τ̄` from `csc(π/(2n)) ≤ c`, `√5 ≤ F` and `1 − q²/s⁴ ≤ v²` (through `β < s`). -/
private theorem tauBar_le_of (P : Params) (n : ℕ) {c F v : ℝ} (hq : 0 < P.q)
    (hα : 1 ≤ P.alpha) (hs : beta P n < P.s) (hpA : 0 < P.pA) (hc : cscN n ≤ c) (hF : √5 ≤ F)
    (hv0 : 0 ≤ v) (hv : 1 - (P.q : ℝ) ^ 2 / P.s ^ 4 ≤ v ^ 2) :
    tauBar P n ≤ (1 + F) * c / (2 * P.s * P.pA) * v +
      (3 + F) * c ^ 2 / (8 * P.s ^ 2 * (P.pA : ℝ) ^ 2) := by
  have hb0 := beta_pos P n hα hq
  have hs0 := hb0.trans hs
  have hc0 := cscN_nonneg n
  have h5 := Real.sqrt_nonneg 5
  have hA : (0 : ℝ) < P.pA := Nat.cast_pos.2 hpA
  have hsb : P.s ^ 2 * beta P n ^ 2 ≤ P.s ^ 4 := by
    linarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0.le hs.le 2) (sq_nonneg P.s)]
  have hsq : √(1 - (P.q : ℝ) ^ 2 / (P.s ^ 2 * beta P n ^ 2)) ≤ v :=
    (Real.sqrt_le_left hv0).2 ((sub_le_sub_left (div_le_div_of_nonneg_left (sq_nonneg _)
      (by positivity) hsb) 1).trans hv)
  unfold tauBar
  refine add_le_add (mul_le_mul (div_le_div_of_nonneg_right
    (mul_le_mul (by linarith) hc hc0 (by linarith)) (by positivity)) hsq (Real.sqrt_nonneg _)
    (div_nonneg (mul_nonneg (by linarith) (hc0.trans hc)) (by positivity)))
    (div_le_div_of_nonneg_right (mul_le_mul (by linarith) (pow_le_pow_left₀ hc0 hc 2)
      (sq_nonneg _) (by linarith)) (by positivity))

/-- `τ̄ ≤ 6.16·10⁻¹³` at Mitaka-512. -/
theorem tauBar_le_mitaka512 : tauBar Params.mitaka512 512 ≤ 616 / 10 ^ 15 :=
  (tauBar_le_of _ _ (F := 559017 / 250000) (v := 654487 / 1000000)
    (by norm_num [Params.mitaka512]) (by norm_num [Params.mitaka512]) beta_lt_mitaka512
    (by norm_num [Params.mitaka512]) cscN_512_le ((Real.sqrt_le_left (by norm_num)).2 (by norm_num))
    (by norm_num) (by norm_num [Params.mitaka512])).trans (by norm_num [Params.mitaka512])

/-- `τ̄ ≤ 6.65·10⁻¹³` at Mitaka-1024. -/
theorem tauBar_le_mitaka1024 : tauBar Params.mitaka1024 1024 ≤ 665 / 10 ^ 15 :=
  (tauBar_le_of _ _ (F := 559017 / 250000) (v := 381967 / 500000)
    (by norm_num [Params.mitaka1024]) (by norm_num [Params.mitaka1024]) beta_lt_mitaka1024
    (by norm_num [Params.mitaka1024]) cscN_1024_le
    ((Real.sqrt_le_left (by norm_num)).2 (by norm_num)) (by norm_num)
    (by norm_num [Params.mitaka1024])).trans (by norm_num [Params.mitaka1024])

/-! ### Condition 3 in closed form -/

private theorem log_2n_512 :
    Real.log (2 * ((512 : ℕ) : ℝ) * (1 + 1 / eps512)) ≤ (10 + 38) * Real.log 2 + 1 / 2 ^ 38 :=
  log_mul_one_add_inv_le (by norm_num) eps512_pos (log_two_mul_pow 10 (by norm_num))
    log_inv_eps512 le_rfl

private theorem log_4n_512 :
    Real.log (4 * ((512 : ℕ) : ℝ) * (1 + 1 / eps512)) ≤ (11 + 38) * Real.log 2 + 1 / 2 ^ 38 :=
  log_mul_one_add_inv_le (by norm_num) eps512_pos (log_two_mul_pow 11 (by norm_num))
    log_inv_eps512 le_rfl

private theorem log_2n_1024 :
    Real.log (2 * ((1024 : ℕ) : ℝ) * (1 + 1 / eps1024)) ≤
      (11 + 79 / 2) * Real.log 2 + 1 / 2 ^ 39 :=
  log_mul_one_add_inv_le (by norm_num) eps1024_pos (log_two_mul_pow 11 (by norm_num))
    log_inv_eps1024 eps1024_le

private theorem log_4n_1024 :
    Real.log (4 * ((1024 : ℕ) : ℝ) * (1 + 1 / eps1024)) ≤
      (12 + 79 / 2) * Real.log 2 + 1 / 2 ^ 39 :=
  log_mul_one_add_inv_le (by norm_num) eps1024_pos (log_two_mul_pow 12 (by norm_num))
    log_inv_eps1024 eps1024_le

/-- **Condition 3, `r ≥ η_ϵ(ℤⁿ)`, at Mitaka-512**, through `√(ln(2n(1 + 1/ϵ))/π) ≤ r`. -/
theorem sqrt_log_le_r_mitaka512 :
    √(Real.log (2 * ((512 : ℕ) : ℝ) * (1 + 1 / eps512)) / π) ≤ Params.mitaka512.r :=
  sqrt_div_pi_le Params.mitaka512_r_pos.le (log_2n_512.trans (by
    norm_num [Params.mitaka512]
    linarith [Real.log_two_lt_d9]))

/-- **Condition 3, `r ≥ η_ϵ(ℤⁿ)`, at Mitaka-1024**, through `√(ln(2n(1 + 1/ϵ))/π) ≤ r`. -/
theorem sqrt_log_le_r_mitaka1024 :
    √(Real.log (2 * ((1024 : ℕ) : ℝ) * (1 + 1 / eps1024)) / π) ≤ Params.mitaka1024.r :=
  sqrt_div_pi_le Params.mitaka1024_r_pos.le (log_2n_1024.trans (by
    norm_num [Params.mitaka1024]
    linarith [Real.log_two_lt_d9]))

/-- Condition 3's bound on `L` from `β < s`, `1 + τ̄ ≤ 1.1²` and `√(ln(4n(1 + 1/ϵ))/π) ≤ w`. -/
private theorem cond3L_of (P : Params) (n : ℕ) {ϵ T w : ℝ} (hq : 0 < P.q) (hα : 1 ≤ P.alpha)
    (hs : beta P n < P.s) (hr : 0 < P.r) (hT : tauBar P n ≤ T) (hT1 : 1 + T ≤ (11 / 10) ^ 2)
    (hw0 : 0 ≤ w) (hw : Real.log (4 * n * (1 + 1 / ϵ)) ≤ w ^ 2 * 3.141592)
    (h : P.s * P.s * (11 / 10) / (P.q * P.r) * w ≤ P.L) :
    beta P n * P.s * √(1 + tauBar P n) / (P.q * P.r) *
      √(Real.log (4 * n * (1 + 1 / ϵ)) / π) ≤ P.L := by
  have hs0 := (beta_pos P n hα hq).trans hs
  have hqr : 0 < (P.q : ℝ) * P.r := mul_pos (Nat.cast_pos.2 hq) hr
  have h1 : √(1 + tauBar P n) ≤ 11 / 10 := (Real.sqrt_le_left (by norm_num)).2 (by linarith)
  have hn1 : beta P n * P.s * √(1 + tauBar P n) ≤ P.s * P.s * (11 / 10) :=
    mul_le_mul (mul_le_mul_of_nonneg_right hs.le hs0.le) h1 (Real.sqrt_nonneg _)
      (mul_nonneg hs0.le hs0.le)
  exact (mul_le_mul (div_le_div_of_nonneg_right hn1 hqr.le) (sqrt_div_pi_le hw0 hw)
    (Real.sqrt_nonneg _) (div_nonneg (by positivity) hqr.le)).trans h

/-- **Condition 3, the bound on `L`, at Mitaka-512**, through
`η_ϵ(ℤ^{2n}) ≤ √(ln(4n(1 + 1/ϵ))/π)`. -/
theorem cond3L_mitaka512 :
    beta Params.mitaka512 512 * Params.mitaka512.s * √(1 + tauBar Params.mitaka512 512) /
        (Params.mitaka512.q * Params.mitaka512.r) *
      √(Real.log (4 * ((512 : ℕ) : ℝ) * (1 + 1 / eps512)) / π) ≤ Params.mitaka512.L :=
  cond3L_of _ _ (by norm_num [Params.mitaka512]) (by norm_num [Params.mitaka512])
    beta_lt_mitaka512 Params.mitaka512_r_pos tauBar_le_mitaka512 (by norm_num)
    (w := 34 / 10) (by norm_num) (log_4n_512.trans (by linarith [Real.log_two_lt_d9]))
    (by norm_num [Params.mitaka512])

/-- **Condition 3, the bound on `L`, at Mitaka-1024**, through
`η_ϵ(ℤ^{2n}) ≤ √(ln(4n(1 + 1/ϵ))/π)`. -/
theorem cond3L_mitaka1024 :
    beta Params.mitaka1024 1024 * Params.mitaka1024.s * √(1 + tauBar Params.mitaka1024 1024) /
        (Params.mitaka1024.q * Params.mitaka1024.r) *
      √(Real.log (4 * ((1024 : ℕ) : ℝ) * (1 + 1 / eps1024)) / π) ≤ Params.mitaka1024.L :=
  cond3L_of _ _ (by norm_num [Params.mitaka1024]) (by norm_num [Params.mitaka1024])
    beta_lt_mitaka1024 Params.mitaka1024_r_pos tauBar_le_mitaka1024 (by norm_num)
    (w := 34 / 10) (by norm_num) (log_4n_1024.trans (by linarith [Real.log_two_lt_d9]))
    (by norm_num [Params.mitaka1024])

/-! ### Condition 4 in closed form, every order `a ≤ 2²⁰` -/

private theorem tauBar_nonneg_mitaka512 : 0 ≤ tauBar Params.mitaka512 512 :=
  tauBar_nonneg _ _ (by norm_num [Params.mitaka512])

private theorem tauBar_nonneg_mitaka1024 : 0 ≤ tauBar Params.mitaka1024 1024 :=
  tauBar_nonneg _ _ (by norm_num [Params.mitaka1024])

/-- **Condition 4, `(2a − 1)τ̄ < 1`, at Mitaka-512**, for `a ≤ 2²⁰`. -/
theorem cond4a_mitaka512 {a : ℝ} (ha : a ≤ 2 ^ 20) :
    (2 * a - 1) * tauBar Params.mitaka512 512 < 1 :=
  (two_mul_sub_one_mul_le ha tauBar_nonneg_mitaka512 tauBar_le_mitaka512).trans_lt (by norm_num)

/-- **Condition 4, `(2a − 1)τ̄ < 1`, at Mitaka-1024**, for `a ≤ 2²⁰`. -/
theorem cond4a_mitaka1024 {a : ℝ} (ha : a ≤ 2 ^ 20) :
    (2 * a - 1) * tauBar Params.mitaka1024 1024 < 1 :=
  (two_mul_sub_one_mul_le ha tauBar_nonneg_mitaka1024 tauBar_le_mitaka1024).trans_lt (by norm_num)

/-- Condition 4's target width from `√q ≤ Q`, `√(ln(4n(1 + 1/ϵ))/π) ≤ w`, `√(ϵ/2) ≤ S`,
`τ̄ ≤ T`, `(2a − 1)τ̄ ≤ U` and `z² ≤ (1 − S − T)/(1 + U)`. -/
private theorem cond4_of (P : Params) (n : ℕ) {ϵ a S T U Q w z : ℝ} (ha : 1 ≤ a)
    (hα : 0 ≤ P.alpha) (hQ0 : 0 ≤ Q) (hQ : (P.q : ℝ) ≤ Q ^ 2) (hw0 : 0 ≤ w)
    (hw : Real.log (4 * n * (1 + 1 / ϵ)) ≤ w ^ 2 * 3.141592) (hS : √(ϵ / 2) ≤ S)
    (ht0 : 0 ≤ tauBar P n) (hT : tauBar P n ≤ T) (hU : (2 * a - 1) * tauBar P n ≤ U)
    (hz0 : 0 < z) (hz : z ^ 2 * (1 + U) ≤ 1 - S - T) (hrs : 0 ≤ P.r * P.s)
    (h : P.alpha * Q * w ≤ P.r * P.s * z) :
    P.alpha * √(P.q : ℝ) * √(Real.log (4 * n * (1 + 1 / ϵ)) / π) ≤
      P.r * P.s * √((1 - √(ϵ / 2)) * (1 - tauBar P n) / (1 + (2 * a - 1) * tauBar P n)) := by
  have hu0 : 0 ≤ (2 * a - 1) * tauBar P n := mul_nonneg (by linarith) ht0
  have hzY : z ≤ √((1 - √(ϵ / 2)) * (1 - tauBar P n) / (1 + (2 * a - 1) * tauBar P n)) := by
    rw [Real.le_sqrt' hz0, le_div_iff₀ (by linarith)]
    linarith [mul_nonneg (Real.sqrt_nonneg (ϵ / 2)) ht0,
      mul_le_mul_of_nonneg_left hU (sq_nonneg z)]
  calc P.alpha * √(P.q : ℝ) * √(Real.log (4 * n * (1 + 1 / ϵ)) / π) ≤ P.alpha * Q * w :=
        mul_le_mul (mul_le_mul_of_nonneg_left ((Real.sqrt_le_left hQ0).2 hQ) hα)
          (sqrt_div_pi_le hw0 hw) (Real.sqrt_nonneg _) (mul_nonneg hα hQ0)
    _ ≤ P.r * P.s * z := h
    _ ≤ _ := mul_le_mul_of_nonneg_left hzY hrs

/-- **Condition 4, the target width, at Mitaka-512**, for `1 ≤ a ≤ 2²⁰`, through
`η_ϵ(L(B)) ≤ α√q √(ln(4n(1 + 1/ϵ))/π)`. -/
theorem cond4_mitaka512 {a : ℝ} (ha : 1 ≤ a) (ha' : a ≤ 2 ^ 20) :
    Params.mitaka512.alpha * √(Params.mitaka512.q : ℝ) *
        √(Real.log (4 * ((512 : ℕ) : ℝ) * (1 + 1 / eps512)) / π) ≤
      Params.mitaka512.r * Params.mitaka512.s *
        √((1 - √(eps512 / 2)) * (1 - tauBar Params.mitaka512 512) /
          (1 + (2 * a - 1) * tauBar Params.mitaka512 512)) :=
  cond4_of _ _ ha (Q := 110855763 / 1000000) (w := 82201 / 25000) (z := 9999 / 10000)
    (by norm_num [Params.mitaka512]) (by norm_num) (by norm_num [Params.mitaka512]) (by norm_num)
    (log_4n_512.trans (by linarith [Real.log_two_lt_d9]))
    ((Real.sqrt_le_left (by norm_num)).2 (by norm_num [eps512] : eps512 / 2 ≤ (1 / 2 ^ 19) ^ 2))
    tauBar_nonneg_mitaka512 tauBar_le_mitaka512
    (two_mul_sub_one_mul_le ha' tauBar_nonneg_mitaka512 tauBar_le_mitaka512) (by norm_num)
    (by norm_num) (by norm_num [Params.mitaka512]) (by norm_num [Params.mitaka512])

/-- **Condition 4, the target width, at Mitaka-1024**, for `1 ≤ a ≤ 2²⁰`, through
`η_ϵ(L(B)) ≤ α√q √(ln(4n(1 + 1/ϵ))/π)`. -/
theorem cond4_mitaka1024 {a : ℝ} (ha : 1 ≤ a) (ha' : a ≤ 2 ^ 20) :
    Params.mitaka1024.alpha * √(Params.mitaka1024.q : ℝ) *
        √(Real.log (4 * ((1024 : ℕ) : ℝ) * (1 + 1 / eps1024)) / π) ≤
      Params.mitaka1024.r * Params.mitaka1024.s *
        √((1 - √(eps1024 / 2)) * (1 - tauBar Params.mitaka1024 1024) /
          (1 + (2 * a - 1) * tauBar Params.mitaka1024 1024)) :=
  cond4_of _ _ ha (Q := 110855763 / 1000000) (w := 337087 / 100000) (z := 9999 / 10000)
    (by norm_num [Params.mitaka1024]) (by norm_num) (by norm_num [Params.mitaka1024])
    (by norm_num) (log_4n_1024.trans (by linarith [Real.log_two_lt_d9]))
    ((Real.sqrt_le_left (by norm_num)).2
      (by linarith [eps1024_le] : eps1024 / 2 ≤ (1 / 2 ^ 20) ^ 2))
    tauBar_nonneg_mitaka1024 tauBar_le_mitaka1024
    (two_mul_sub_one_mul_le ha' tauBar_nonneg_mitaka1024 tauBar_le_mitaka1024) (by norm_num)
    (by norm_num) (by norm_num [Params.mitaka1024]) (by norm_num [Params.mitaka1024])

/-! ### `ℰ_a` -/

/-- `(log κ)² ≤ 4ϵ²/(1 − e₀)²` for `0 < ϵ ≤ e₀ < 1` (`log κ ≤ κ − 1`). -/
private theorem log_kappa_sq_le {ϵ e₀ : ℝ} (hϵ : 0 < ϵ) (he : ϵ ≤ e₀) (he₁ : e₀ < 1) :
    Real.log (kappa ϵ) ^ 2 ≤ 4 * ϵ ^ 2 / (1 - e₀) ^ 2 := by
  have hk := one_le_kappa hϵ.le (he.trans_lt he₁)
  have hk1 : kappa ϵ - 1 = 2 * ϵ / (1 - ϵ) := by
    rw [kappa]
    field_simp [(show (0 : ℝ) < 1 - ϵ by linarith).ne']
    ring
  have hl : Real.log (kappa ϵ) ≤ 2 * ϵ / (1 - e₀) :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (hk1 ▸
      div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith))
  calc Real.log (kappa ϵ) ^ 2 ≤ (2 * ϵ / (1 - e₀)) ^ 2 :=
        pow_le_pow_left₀ (Real.log_nonneg hk) hl 2
    _ = 4 * ϵ ^ 2 / (1 - e₀) ^ 2 := by rw [div_pow]; ring

/-- `n² sin²(π/(2n)) ≤ (3.141593/2)²`. -/
private theorem natCast_sq_mul_sin_sq_le {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ 2 * Real.sin (π / (2 * n)) ^ 2 ≤ (3.141593 / 2) ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  calc (n : ℝ) ^ 2 * Real.sin (π / (2 * n)) ^ 2 ≤ (n : ℝ) ^ 2 * (π / (2 * n)) ^ 2 :=
        mul_le_mul_of_nonneg_left Real.sin_sq_le_sq (sq_nonneg _)
    _ = (π / 2) ^ 2 := by
        field_simp
    _ ≤ (3.141593 / 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith [Real.pi_lt_d6]) 2

/-- `ℰ_a ≤ a(9ϵ²/(1 − e₀)² + 3(3.141593/2)²T²/(5.236(1 − U)) + 5T²/(1 − U)²)` from
`ϵ ≤ e₀`, `τ̄ ≤ T` and `(2a − 1)τ̄ ≤ U < 1`. -/
private theorem renyiBound_le_of (P : Params) (n : ℕ) (hn : 0 < n) {ϵ e₀ a T U : ℝ}
    (hϵ : 0 < ϵ) (he : ϵ ≤ e₀) (he₁ : e₀ < 1) (ha : 1 < a) (ht0 : 0 ≤ tauBar P n)
    (hT : tauBar P n ≤ T) (hU : (2 * a - 1) * tauBar P n ≤ U) (hU1 : U < 1) :
    renyiBound P n ϵ a ≤ a * (9 * ϵ ^ 2 / (1 - e₀) ^ 2 +
      3 * (3.141593 / 2) ^ 2 * T ^ 2 / ((3 + 2.236) * (1 - U)) + 5 * T ^ 2 / (1 - U) ^ 2) := by
  have hT2 : tauBar P n ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ ht0 hT 2
  have h5 : 2.236 ≤ √5 := (Real.le_sqrt' (by norm_num)).2 (by norm_num)
  have h1 : 9 * a / 4 * Real.log (kappa ϵ) ^ 2 ≤ a * (9 * ϵ ^ 2 / (1 - e₀) ^ 2) :=
    (mul_le_mul_of_nonneg_left (log_kappa_sq_le hϵ he he₁) (by linarith)).trans_eq (by ring)
  have h2 : 3 * a * n ^ 2 * Real.sin (π / (2 * n)) ^ 2 * tauBar P n ^ 2 /
        ((3 + √5) * (1 + tauBar P n) * (1 - (2 * a - 1) * tauBar P n)) ≤
      a * (3 * (3.141593 / 2) ^ 2 * T ^ 2 / ((3 + 2.236) * (1 - U))) := by
    rw [show a * (3 * (3.141593 / 2) ^ 2 * T ^ 2 / ((3 + 2.236) * (1 - U))) =
      3 * a * (3.141593 / 2) ^ 2 * T ^ 2 / ((3 + 2.236) * (1 - U)) by ring,
      show 3 * a * n ^ 2 * Real.sin (π / (2 * n)) ^ 2 * tauBar P n ^ 2 =
        3 * a * (n ^ 2 * Real.sin (π / (2 * n)) ^ 2) * tauBar P n ^ 2 by ring]
    exact div_le_div₀ (mul_nonneg (mul_nonneg (by linarith) (by norm_num)) (sq_nonneg T))
      (mul_le_mul (mul_le_mul_of_nonneg_left (natCast_sq_mul_sin_sq_le hn) (by linarith)) hT2
        (sq_nonneg _) (mul_nonneg (by linarith) (by norm_num)))
      (mul_pos (by norm_num) (by linarith))
      (mul_le_mul (by linarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 3 + √5) ht0])
        (by linarith) (by linarith) (by positivity))
  have h3 : 5 * a * tauBar P n ^ 2 / (1 - (2 * a - 1) * tauBar P n) ^ 2 ≤
      a * (5 * T ^ 2 / (1 - U) ^ 2) := by
    rw [show a * (5 * T ^ 2 / (1 - U) ^ 2) = 5 * a * T ^ 2 / (1 - U) ^ 2 by ring]
    exact div_le_div₀ (mul_nonneg (by linarith) (sq_nonneg T))
      (mul_le_mul_of_nonneg_left hT2 (by linarith)) (pow_pos (by linarith) 2)
      (pow_le_pow_left₀ (by linarith) (by linarith) 2)
  rw [renyiBound]
  linarith

/-- **`ℰ_a` at Mitaka-512**: `ℰ_a ≤ a · 1.216·10⁻²²` for `1 < a ≤ 2²⁰`
(`(9/4)(log κ)² = 1.19114·10⁻²²` per unit of `a`; the `τ̄` terms add about `2.4·10⁻²⁴`). -/
theorem renyiBound_le_mitaka512 {a : ℝ} (ha : 1 < a) (ha' : a ≤ 2 ^ 20) :
    renyiBound Params.mitaka512 512 eps512 a ≤ a * (1216 / 10 ^ 25) :=
  (renyiBound_le_of _ _ (by norm_num) eps512_pos le_rfl (by norm_num [eps512]) ha
    tauBar_nonneg_mitaka512 tauBar_le_mitaka512
    (two_mul_sub_one_mul_le ha' tauBar_nonneg_mitaka512 tauBar_le_mitaka512)
    (by norm_num)).trans (mul_le_mul_of_nonneg_left (by norm_num [eps512]) (by linarith))

/-- **`ℰ_a` at Mitaka-1024**: `ℰ_a ≤ a · 1.774·10⁻²³` for `1 < a ≤ 2²⁰`
(`(9/4)(log κ)² = 1.48893·10⁻²³` per unit of `a`; the `τ̄` terms add about `2.8·10⁻²⁴`). -/
theorem renyiBound_le_mitaka1024 {a : ℝ} (ha : 1 < a) (ha' : a ≤ 2 ^ 20) :
    renyiBound Params.mitaka1024 1024 eps1024 a ≤ a * (1774 / 10 ^ 26) :=
  (renyiBound_le_of _ _ (by norm_num) eps1024_pos eps1024_le (by norm_num) ha
    tauBar_nonneg_mitaka1024 tauBar_le_mitaka1024
    (two_mul_sub_one_mul_le ha' tauBar_nonneg_mitaka1024 tauBar_le_mitaka1024)
    (by norm_num)).trans (mul_le_mul_of_nonneg_left (by rw [eps1024_sq]; norm_num) (by linarith))

/-! ### The fixed-point term at `Δ = 2⁻⁶⁴` -/

/-- The fixed-point term is at most `a · 2n(3.141593/r² + 2/2³¹)/2¹²⁸` for `3 ≤ a`. -/
private theorem fpTerm_le_of (n : ℕ) {r a : ℝ} (ha : 3 ≤ a) :
    2 * (n : ℝ) * (a * π * (1 / 2 ^ 64) ^ 2 / r ^ 2 +
      a * (a + 1) * (1 / 2 ^ 64) ^ 2 / (2 ^ 31 * (a - 1))) ≤
      a * (2 * n * (3.141593 / r ^ 2 + 2 / 2 ^ 31) / 2 ^ 128) := by
  have h1 : a * π * (1 / 2 ^ 64) ^ 2 / r ^ 2 ≤ a * 3.141593 * (1 / 2 ^ 64) ^ 2 / r ^ 2 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left Real.pi_lt_d6.le (by linarith)) (by positivity)) (by positivity)
  have h2 : a * (a + 1) * (1 / 2 ^ 64) ^ 2 / (2 ^ 31 * (a - 1)) ≤
      2 * a * (1 / 2 ^ 64) ^ 2 / 2 ^ 31 := by
    rw [div_le_div_iff₀ (mul_pos (by norm_num) (by linarith)) (by norm_num)]
    linarith [mul_le_mul_of_nonneg_left (show a + 1 ≤ 2 * (a - 1) by linarith)
      (show 0 ≤ a by linarith)]
  calc _ ≤ 2 * (n : ℝ) * (a * 3.141593 * (1 / 2 ^ 64) ^ 2 / r ^ 2 +
        2 * a * (1 / 2 ^ 64) ^ 2 / 2 ^ 31) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity)
    _ = _ := by ring

/-- **The fixed-point term at Mitaka-512** (`renyiDiv_sample_q64Round_le` at `n = 512`,
`r = 3.305`), for `3 ≤ a`: `2n(aπΔ²/r² + a(a+1)Δ²/(2³¹(a−1))) ≤ a·2⁻¹¹⁹`, `Δ = 2⁻⁶⁴`. -/
theorem fpTerm_le_mitaka512 {a : ℝ} (ha : 3 ≤ a) :
    2 * ((512 : ℕ) : ℝ) * (a * π * (1 / 2 ^ 64) ^ 2 / Params.mitaka512.r ^ 2 +
      a * (a + 1) * (1 / 2 ^ 64) ^ 2 / (2 ^ 31 * (a - 1))) ≤ a / 2 ^ 119 :=
  (fpTerm_le_of _ ha).trans ((mul_le_mul_of_nonneg_left
    (by norm_num [Params.mitaka512] : _ ≤ (1 : ℝ) / 2 ^ 119) (by linarith)).trans_eq (by ring))

/-- **The fixed-point term at Mitaka-1024** (`n = 1024`, `r = 3.34`), for `3 ≤ a`:
`2n(aπΔ²/r² + a(a+1)Δ²/(2³¹(a−1))) ≤ a·2⁻¹¹⁸`, `Δ = 2⁻⁶⁴`. -/
theorem fpTerm_le_mitaka1024 {a : ℝ} (ha : 3 ≤ a) :
    2 * ((1024 : ℕ) : ℝ) * (a * π * (1 / 2 ^ 64) ^ 2 / Params.mitaka1024.r ^ 2 +
      a * (a + 1) * (1 / 2 ^ 64) ^ 2 / (2 ^ 31 * (a - 1))) ≤ a / 2 ^ 118 :=
  (fpTerm_le_of _ ha).trans ((mul_le_mul_of_nonneg_left
    (by norm_num [Params.mitaka1024] : _ ≤ (1 : ℝ) / 2 ^ 118) (by linarith)).trans_eq (by ring))

/-- `(a − 1/p)/(a − 1) · X ≤ 2B` from `X ≤ B`, for `2 ≤ a`, `2 ≤ p`. -/
private theorem holder_mul_le {a p X B : ℝ} (ha : 2 ≤ a) (hp : 2 ≤ p) (hX : X ≤ B) (hB : 0 ≤ B) :
    (a - 1 / p) / (a - 1) * X ≤ 2 * B := by
  have hp1 : 1 / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp
  have hp0 : 0 ≤ 1 / p := one_div_nonneg.2 (by linarith)
  have hf : (a - 1 / p) / (a - 1) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  exact (mul_le_mul_of_nonneg_left hX (div_nonneg (by linarith) (by linarith))).trans
    (mul_le_mul_of_nonneg_right hf hB)

private theorem mul_bounds {a p : ℝ} (ha : 2 ≤ a) (ha' : a ≤ 2 ^ 19) (hp : 2 ≤ p)
    (hp' : p ≤ 2 ^ 10) : 3 ≤ p * a ∧ p * a ≤ 2 ^ 29 :=
  ⟨by linarith [mul_le_mul hp ha (by norm_num) (by linarith)],
    by linarith [mul_le_mul hp' ha' (by linarith) (by norm_num)]⟩

/-- **The fixed-point term as it enters the combined bound, Mitaka-512**: the first summand of
`Key.renyiDiv_sample_q64Round_gaussianQ0_le` at `n = 512`, `r = 3.305`, `Δ = 2⁻⁶⁴`, is at most
`2⁻⁸⁸` for `2 ≤ a ≤ 2¹⁹`, `2 ≤ p ≤ 2¹⁰`. -/
theorem holderFpTerm_le_mitaka512 {a p : ℝ} (ha : 2 ≤ a) (ha' : a ≤ 2 ^ 19) (hp : 2 ≤ p)
    (hp' : p ≤ 2 ^ 10) :
    (a - 1 / p) / (a - 1) *
        (2 * ((512 : ℕ) : ℝ) * (p * a * π * (1 / 2 ^ 64) ^ 2 / Params.mitaka512.r ^ 2 +
          p * a * (p * a + 1) * (1 / 2 ^ 64) ^ 2 / (2 ^ 31 * (p * a - 1)))) ≤ 1 / 2 ^ 88 := by
  obtain ⟨h3, h29⟩ := mul_bounds ha ha' hp hp'
  have := holder_mul_le ha hp (fpTerm_le_mitaka512 h3) (by linarith)
  linarith

/-- **The fixed-point term as it enters the combined bound, Mitaka-1024**: at `n = 1024`,
`r = 3.34`, `Δ = 2⁻⁶⁴`, at most `2⁻⁸⁸` for `2 ≤ a ≤ 2¹⁹`, `2 ≤ p ≤ 2¹⁰`. -/
theorem holderFpTerm_le_mitaka1024 {a p : ℝ} (ha : 2 ≤ a) (ha' : a ≤ 2 ^ 19) (hp : 2 ≤ p)
    (hp' : p ≤ 2 ^ 10) :
    (a - 1 / p) / (a - 1) *
        (2 * ((1024 : ℕ) : ℝ) * (p * a * π * (1 / 2 ^ 64) ^ 2 / Params.mitaka1024.r ^ 2 +
          p * a * (p * a + 1) * (1 / 2 ^ 64) ^ 2 / (2 ^ 31 * (p * a - 1)))) ≤ 1 / 2 ^ 88 := by
  obtain ⟨h3, h29⟩ := mul_bounds ha ha' hp hp'
  have := holder_mul_le ha hp (fpTerm_le_mitaka1024 h3) (by linarith)
  linarith

/-! ### Instances: only the per-key hypotheses and the worlds remain -/

namespace Key

variable {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m]

/-- Condition 3's `L` bound with `η_ϵ(ℤ^{2n})`, from its closed form
(`smoothingParam_one_le` at `m = n + n`). -/
private theorem cond3L_smoothing_le (P : Params) {n : ℕ} (hn : 0 < n) {ϵ : ℝ} (hϵ : 0 < ϵ)
    (hq : 0 < P.q) (hα : 1 ≤ P.alpha) (hs : beta P n < P.s) (hr : 0 < P.r)
    (h : beta P n * P.s * √(1 + tauBar P n) / (P.q * P.r) *
      √(Real.log (4 * n * (1 + 1 / ϵ)) / π) ≤ P.L) :
    beta P n * P.s * √(1 + tauBar P n) / (P.q * P.r) *
      smoothingParam ϵ (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ) ≤ P.L := by
  have hb0 := beta_pos P n hα hq
  have hη2 := smoothingParam_one_le (m := n + n) (by omega) hϵ
  rw [show (2 : ℝ) * ((n + n : ℕ) : ℝ) * (1 + 1 / ϵ) = 4 * n * (1 + 1 / ϵ) by push_cast; ring]
    at hη2
  exact (mul_le_mul_of_nonneg_left hη2 (div_nonneg (mul_nonneg (mul_nonneg hb0.le
    (hb0.trans hs).le) (Real.sqrt_nonneg _)) (mul_nonneg (Nat.cast_nonneg _) hr.le))).trans h

/-- `1 < (pa − 1)/(p − 1) ≤ 2²⁰` for `2 ≤ a ≤ 2¹⁹`, `2 ≤ p`. -/
private theorem holderOrder_mem {a p : ℝ} (ha : 2 ≤ a) (ha' : a ≤ 2 ^ 19) (hp : 2 ≤ p) :
    1 < (p * a - 1) / (p - 1) ∧ (p * a - 1) / (p - 1) ≤ 2 ^ 20 := by
  have hp0 : (0 : ℝ) ≤ p := by linarith
  refine ⟨(one_lt_div (by linarith)).2 ?_, (div_le_iff₀ (by linarith)).2 ?_⟩
  · linarith [mul_le_mul_of_nonneg_left ha hp0]
  · linarith [mul_le_mul_of_nonneg_left ha' hp0]

/-- **Theorem 1 at Mitaka-512** (Table 2, `ϵ = 2⁻³⁸`), every order `1 < a ≤ 2²⁰`:
`log R_a(𝒫‖𝒬₀) ≤ ℰ_a` (and `ℰ_a ≤ a · 1.216·10⁻²²`, `renyiBound_le_mitaka512`).
Assumed, per key: condition 1 (`Key.Annular`, `α = 1.15`), `fG − gF = q` (`Key.NTRU`), the
Gram–Schmidt coefficient `u` (`Key.GSCoeff`), the key-expansion facts `Key.UClose`,
`Key.CholeskyRoot`, `Key.AClose`; and perfect integer samplers (`hE`). Conditions 2-4 are
discharged by this file. -/
theorem renyiDiv_sample_gaussianQ0_le_mitaka512 (K : Key 512) (u : Fin 512 → ℝ)
    (A : Fin 2 → Fin 2 → Fin 512 → ℝ) (hK : K.Annular Params.mitaka512)
    (hN : K.NTRU Params.mitaka512) (hu : K.GSCoeff u) (hr : K.UClose Params.mitaka512 u)
    (hC : K.CholeskyRoot Params.mitaka512 A) (hAc : K.AClose Params.mitaka512 A) {a : ℝ}
    (ha : 1 < a) (ha' : a ≤ 2 ^ 20) (c : Fin 2 → Fin 512 → ℝ)
    (implE : QueryImpl samplerSpec m)
    (hE : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implE t) = answer Params.mitaka512 id t) :
    renyiDiv a 𝒟[simulateQ implE (sample Params.mitaka512 K c)]
        (K.gaussianQ0 Params.mitaka512 c) ≤
      ENNReal.ofReal (Real.exp (renyiBound Params.mitaka512 512 eps512 a)) :=
  renyiDiv_sample_gaussianQ0_le_of_sqrt_log (ℓ := 9) (by norm_num) _ K u A
    (by norm_num [Params.mitaka512]) hK hN hu hr hC hAc eps512_pos (by norm_num [eps512]) ha
    beta_lt_mitaka512 sqrt_log_le_r_mitaka512 cond3L_mitaka512 (cond4a_mitaka512 ha')
    (cond4_mitaka512 ha.le ha') c implE hE

/-- **Theorem 1 at Mitaka-1024** (Table 2, `ϵ = 2⁻³⁹·⁵`), every order `1 < a ≤ 2²⁰`:
`log R_a(𝒫‖𝒬₀) ≤ ℰ_a` (and `ℰ_a ≤ a · 1.774·10⁻²³`, `renyiBound_le_mitaka1024`).
Assumed, per key: `Key.Annular` (`α = 1.23`), `Key.NTRU`, `Key.GSCoeff`, `Key.UClose`,
`Key.CholeskyRoot`, `Key.AClose`; and perfect integer samplers (`hE`). -/
theorem renyiDiv_sample_gaussianQ0_le_mitaka1024 (K : Key 1024) (u : Fin 1024 → ℝ)
    (A : Fin 2 → Fin 2 → Fin 1024 → ℝ) (hK : K.Annular Params.mitaka1024)
    (hN : K.NTRU Params.mitaka1024) (hu : K.GSCoeff u) (hr : K.UClose Params.mitaka1024 u)
    (hC : K.CholeskyRoot Params.mitaka1024 A) (hAc : K.AClose Params.mitaka1024 A) {a : ℝ}
    (ha : 1 < a) (ha' : a ≤ 2 ^ 20) (c : Fin 2 → Fin 1024 → ℝ)
    (implE : QueryImpl samplerSpec m)
    (hE : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implE t) = answer Params.mitaka1024 id t) :
    renyiDiv a 𝒟[simulateQ implE (sample Params.mitaka1024 K c)]
        (K.gaussianQ0 Params.mitaka1024 c) ≤
      ENNReal.ofReal (Real.exp (renyiBound Params.mitaka1024 1024 eps1024 a)) :=
  renyiDiv_sample_gaussianQ0_le_of_sqrt_log (ℓ := 10) (by norm_num) _ K u A
    (by norm_num [Params.mitaka1024]) hK hN hu hr hC hAc eps1024_pos
    (eps1024_le.trans (by norm_num)) ha beta_lt_mitaka1024 sqrt_log_le_r_mitaka1024
    cond3L_mitaka1024 (cond4a_mitaka1024 ha') (cond4_mitaka1024 ha.le ha') c implE hE

/-- **The fixed-point sampler with Algorithm 4's centres against `𝒬₀`, Mitaka-512**
(`Key.renyiDiv_sample_q64Round_gaussianQ0_le` at Table 2, `ϵ = 2⁻³⁸`, `Δ = 2⁻⁶⁴`), for
`2 ≤ a ≤ 2¹⁹` and Hölder exponent `2 ≤ p ≤ 2¹⁰`:
`log R_a(𝒫_fp‖𝒬₀) ≤ 2⁻⁸⁸ + b · 1.216·10⁻²²` with `b = (pa − 1)/(p − 1)`.
Assumed, per key: `Key.Annular` (`α = 1.15`), `Key.NTRU`, `Key.GSCoeff`, `Key.UClose`,
`Key.CholeskyRoot`, `Key.AClose`; and the worlds: perfect integer samplers (`hE`) and the
fixed-point world with `q64Round` centres (`hF`). -/
theorem renyiDiv_sample_q64Round_gaussianQ0_le_mitaka512 (K : Key 512) (u : Fin 512 → ℝ)
    (A : Fin 2 → Fin 2 → Fin 512 → ℝ) (hK : K.Annular Params.mitaka512)
    (hN : K.NTRU Params.mitaka512) (hu : K.GSCoeff u) (hr : K.UClose Params.mitaka512 u)
    (hC : K.CholeskyRoot Params.mitaka512 A) (hAc : K.AClose Params.mitaka512 A) {a p : ℝ}
    (ha : 2 ≤ a) (ha' : a ≤ 2 ^ 19) (hp : 2 ≤ p) (hp' : p ≤ 2 ^ 10) (c : Fin 2 → Fin 512 → ℝ)
    (implE implF : QueryImpl samplerSpec m)
    (hE : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implE t) = answer Params.mitaka512 id t)
    (hF : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implF t) =
      answer Params.mitaka512 q64Round t) :
    renyiDiv a 𝒟[simulateQ implF (sample Params.mitaka512 K c)]
        (K.gaussianQ0 Params.mitaka512 c) ≤
      ENNReal.ofReal (Real.exp (1 / 2 ^ 88 + (p * a - 1) / (p - 1) * (1216 / 10 ^ 25))) := by
  obtain ⟨hb, hb'⟩ := holderOrder_mem ha ha' hp
  have hq : 0 < Params.mitaka512.q := by norm_num [Params.mitaka512]
  refine (renyiDiv_sample_q64Round_gaussianQ0_le (ℓ := 9) (by norm_num) _ K u A hq hK hN hu hr
    hC hAc eps512_pos (by norm_num [eps512]) (by linarith) (by linarith) beta_lt_mitaka512
    ((smoothingParam_one_le (by norm_num) eps512_pos).trans sqrt_log_le_r_mitaka512)
    (cond3L_smoothing_le _ (by norm_num) eps512_pos hq (by norm_num [Params.mitaka512])
      beta_lt_mitaka512 Params.mitaka512_r_pos cond3L_mitaka512)
    (cond4a_mitaka512 hb')
    ((smoothingParam_basisMat_le _ K u hq hK hN hu eps512_pos).trans (cond4_mitaka512 hb.le hb'))
    c Lemma5.stdDev_mitaka512 implE implF hE hF).trans ?_
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (add_le_add
    (holderFpTerm_le_mitaka512 ha ha' hp hp') (renyiBound_le_mitaka512 hb hb')))

/-- **The fixed-point sampler with Algorithm 4's centres against `𝒬₀`, Mitaka-1024**
(Table 2, `ϵ = 2⁻³⁹·⁵`, `Δ = 2⁻⁶⁴`), for `2 ≤ a ≤ 2¹⁹`, `2 ≤ p ≤ 2¹⁰`:
`log R_a(𝒫_fp‖𝒬₀) ≤ 2⁻⁸⁸ + b · 1.774·10⁻²³` with `b = (pa − 1)/(p − 1)`.
Assumed, per key: `Key.Annular` (`α = 1.23`), `Key.NTRU`, `Key.GSCoeff`, `Key.UClose`,
`Key.CholeskyRoot`, `Key.AClose`; and the worlds (`hE`, `hF`). -/
theorem renyiDiv_sample_q64Round_gaussianQ0_le_mitaka1024 (K : Key 1024) (u : Fin 1024 → ℝ)
    (A : Fin 2 → Fin 2 → Fin 1024 → ℝ) (hK : K.Annular Params.mitaka1024)
    (hN : K.NTRU Params.mitaka1024) (hu : K.GSCoeff u) (hr : K.UClose Params.mitaka1024 u)
    (hC : K.CholeskyRoot Params.mitaka1024 A) (hAc : K.AClose Params.mitaka1024 A) {a p : ℝ}
    (ha : 2 ≤ a) (ha' : a ≤ 2 ^ 19) (hp : 2 ≤ p) (hp' : p ≤ 2 ^ 10)
    (c : Fin 2 → Fin 1024 → ℝ) (implE implF : QueryImpl samplerSpec m)
    (hE : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implE t) = answer Params.mitaka1024 id t)
    (hF : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implF t) =
      answer Params.mitaka1024 q64Round t) :
    renyiDiv a 𝒟[simulateQ implF (sample Params.mitaka1024 K c)]
        (K.gaussianQ0 Params.mitaka1024 c) ≤
      ENNReal.ofReal (Real.exp (1 / 2 ^ 88 + (p * a - 1) / (p - 1) * (1774 / 10 ^ 26))) := by
  obtain ⟨hb, hb'⟩ := holderOrder_mem ha ha' hp
  have hq : 0 < Params.mitaka1024.q := by norm_num [Params.mitaka1024]
  refine (renyiDiv_sample_q64Round_gaussianQ0_le (ℓ := 10) (by norm_num) _ K u A hq hK hN hu hr
    hC hAc eps1024_pos (eps1024_le.trans (by norm_num)) (by linarith) (by linarith)
    beta_lt_mitaka1024
    ((smoothingParam_one_le (by norm_num) eps1024_pos).trans sqrt_log_le_r_mitaka1024)
    (cond3L_smoothing_le _ (by norm_num) eps1024_pos hq (by norm_num [Params.mitaka1024])
      beta_lt_mitaka1024 Params.mitaka1024_r_pos cond3L_mitaka1024)
    (cond4a_mitaka1024 hb')
    ((smoothingParam_basisMat_le _ K u hq hK hN hu eps1024_pos).trans
      (cond4_mitaka1024 hb.le hb'))
    c Lemma5.stdDev_mitaka1024 implE implF hE hF).trans ?_
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (add_le_add
    (holderFpTerm_le_mitaka1024 ha ha' hp hp') (renyiBound_le_mitaka1024 hb hb')))

end Key

end Mitaka
