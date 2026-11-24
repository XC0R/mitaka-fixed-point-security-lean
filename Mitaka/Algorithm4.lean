/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import Mathlib.Data.Int.Bitwise
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! # Algorithm 4 of [ZKLY26]: fixed-point centres from low and high parts

[ZKLY26] (ePrint 2026/2521), Algorithm 4 "Fixed point center computation from low and high parts"
(p. 12, box at l. 368). "Parameters: `q = 12289`, `b ∈ {43, 44}`, and `t ∈ {0, 16}`. Input: Signed
64-bit integers `(ℓ, h)` satisfying the bounds of Section 4.3. Output: `k = ⌊c⌋` and
`R = max{1, ⌊2⁶⁴(c − k)⌋}`, representing `c^fp = k + R2⁻⁶⁴`.
1 `a ← ⌊ℓ/2^b⌋`; `ℓ₀ ← ℓ − 2^b a` 2 `H ← h + a` 3 `v ← ⌊H/2^t⌋`; `h₀ ← H − 2^t v`
4 `k ← trunc(v/q)`; `r ← v − qk` 5 `δ ← [r < 0]`; `k ← k − δ`; `r ← r + qδ`
6 `w ← (2^b h₀ + ℓ₀) 2^{64−b−t}` 7 `u ← r 2³² + ⌊w/2³²⌋` 8 `R_hi ← ⌊u/q⌋`; `r ← u − qR_hi`
9 `u ← r 2³² + (w mod 2³²)` 10 `R_lo ← ⌊u/q⌋` 11 `R ← R_hi 2³² + R_lo`
12 `R ← R OR (R == 0)` // bitwise OR 13 return `(k, R)`", where `c = (2^b h + ℓ)/(q 2^{b+t})`
(p. 12, l. 360). "`[P] ∈ {0, 1}` is the indicator of `P`, and trunc rounds toward zero, as in
signed C division. [...] The divisions by powers of two are floor splits, implemented by shifts and
masks" (p. 12-13, l. 369-372).

* `run`: the algorithm on `ℤ`, line by line, recording every intermediate (`Trace`).
* `run_k`, `run_R`, `run_R_mem`, `run_fp`: the outputs are `⌊c⌋` and `max{1, ⌊2⁶⁴(c − k)⌋}`, with
  `1 ≤ R < 2⁶⁴`, and `k + R2⁻⁶⁴ = q64Round c`, for all integers `ℓ, h` and `b + t ≤ 64`.
* `run_euclid`, `run_invariant`, `run_R₀`, `run_dividends`: the claims of p. 13, l. 369-378.
* `abs_q64Round_sub_le`, `q64Round_sub_cases`, `abs_q64Round_sub_eq_iff`: `|c^fp − c| ≤ 2⁻⁶⁴` for
  every real `c`, the case split of l. 390, and equality exactly at integer centres (l. 391-392).
* `run_inWords`: every intermediate lies in its 64-bit word (l. 378-379), when `ℓ` and
  `h + ⌊ℓ/2^b⌋` are signed 64-bit integers. `Table4Input` is the paper's input condition (§4.3,
  Table 4); `run_inWords_of_table4`, `algorithm4_correct` use it.
* `runBV`: the algorithm on 64-bit words with the operations of l. 369-372 (arithmetic shifts and
  masks, signed `trunc` division, unsigned digit divisions, bitwise `OR`). `runBV_noOverflow`: no
  operation overflows, in the sense of Lean core's `BitVec.saddOverflow`, `smulOverflow`,
  `ssubOverflow`, `sdivOverflow`, `uaddOverflow`, `umulOverflow`, `usubOverflow`;
  `runBV_refines`: the words have the values of `run` (`toInt` for signed, `toNat` for unsigned
  variables); `runBV_fp`: the word program computes `q64Round c`.

The §4.3 bounds themselves (Table 4) are not proved here: they are the hypothesis `Table4Input`. -/

@[expose] public section

namespace Mitaka.Algorithm4

/-- The NTRU modulus `q = 12289` (Algorithm 4, parameters). -/
def q : ℤ := 12289

/-- `x` lies in a signed 64-bit word: `-2⁶³ ≤ x < 2⁶³`. -/
structure Signed64 (x : ℤ) : Prop where
  /-- The lower end. -/
  le : -2 ^ 63 ≤ x
  /-- The upper end. -/
  lt : x < 2 ^ 63

/-- `x` lies in an unsigned 64-bit word: `0 ≤ x < 2⁶⁴`. -/
structure Unsigned64 (x : ℤ) : Prop where
  /-- The lower end. -/
  nonneg : 0 ≤ x
  /-- The upper end. -/
  lt : x < 2 ^ 64

/-- The centre `c = (2^b h + ℓ)/(q 2^{b+t})` (p. 12, l. 360). -/
noncomputable def centre (b t : ℕ) (ℓ h : ℤ) : ℝ := (2 ^ b * h + ℓ) / (q * 2 ^ (b + t))

/-- The output rule of Algorithm 4: `c^fp = k + R 2⁻⁶⁴` with `k = ⌊c⌋` and
`R = max{1, ⌊2⁶⁴(c − k)⌋}` (p. 12, Output). -/
noncomputable def q64Round (c : ℝ) : ℝ :=
  ⌊c⌋ + ((max 1 ⌊2 ^ 64 * (c - ⌊c⌋)⌋ : ℤ) : ℝ) / 2 ^ 64

/-- The values of the variables of Algorithm 4. The paper reassigns `k`, `r`, `u` and `R`; here
`k₀, r₀` are those of line 4, `k, r` of line 5, `u₁, r₁` of lines 7-8, `u₂` of line 9, `R₀` of
line 11 and `R` of line 12. -/
structure Trace where
  /-- Line 1: `a = ⌊ℓ/2^b⌋`. -/
  a : ℤ
  /-- Line 1: `ℓ₀ = ℓ − 2^b a`. -/
  ℓ₀ : ℤ
  /-- Line 2: `H = h + a`. -/
  H : ℤ
  /-- Line 3: `v = ⌊H/2^t⌋`. -/
  v : ℤ
  /-- Line 3: `h₀ = H − 2^t v`. -/
  h₀ : ℤ
  /-- Line 4: `k = trunc(v/q)`. -/
  k₀ : ℤ
  /-- Line 4: `r = v − qk`. -/
  r₀ : ℤ
  /-- Line 5: `δ = [r < 0]`. -/
  δ : ℤ
  /-- Line 5: `k ← k − δ`. -/
  k : ℤ
  /-- Line 5: `r ← r + qδ`. -/
  r : ℤ
  /-- Line 6: `w = (2^b h₀ + ℓ₀) 2^{64−b−t}`. -/
  w : ℤ
  /-- Line 7: `u = r 2³² + ⌊w/2³²⌋`. -/
  u₁ : ℤ
  /-- Line 8: `R_hi = ⌊u/q⌋`. -/
  Rhi : ℤ
  /-- Line 8: `r ← u − qR_hi`. -/
  r₁ : ℤ
  /-- Line 9: `u ← r 2³² + (w mod 2³²)`. -/
  u₂ : ℤ
  /-- Line 10: `R_lo = ⌊u/q⌋`. -/
  Rlo : ℤ
  /-- Line 11: `R = R_hi 2³² + R_lo`. -/
  R₀ : ℤ
  /-- Line 12: `R ← R OR (R == 0)`. -/
  R : ℤ

/-- **Algorithm 4** on `ℤ` (p. 12): `⌊·⌋` is `Int.fdiv`, `trunc` is `Int.tdiv`, `mod` is `Int.emod`,
`OR` is `Int.lor`. -/
def run (b t : ℕ) (ℓ h : ℤ) : Trace :=
  let a := ℓ.fdiv (2 ^ b)
  let ℓ₀ := ℓ - 2 ^ b * a
  let H := h + a
  let v := H.fdiv (2 ^ t)
  let h₀ := H - 2 ^ t * v
  let k₀ := v.tdiv q
  let r₀ := v - q * k₀
  let δ : ℤ := if r₀ < 0 then 1 else 0
  let k := k₀ - δ
  let r := r₀ + q * δ
  let w := (2 ^ b * h₀ + ℓ₀) * 2 ^ (64 - b - t)
  let u₁ := r * 2 ^ 32 + w.fdiv (2 ^ 32)
  let Rhi := u₁.fdiv q
  let r₁ := u₁ - q * Rhi
  let u₂ := r₁ * 2 ^ 32 + w % 2 ^ 32
  let Rlo := u₂.fdiv q
  let R₀ := Rhi * 2 ^ 32 + Rlo
  let R := R₀.lor (if R₀ = 0 then 1 else 0)
  ⟨a, ℓ₀, H, v, h₀, k₀, r₀, δ, k, r, w, u₁, Rhi, r₁, u₂, Rlo, R₀, R⟩

/-! ### Correctness on `ℤ` (p. 12-13, l. 369-393) -/

private theorem q_pos : (0 : ℤ) < q := by norm_num [q]

private theorem fdiv_two_pow (x : ℤ) (k : ℕ) : x.fdiv (2 ^ k) = x / 2 ^ k :=
  Int.fdiv_eq_ediv_of_nonneg x (by positivity)

private theorem run_a (b t : ℕ) (ℓ h : ℤ) : (run b t ℓ h).a = ℓ / 2 ^ b := fdiv_two_pow ℓ b

private theorem run_ℓ₀ (b t : ℕ) (ℓ h : ℤ) : (run b t ℓ h).ℓ₀ = ℓ % 2 ^ b := by
  rw [Int.emod_def, ← run_a b t ℓ h]; rfl

private theorem run_v (b t : ℕ) (ℓ h : ℤ) : (run b t ℓ h).v = (run b t ℓ h).H / 2 ^ t :=
  fdiv_two_pow _ t

private theorem run_h₀ (b t : ℕ) (ℓ h : ℤ) : (run b t ℓ h).h₀ = (run b t ℓ h).H % 2 ^ t := by
  rw [Int.emod_def, ← run_v]; rfl

private theorem run_r₀ (b t : ℕ) (ℓ h : ℤ) : (run b t ℓ h).r₀ = (run b t ℓ h).v.tmod q :=
  (Int.tmod_def _ _).symm

private theorem run_δ (b t : ℕ) (ℓ h : ℤ) : (run b t ℓ h).δ = 0 ∨ (run b t ℓ h).δ = 1 := by
  by_cases hr : (run b t ℓ h).r₀ < 0
  · exact Or.inr (ite_eq_left hr)
  · exact Or.inl (ite_eq_right hr)

private theorem run_u₁ (b t : ℕ) (ℓ h : ℤ) :
    (run b t ℓ h).u₁ = (run b t ℓ h).r * 2 ^ 32 + (run b t ℓ h).w / 2 ^ 32 :=
  congrArg ((run b t ℓ h).r * 2 ^ 32 + ·) (fdiv_two_pow _ 32)

private theorem run_Rhi (b t : ℕ) (ℓ h : ℤ) : (run b t ℓ h).Rhi = (run b t ℓ h).u₁ / q :=
  Int.fdiv_eq_ediv_of_nonneg _ q_pos.le

private theorem run_r₁ (b t : ℕ) (ℓ h : ℤ) : (run b t ℓ h).r₁ = (run b t ℓ h).u₁ % q := by
  rw [Int.emod_def, ← run_Rhi]; rfl

private theorem run_Rlo (b t : ℕ) (ℓ h : ℤ) : (run b t ℓ h).Rlo = (run b t ℓ h).u₂ / q :=
  Int.fdiv_eq_ediv_of_nonneg _ q_pos.le

private theorem run_ℓ₀_mem (b t : ℕ) (ℓ h : ℤ) :
    0 ≤ (run b t ℓ h).ℓ₀ ∧ (run b t ℓ h).ℓ₀ < 2 ^ b := by
  rw [run_ℓ₀]; exact ⟨Int.emod_nonneg _ (by positivity), Int.emod_lt_of_pos _ (by positivity)⟩

private theorem run_h₀_mem (b t : ℕ) (ℓ h : ℤ) :
    0 ≤ (run b t ℓ h).h₀ ∧ (run b t ℓ h).h₀ < 2 ^ t := by
  rw [run_h₀]; exact ⟨Int.emod_nonneg _ (by positivity), Int.emod_lt_of_pos _ (by positivity)⟩

private theorem run_r₀_mem (b t : ℕ) (ℓ h : ℤ) : -q < (run b t ℓ h).r₀ ∧ (run b t ℓ h).r₀ < q := by
  rw [run_r₀]; exact ⟨Int.lt_tmod_of_pos _ q_pos, Int.tmod_lt_of_pos _ q_pos⟩

private theorem run_r₀_sign (b t : ℕ) (ℓ h : ℤ) :
    (0 ≤ (run b t ℓ h).v → 0 ≤ (run b t ℓ h).r₀) ∧
      ((run b t ℓ h).v ≤ 0 → (run b t ℓ h).r₀ ≤ 0) := by
  rw [run_r₀]
  refine ⟨Int.tmod_nonneg q, fun hv => ?_⟩
  have := Int.tmod_nonneg q (neg_nonneg.2 hv)
  rw [Int.neg_tmod] at this
  linarith

private theorem run_r₁_mem (b t : ℕ) (ℓ h : ℤ) : 0 ≤ (run b t ℓ h).r₁ ∧ (run b t ℓ h).r₁ < q := by
  rw [run_r₁]; exact ⟨Int.emod_nonneg _ q_pos.ne', Int.emod_lt_of_pos _ q_pos⟩

/-- "The correction by `δ` converts this quotient and remainder into Euclidean division, including
for negative inputs" (p. 12-13, l. 370-371). -/
theorem run_euclid (b t : ℕ) (ℓ h : ℤ) :
    (run b t ℓ h).k = (run b t ℓ h).v / q ∧ (run b t ℓ h).r = (run b t ℓ h).v % q := by
  obtain ⟨h₁, h₂⟩ := run_r₀_mem b t ℓ h
  have e₀ : (run b t ℓ h).r₀ = (run b t ℓ h).v - q * (run b t ℓ h).k₀ := rfl
  have ek : (run b t ℓ h).k = (run b t ℓ h).k₀ - (run b t ℓ h).δ := rfl
  have er : (run b t ℓ h).r = (run b t ℓ h).r₀ + q * (run b t ℓ h).δ := rfl
  have eδ : (run b t ℓ h).δ = if (run b t ℓ h).r₀ < 0 then 1 else 0 := rfl
  have key : (run b t ℓ h).r + q * (run b t ℓ h).k = (run b t ℓ h).v ∧
      0 ≤ (run b t ℓ h).r ∧ (run b t ℓ h).r < q := by
    rw [er, ek, eδ]
    split_ifs <;> exact ⟨by linear_combination e₀, by linarith, by linarith⟩
  have := (Int.ediv_emod_unique q_pos).2 key
  exact ⟨this.1.symm, this.2.symm⟩

private theorem run_r_mem (b t : ℕ) (ℓ h : ℤ) : 0 ≤ (run b t ℓ h).r ∧ (run b t ℓ h).r < q := by
  rw [(run_euclid b t ℓ h).2]; exact ⟨Int.emod_nonneg _ q_pos.ne', Int.emod_lt_of_pos _ q_pos⟩

private theorem run_X_mem (b t : ℕ) (ℓ h : ℤ) :
    0 ≤ 2 ^ b * (run b t ℓ h).h₀ + (run b t ℓ h).ℓ₀ ∧
      2 ^ b * (run b t ℓ h).h₀ + (run b t ℓ h).ℓ₀ < 2 ^ b * 2 ^ t := by
  obtain ⟨h₁, h₂⟩ := run_ℓ₀_mem b t ℓ h
  obtain ⟨h₃, h₄⟩ := run_h₀_mem b t ℓ h
  have hB : (0 : ℤ) < 2 ^ b := by positivity
  have := mul_le_mul_of_nonneg_left (Int.le_sub_one_of_lt h₄) hB.le
  exact ⟨add_nonneg (mul_nonneg hB.le h₃) h₁, by linarith [mul_sub_one ((2 : ℤ) ^ b) (2 ^ t)]⟩

private theorem two_pow_64 {R : Type*} [Monoid R] [OfNat R 2] {b t : ℕ} (hbt : b + t ≤ 64) :
    (2 : R) ^ 64 = 2 ^ b * 2 ^ t * 2 ^ (64 - b - t) := by
  rw [← pow_add, ← pow_add]; congr 1; omega

private theorem run_w_mem {b t : ℕ} (hbt : b + t ≤ 64) (ℓ h : ℤ) : Unsigned64 (run b t ℓ h).w := by
  obtain ⟨h₁, h₂⟩ := run_X_mem b t ℓ h
  have hE : (0 : ℤ) < 2 ^ (64 - b - t) := by positivity
  refine ⟨mul_nonneg h₁ hE.le, ?_⟩
  rw [two_pow_64 hbt]
  exact mul_lt_mul_of_pos_right h₂ hE

private theorem run_identity (b t : ℕ) (ℓ h : ℤ) :
    (2 ^ b * h + ℓ) * 2 ^ (64 - b - t) =
      q * (2 ^ b * 2 ^ t * 2 ^ (64 - b - t)) * (run b t ℓ h).k +
        ((run b t ℓ h).r * (2 ^ b * 2 ^ t * 2 ^ (64 - b - t)) + (run b t ℓ h).w) := by
  have e₁ : (run b t ℓ h).ℓ₀ = ℓ - 2 ^ b * (run b t ℓ h).a := rfl
  have e₂ : (run b t ℓ h).H = h + (run b t ℓ h).a := rfl
  have e₃ : (run b t ℓ h).h₀ = (run b t ℓ h).H - 2 ^ t * (run b t ℓ h).v := rfl
  have e₄ := ((Int.ediv_emod_unique q_pos).1
    ⟨(run_euclid b t ℓ h).1.symm, (run_euclid b t ℓ h).2.symm⟩).1
  have e₅ : (run b t ℓ h).w =
    (2 ^ b * (run b t ℓ h).h₀ + (run b t ℓ h).ℓ₀) * 2 ^ (64 - b - t) := rfl
  linear_combination (-2 ^ (64 - b - t) : ℤ) * e₁ - 2 ^ b * 2 ^ (64 - b - t) * e₂ -
    2 ^ b * 2 ^ (64 - b - t) * e₃ - 2 ^ b * 2 ^ t * 2 ^ (64 - b - t) * e₄ - e₅

/-- "Immediately before the two 32-bit quotient digits are extracted, `0 ≤ r < q`, `0 ≤ w < 2⁶⁴`,
and `c = k + (r 2⁶⁴ + w)/(q 2⁶⁴)`" (p. 13, l. 373-375), for `b + t ≤ 64`. -/
theorem run_invariant {b t : ℕ} (hbt : b + t ≤ 64) (ℓ h : ℤ) :
    0 ≤ (run b t ℓ h).r ∧ (run b t ℓ h).r < q ∧ Unsigned64 (run b t ℓ h).w ∧
      centre b t ℓ h = (run b t ℓ h).k +
        ((run b t ℓ h).r * 2 ^ 64 + (run b t ℓ h).w) / (q * 2 ^ 64) := by
  obtain ⟨hr₀, hr₁⟩ := run_r_mem b t ℓ h
  refine ⟨hr₀, hr₁, run_w_mem hbt ℓ h, ?_⟩
  have hR : ((2 : ℝ) ^ b * h + ℓ) * 2 ^ (64 - b - t) =
      q * (2 ^ b * 2 ^ t * 2 ^ (64 - b - t)) * (run b t ℓ h).k +
        ((run b t ℓ h).r * (2 ^ b * 2 ^ t * 2 ^ (64 - b - t)) + (run b t ℓ h).w) := by
    exact_mod_cast run_identity b t ℓ h
  have hq : (q : ℝ) ≠ 0 := by norm_num [q]
  have h₁ : (q : ℝ) * (2 ^ b * 2 ^ t) ≠ 0 := mul_ne_zero hq (by positivity)
  have h₂ : (q : ℝ) * (2 ^ b * 2 ^ t * 2 ^ (64 - b - t)) ≠ 0 := mul_ne_zero hq (by positivity)
  rw [centre, two_pow_64 hbt, pow_add, add_div' _ _ _ h₂, div_eq_div_iff h₁ h₂]
  linear_combination ((q : ℝ) * (2 ^ b * 2 ^ t)) * hR

private theorem run_F (b t : ℕ) (ℓ h : ℤ) :
    (run b t ℓ h).r * 2 ^ 64 + (run b t ℓ h).w =
      (run b t ℓ h).u₂ % q + q * (run b t ℓ h).R₀ := by
  have eu₂ := Int.mul_ediv_add_emod (run b t ℓ h).u₂ q
  rw [← run_Rlo] at eu₂
  have ew := Int.mul_ediv_add_emod (run b t ℓ h).w (2 ^ 32)
  have eu₁ := run_u₁ b t ℓ h
  have er₁ : (run b t ℓ h).r₁ = (run b t ℓ h).u₁ - q * (run b t ℓ h).Rhi := rfl
  have eu₂' : (run b t ℓ h).u₂ = (run b t ℓ h).r₁ * 2 ^ 32 + (run b t ℓ h).w % 2 ^ 32 := rfl
  have eR₀ : (run b t ℓ h).R₀ = (run b t ℓ h).Rhi * 2 ^ 32 + (run b t ℓ h).Rlo := rfl
  linear_combination -eu₂ - q * eR₀ - eu₂' - 2 ^ 32 * er₁ - 2 ^ 32 * eu₁ - ew

/-- "The two successive divisions by `q` therefore compute `⌊(r 2⁶⁴ + w)/q⌋` exactly, without
storing the wide dividend" (p. 13, l. 376-377), for all `b, t`. -/
theorem run_R₀ (b t : ℕ) (ℓ h : ℤ) :
    (run b t ℓ h).R₀ = ((run b t ℓ h).r * 2 ^ 64 + (run b t ℓ h).w).fdiv q := by
  rw [Int.fdiv_eq_ediv_of_nonneg _ q_pos.le, run_F, Int.add_mul_ediv_left _ _ q_pos.ne',
    Int.ediv_eq_zero_of_lt (Int.emod_nonneg _ q_pos.ne') (Int.emod_lt_of_pos _ q_pos), zero_add]

/-- "Each temporary dividend `u` is smaller than `q 2³² < 2⁴⁶`, and each quotient digit fits in
32 bits" (p. 13, l. 377-378), for `b + t ≤ 64`. -/
theorem run_dividends {b t : ℕ} (hbt : b + t ≤ 64) (ℓ h : ℤ) :
    (0 ≤ (run b t ℓ h).u₁ ∧ (run b t ℓ h).u₁ < q * 2 ^ 32) ∧
      (0 ≤ (run b t ℓ h).u₂ ∧ (run b t ℓ h).u₂ < q * 2 ^ 32) ∧ q * 2 ^ 32 < 2 ^ 46 ∧
      (0 ≤ (run b t ℓ h).Rhi ∧ (run b t ℓ h).Rhi < 2 ^ 32) ∧
      (0 ≤ (run b t ℓ h).Rlo ∧ (run b t ℓ h).Rlo < 2 ^ 32) := by
  obtain ⟨hr₀, hr₁⟩ := run_r_mem b t ℓ h
  obtain ⟨hw₀, hw₁⟩ := run_w_mem hbt ℓ h
  obtain ⟨hs₀, hs₁⟩ := run_r₁_mem b t ℓ h
  have hq : q = 12289 := rfl
  have h₁ : 0 ≤ (run b t ℓ h).w / 2 ^ 32 := Int.ediv_nonneg hw₀ (by positivity)
  have h₂ : (run b t ℓ h).w / 2 ^ 32 < 2 ^ 32 :=
    Int.ediv_lt_of_lt_mul (by positivity) (by linarith)
  have h₃ : 0 ≤ (run b t ℓ h).w % 2 ^ 32 := Int.emod_nonneg _ (by positivity)
  have h₄ : (run b t ℓ h).w % 2 ^ 32 < 2 ^ 32 := Int.emod_lt_of_pos _ (by positivity)
  have eu₁ := run_u₁ b t ℓ h
  have eu₂ : (run b t ℓ h).u₂ = (run b t ℓ h).r₁ * 2 ^ 32 + (run b t ℓ h).w % 2 ^ 32 := rfl
  have hu₁ : 0 ≤ (run b t ℓ h).u₁ ∧ (run b t ℓ h).u₁ < q * 2 ^ 32 :=
    ⟨by linarith, by linarith⟩
  have hu₂ : 0 ≤ (run b t ℓ h).u₂ ∧ (run b t ℓ h).u₂ < q * 2 ^ 32 :=
    ⟨by linarith, by linarith⟩
  rw [run_Rhi, run_Rlo]
  exact ⟨hu₁, hu₂, by norm_num [q], ⟨Int.ediv_nonneg hu₁.1 q_pos.le,
    Int.ediv_lt_of_lt_mul q_pos (by linarith)⟩, ⟨Int.ediv_nonneg hu₂.1 q_pos.le,
    Int.ediv_lt_of_lt_mul q_pos (by linarith)⟩⟩

/-- **Algorithm 4, integer part**: `k = ⌊c⌋` (p. 12, Output), for `b + t ≤ 64`. -/
theorem run_k {b t : ℕ} (hbt : b + t ≤ 64) (ℓ h : ℤ) :
    (run b t ℓ h).k = ⌊centre b t ℓ h⌋ := by
  obtain ⟨hr₀, hr₁, ⟨hw₀, hw₁⟩, hc⟩ := run_invariant hbt ℓ h
  have hq : (0 : ℝ) < q * 2 ^ 64 := mul_pos (by exact_mod_cast q_pos) (by positivity)
  have h₁ : (0 : ℝ) ≤ (run b t ℓ h).r := by exact_mod_cast hr₀
  have h₂ : ((run b t ℓ h).r : ℝ) + 1 ≤ q := by exact_mod_cast Int.add_one_le_of_lt hr₁
  have h₃ : (0 : ℝ) ≤ (run b t ℓ h).w := by exact_mod_cast hw₀
  have h₄ : ((run b t ℓ h).w : ℝ) < 2 ^ 64 := by exact_mod_cast hw₁
  have h₅ : (0 : ℝ) ≤ ((run b t ℓ h).r * 2 ^ 64 + (run b t ℓ h).w) / (q * 2 ^ 64) :=
    div_nonneg (by positivity) hq.le
  have h₆ : ((run b t ℓ h).r * 2 ^ 64 + (run b t ℓ h).w) / (q * 2 ^ 64) < (1 : ℝ) :=
    (div_lt_one hq).2 (by linarith)
  exact (Int.floor_eq_iff.2 ⟨by rw [hc]; linarith, by rw [hc]; linarith⟩).symm

private theorem lor_indicator {x : ℤ} (hx : 0 ≤ x) :
    x.lor (if x = 0 then 1 else 0) = max 1 x := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hx
  rcases n with _ | n
  · decide
  · have h₁ : ((n + 1 : ℕ) : ℤ) ≠ 0 := by omega
    have h₂ : (1 : ℤ) ≤ ((n + 1 : ℕ) : ℤ) := by omega
    rw [ite_eq_right h₁, max_eq_right h₂]
    exact congrArg Int.ofNat (Nat.or_zero _)

private theorem run_R_eq (b t : ℕ) (ℓ h : ℤ) : (run b t ℓ h).R = max 1 (run b t ℓ h).R₀ := by
  have hw : 0 ≤ (run b t ℓ h).w := mul_nonneg (run_X_mem b t ℓ h).1 (by positivity)
  have hu₁ : 0 ≤ (run b t ℓ h).u₁ := by
    rw [run_u₁]
    exact add_nonneg (mul_nonneg (run_r_mem b t ℓ h).1 (by positivity))
      (Int.ediv_nonneg hw (by positivity))
  have hu₂ : 0 ≤ (run b t ℓ h).u₂ :=
    add_nonneg (mul_nonneg (run_r₁_mem b t ℓ h).1 (by positivity))
      (Int.emod_nonneg _ (by positivity))
  have eR₀ : (run b t ℓ h).R₀ = (run b t ℓ h).u₁ / q * 2 ^ 32 + (run b t ℓ h).u₂ / q := by
    rw [← run_Rhi, ← run_Rlo]; rfl
  have hR₀ : 0 ≤ (run b t ℓ h).R₀ := by
    rw [eR₀]
    exact add_nonneg (mul_nonneg (Int.ediv_nonneg hu₁ q_pos.le) (by positivity))
      (Int.ediv_nonneg hu₂ q_pos.le)
  exact lor_indicator hR₀

/-- **Algorithm 4, fractional code**: `R = max{1, ⌊2⁶⁴(c − k)⌋}` (p. 12, Output; line 12 and
p. 13, l. 382-384), for `b + t ≤ 64`. -/
theorem run_R {b t : ℕ} (hbt : b + t ≤ 64) (ℓ h : ℤ) :
    (run b t ℓ h).R = max 1 ⌊2 ^ 64 * (centre b t ℓ h - ⌊centre b t ℓ h⌋)⌋ := by
  obtain ⟨-, -, -, hc⟩ := run_invariant hbt ℓ h
  have hF : ((run b t ℓ h).r * 2 ^ 64 + (run b t ℓ h).w : ℝ) =
      (((run b t ℓ h).u₂ % q : ℤ) : ℝ) + q * (run b t ℓ h).R₀ := by
    exact_mod_cast run_F b t ℓ h
  have hq : (0 : ℝ) < q := by exact_mod_cast q_pos
  have hs₀ : (0 : ℝ) ≤ (((run b t ℓ h).u₂ % q : ℤ) : ℝ) := by
    exact_mod_cast Int.emod_nonneg _ q_pos.ne'
  have hs₁ : (((run b t ℓ h).u₂ % q : ℤ) : ℝ) < q := by
    exact_mod_cast Int.emod_lt_of_pos _ q_pos
  have e : (2 : ℝ) ^ 64 * (centre b t ℓ h - (run b t ℓ h).k) =
      (run b t ℓ h).R₀ + (((run b t ℓ h).u₂ % q : ℤ) : ℝ) / q := by
    rw [hc, add_sub_cancel_left, hF]
    field_simp
    ring
  rw [← run_k hbt, run_R_eq, e]
  congr 1
  refine (Int.floor_eq_iff.2 ⟨?_, ?_⟩).symm
  · linarith [div_nonneg hs₀ hq.le]
  · linarith [(div_lt_one hq).2 hs₁]

/-- `1 ≤ R < 2⁶⁴` (p. 13, l. 386-387), for `b + t ≤ 64`. -/
theorem run_R_mem {b t : ℕ} (hbt : b + t ≤ 64) (ℓ h : ℤ) :
    1 ≤ (run b t ℓ h).R ∧ (run b t ℓ h).R < 2 ^ 64 := by
  obtain ⟨-, -, -, ⟨-, h₁⟩, ⟨-, h₂⟩⟩ := run_dividends hbt ℓ h
  have e : (run b t ℓ h).R₀ = (run b t ℓ h).Rhi * 2 ^ 32 + (run b t ℓ h).Rlo := rfl
  rw [run_R_eq]
  exact ⟨le_max_left _ _, max_lt (by norm_num) (by omega)⟩

/-- "Restricting `1 ≤ R < 2⁶⁴` keeps both values representable in one word" (p. 13, l. 386-387):
`R` and its complement `2⁶⁴ − R` are unsigned 64-bit integers, for `b + t ≤ 64`. -/
theorem run_R_complement_mem {b t : ℕ} (hbt : b + t ≤ 64) (ℓ h : ℤ) :
    Unsigned64 (run b t ℓ h).R ∧ Unsigned64 (2 ^ 64 - (run b t ℓ h).R) := by
  obtain ⟨h₁, h₂⟩ := run_R_mem hbt ℓ h
  exact ⟨⟨by linarith, h₂⟩, ⟨by linarith, by linarith⟩⟩

/-- **Algorithm 4 computes the Q64 rule**: `k + R 2⁻⁶⁴ = q64Round c` (p. 12, Output), for
`b + t ≤ 64`. -/
theorem run_fp {b t : ℕ} (hbt : b + t ≤ 64) (ℓ h : ℤ) :
    ((run b t ℓ h).k : ℝ) + ((run b t ℓ h).R : ℝ) / 2 ^ 64 = q64Round (centre b t ℓ h) := by
  rw [q64Round, run_R hbt, run_k hbt]

/-- The case split of p. 13, l. 390, with `θ = c − ⌊c⌋` and `R₀ = ⌊2⁶⁴θ⌋`:
`0 < c^fp − c = 2⁻⁶⁴ − θ ≤ 2⁻⁶⁴` when `R₀ = 0`, and `0 ≤ c − c^fp = θ − R₀2⁻⁶⁴ < 2⁻⁶⁴` when
`R₀ > 0`. -/
theorem q64Round_sub_cases (c : ℝ) :
    (⌊2 ^ 64 * (c - ⌊c⌋)⌋ = 0 →
      q64Round c - c = 1 / 2 ^ 64 - (c - ⌊c⌋) ∧ 0 < q64Round c - c ∧
        q64Round c - c ≤ 1 / 2 ^ 64) ∧
    (0 < ⌊2 ^ 64 * (c - ⌊c⌋)⌋ →
      c - q64Round c = (c - ⌊c⌋) - ⌊2 ^ 64 * (c - ⌊c⌋)⌋ / 2 ^ 64 ∧ 0 ≤ c - q64Round c ∧
        c - q64Round c < 1 / 2 ^ 64) := by
  have h₁ := Int.floor_le (2 ^ 64 * (c - ⌊c⌋))
  have h₂ := Int.lt_floor_add_one (2 ^ 64 * (c - ⌊c⌋))
  refine ⟨fun h₀ => ?_, fun h₀ => ?_⟩
  · have e : q64Round c - c = 1 / 2 ^ 64 - (c - ⌊c⌋) := by
      rw [q64Round, h₀, max_eq_left zero_le_one, Int.cast_one]; ring
    rw [h₀, Int.cast_zero] at h₁ h₂
    exact ⟨e, by linarith, by linarith⟩
  · have hm : (1 : ℤ) ≤ ⌊2 ^ 64 * (c - ⌊c⌋)⌋ := h₀
    have e : c - q64Round c = (c - ⌊c⌋) - ⌊2 ^ 64 * (c - ⌊c⌋)⌋ / 2 ^ 64 := by
      rw [q64Round, max_eq_right hm]; ring
    have e' : 2 ^ 64 * (c - q64Round c) = 2 ^ 64 * (c - ⌊c⌋) - ⌊2 ^ 64 * (c - ⌊c⌋)⌋ := by
      rw [e]; ring
    exact ⟨e, by linarith, by linarith⟩

/-- **The `2⁻⁶⁴` error bound** for every real `c`: `|c^fp − c| ≤ 2⁻⁶⁴` "even when zero is
replaced by one" (p. 13, l. 388-391). -/
theorem abs_q64Round_sub_le (c : ℝ) : |q64Round c - c| ≤ 1 / 2 ^ 64 := by
  obtain ⟨h₀, h₁⟩ := q64Round_sub_cases c
  have hm : 0 ≤ ⌊(2 : ℝ) ^ 64 * (c - ⌊c⌋)⌋ :=
    Int.floor_nonneg.2 (mul_nonneg (by positivity) (Int.fract_nonneg c))
  rcases hm.eq_or_lt with hm | hm
  · obtain ⟨-, h₂, h₃⟩ := h₀ hm.symm
    rwa [abs_of_pos h₂]
  · obtain ⟨-, h₂, h₃⟩ := h₁ hm
    rw [abs_sub_comm, abs_of_nonneg h₂]
    exact h₃.le

/-- "with equality exactly at integer centers" (p. 13, l. 391-392). -/
theorem abs_q64Round_sub_eq_iff (c : ℝ) :
    |q64Round c - c| = 1 / 2 ^ 64 ↔ ∃ z : ℤ, c = z := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨h₀, h₁⟩ := q64Round_sub_cases c
    have hm : 0 ≤ ⌊(2 : ℝ) ^ 64 * (c - ⌊c⌋)⌋ :=
      Int.floor_nonneg.2 (mul_nonneg (by positivity) (Int.fract_nonneg c))
    rcases hm.eq_or_lt with hm | hm
    · obtain ⟨e, h₂, -⟩ := h₀ hm.symm
      rw [abs_of_pos h₂, e] at h
      exact ⟨⌊c⌋, by linarith⟩
    · obtain ⟨-, h₂, h₃⟩ := h₁ hm
      rw [abs_sub_comm, abs_of_nonneg h₂] at h
      exact absurd h h₃.ne
  · rintro ⟨z, rfl⟩
    rw [q64Round, Int.floor_intCast, sub_self, mul_zero, Int.floor_zero, max_eq_left zero_le_one,
      Int.cast_one, add_sub_cancel_left, abs_of_pos (by positivity : (0 : ℝ) < 1 / 2 ^ 64)]

/-! ### 64-bit words (p. 13, l. 378-379) -/

/-- Every variable of Algorithm 4 lies in its 64-bit word: signed for `a, ℓ₀, H, v, h₀, k, r`
(both values of `k` and `r`) and `δ`, unsigned for `w, u, R_hi, R_lo, R` (both values of `u`,
`r` of line 8, `R` of lines 11-12) (p. 13, l. 378-379). -/
structure Trace.InWords (s : Trace) : Prop where
  /-- `a`. -/
  a : Signed64 s.a
  /-- `ℓ₀`. -/
  ℓ₀ : Signed64 s.ℓ₀
  /-- `H`. -/
  H : Signed64 s.H
  /-- `v`. -/
  v : Signed64 s.v
  /-- `h₀`. -/
  h₀ : Signed64 s.h₀
  /-- `k` of line 4. -/
  k₀ : Signed64 s.k₀
  /-- `r` of line 4. -/
  r₀ : Signed64 s.r₀
  /-- `δ`. -/
  δ : Signed64 s.δ
  /-- `k` of line 5. -/
  k : Signed64 s.k
  /-- `r` of line 5. -/
  r : Signed64 s.r
  /-- `w`. -/
  w : Unsigned64 s.w
  /-- `u` of line 7. -/
  u₁ : Unsigned64 s.u₁
  /-- `R_hi`. -/
  Rhi : Unsigned64 s.Rhi
  /-- `r` of line 8. -/
  r₁ : Unsigned64 s.r₁
  /-- `u` of line 9. -/
  u₂ : Unsigned64 s.u₂
  /-- `R_lo`. -/
  Rlo : Unsigned64 s.Rlo
  /-- `R` of line 11. -/
  R₀ : Unsigned64 s.R₀
  /-- `R` of line 12. -/
  R : Unsigned64 s.R

private theorem signed64_ediv {x d : ℤ} (hx : Signed64 x) (hd : 1 ≤ d) : Signed64 (x / d) := by
  have hd₀ : 0 < d := by omega
  have h₁ := mul_le_mul_of_nonpos_left hd (by norm_num : (-2 : ℤ) ^ 63 ≤ 0)
  have h₂ := mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℤ) ≤ 2 ^ 63)
  exact ⟨(Int.le_ediv_iff_mul_le hd₀).2 (by linarith [hx.le]),
    (Int.ediv_lt_iff_lt_mul hd₀).2 (by linarith [hx.lt])⟩

/-- "All center-preparation intermediates fit in signed or unsigned 64-bit words" (p. 13,
l. 378-379), when `ℓ` and `H = h + ⌊ℓ/2^b⌋` (line 2) are signed 64-bit integers, `0 < b < 64`
and `b + t ≤ 64`. -/
theorem run_inWords {b t : ℕ} (hb₀ : 0 < b) (hb : b < 64) (hbt : b + t ≤ 64) {ℓ h : ℤ}
    (hℓ : Signed64 ℓ) (hH : Signed64 (h + ℓ.fdiv (2 ^ b))) :
    (run b t ℓ h).InWords := by
  have hB : (2 : ℤ) ^ b ≤ 2 ^ 63 := pow_le_pow_right₀ (by norm_num) (by omega)
  have hT : (2 : ℤ) ^ t ≤ 2 ^ 63 := pow_le_pow_right₀ (by norm_num) (by omega)
  have ha : Signed64 (run b t ℓ h).a := by
    rw [run_a]; exact signed64_ediv hℓ (one_le_pow₀ (by norm_num))
  have hv : Signed64 (run b t ℓ h).v := by
    rw [run_v]; exact signed64_ediv hH (one_le_pow₀ (by norm_num))
  have hv₁ := hv.le
  have hv₂ := hv.lt
  obtain ⟨hℓ₀₁, hℓ₀₂⟩ := run_ℓ₀_mem b t ℓ h
  obtain ⟨hh₀₁, hh₀₂⟩ := run_h₀_mem b t ℓ h
  obtain ⟨hr₁, hr₂⟩ := run_r_mem b t ℓ h
  obtain ⟨hr₀₁, hr₀₂⟩ := run_r₀_mem b t ℓ h
  obtain ⟨hs₁, hs₂⟩ := run_r₁_mem b t ℓ h
  obtain ⟨hu₁, hu₂, -, ⟨hRhi₁, hRhi₂⟩, ⟨hRlo₁, hRlo₂⟩⟩ := run_dividends hbt ℓ h
  obtain ⟨hR₁, hR₂⟩ := run_R_mem hbt ℓ h
  have hq : q = 12289 := rfl
  have hk₁ : -2 ^ 50 ≤ (run b t ℓ h).k := by
    rw [(run_euclid b t ℓ h).1]; exact (Int.le_ediv_iff_mul_le q_pos).2 (by linarith)
  have hk₂ : (run b t ℓ h).k < 2 ^ 50 := by
    rw [(run_euclid b t ℓ h).1]; exact (Int.ediv_lt_iff_lt_mul q_pos).2 (by linarith)
  have ek : (run b t ℓ h).k = (run b t ℓ h).k₀ - (run b t ℓ h).δ := rfl
  have er : (run b t ℓ h).r = (run b t ℓ h).r₀ + q * (run b t ℓ h).δ := rfl
  have eR₀ : (run b t ℓ h).R₀ = (run b t ℓ h).Rhi * 2 ^ 32 + (run b t ℓ h).Rlo := rfl
  rcases run_δ b t ℓ h with hδ | hδ <;> rw [hδ] at ek er <;>
  exact ⟨ha, ⟨by linarith, by linarith⟩, hH, hv, ⟨by linarith, by linarith⟩,
    ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
    ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, run_w_mem hbt ℓ h,
    ⟨hu₁.1, by linarith⟩, ⟨hRhi₁, by linarith⟩, ⟨hs₁, by linarith⟩, ⟨hu₂.1, by linarith⟩,
    ⟨hRlo₁, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, hR₂⟩⟩

/-- The input condition of Algorithm 4, "the bounds of Section 4.3" (p. 12), from Table 4 (p. 12)
and Table 2 (p. 9, `b = log₂ d_p`): `(ℓ, h, t) = (L₂, H₂, 0)` for a coefficient of `ĉ₂` and
`(L₁, H′₁, 16)` for a coefficient of `c′₁` (p. 12, l. 361-362), with `‖L_j‖∞ < 2⁵⁷`,
`‖H₂‖∞ < 2²⁶`, `‖H′₁‖∞ < 2⁵⁰` at `n = 512` (`b = 43`) and `‖L_j‖∞ < 2⁵⁹`, `‖H₂‖∞ < 2²⁷`,
`‖H′₁‖∞ < 2⁵²` at `n = 1024` (`b = 44`). -/
inductive Table4Input : ℕ → ℕ → ℤ → ℤ → Prop
  /-- `ĉ₂` at `n = 512`. -/
  | c2_512 {ℓ h : ℤ} : |ℓ| < 2 ^ 57 → |h| < 2 ^ 26 → Table4Input 43 0 ℓ h
  /-- `c′₁` at `n = 512`. -/
  | c1_512 {ℓ h : ℤ} : |ℓ| < 2 ^ 57 → |h| < 2 ^ 50 → Table4Input 43 16 ℓ h
  /-- `ĉ₂` at `n = 1024`. -/
  | c2_1024 {ℓ h : ℤ} : |ℓ| < 2 ^ 59 → |h| < 2 ^ 27 → Table4Input 44 0 ℓ h
  /-- `c′₁` at `n = 1024`. -/
  | c1_1024 {ℓ h : ℤ} : |ℓ| < 2 ^ 59 → |h| < 2 ^ 52 → Table4Input 44 16 ℓ h

private theorem signed64_of_abs_lt {x : ℤ} (hx : |x| < 2 ^ 63) : Signed64 x :=
  ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩

private theorem table4_signed {b : ℕ} {ℓ h : ℤ} (hℓ : |ℓ| < 2 ^ 59) (hh : |h| < 2 ^ 52) :
    Signed64 ℓ ∧ Signed64 (h + ℓ.fdiv (2 ^ b)) := by
  have ha : |ℓ.fdiv (2 ^ b)| ≤ |ℓ| := by rw [fdiv_two_pow]; exact Int.abs_ediv_le_abs _ _
  exact ⟨signed64_of_abs_lt (by linarith),
    signed64_of_abs_lt (by linarith [abs_add_le h (ℓ.fdiv (2 ^ b))])⟩

private theorem Table4Input.bounds {b t : ℕ} {ℓ h : ℤ} (hin : Table4Input b t ℓ h) :
    0 < b ∧ b < 64 ∧ b + t ≤ 64 ∧ Signed64 ℓ ∧ Signed64 (h + ℓ.fdiv (2 ^ b)) := by
  rcases hin with ⟨hℓ, hh⟩ | ⟨hℓ, hh⟩ | ⟨hℓ, hh⟩ | ⟨hℓ, hh⟩ <;>
  exact ⟨by norm_num, by norm_num, by norm_num, table4_signed (by linarith) (by linarith)⟩

/-- Under the §4.3 bounds every intermediate lies in its 64-bit word (p. 13, l. 378-379). -/
theorem run_inWords_of_table4 {b t : ℕ} {ℓ h : ℤ} (hin : Table4Input b t ℓ h) :
    (run b t ℓ h).InWords := by
  obtain ⟨hb₀, hb, hbt, hℓ, hH⟩ := hin.bounds
  exact run_inWords hb₀ hb hbt hℓ hH

/-- **Algorithm 4** ([ZKLY26, p. 12-13]): for inputs within the §4.3 bounds (`Table4Input`, not
proved here), `k = ⌊c⌋`, `R = max{1, ⌊2⁶⁴(c − k)⌋}`, `1 ≤ R < 2⁶⁴`, `|c^fp − c| ≤ 2⁻⁶⁴` for
`c^fp = k + R2⁻⁶⁴`, and every intermediate lies in its 64-bit word. -/
theorem algorithm4_correct {b t : ℕ} {ℓ h : ℤ} (hin : Table4Input b t ℓ h) :
    (run b t ℓ h).k = ⌊centre b t ℓ h⌋ ∧
      (run b t ℓ h).R = max 1 ⌊2 ^ 64 * (centre b t ℓ h - ⌊centre b t ℓ h⌋)⌋ ∧
      1 ≤ (run b t ℓ h).R ∧ (run b t ℓ h).R < 2 ^ 64 ∧
      |((run b t ℓ h).k : ℝ) + ((run b t ℓ h).R : ℝ) / 2 ^ 64 - centre b t ℓ h| ≤ 1 / 2 ^ 64 ∧
      (run b t ℓ h).InWords := by
  obtain ⟨-, -, hbt, -⟩ := hin.bounds
  obtain ⟨hR₁, hR₂⟩ := run_R_mem hbt ℓ h
  refine ⟨run_k hbt ℓ h, run_R hbt ℓ h, hR₁, hR₂, ?_, run_inWords_of_table4 hin⟩
  rw [run_fp hbt]
  exact abs_q64Round_sub_le _

/-- The input condition is satisfiable at its extreme values (`n = 1024`, `c′₁`). -/
theorem table4Input_witness : Table4Input 44 16 (-(2 ^ 59 - 1)) (2 ^ 52 - 1) :=
  .c1_1024 (by norm_num) (by norm_num)

/-! ### Algorithm 4 on 64-bit words -/

/-- The variables of Algorithm 4 as 64-bit words (names as in `Trace`). -/
structure TraceBV where
  /-- Line 1: `a`. -/
  a : BitVec 64
  /-- Line 1: `ℓ₀`. -/
  ℓ₀ : BitVec 64
  /-- Line 2: `H`. -/
  H : BitVec 64
  /-- Line 3: `v`. -/
  v : BitVec 64
  /-- Line 3: `h₀`. -/
  h₀ : BitVec 64
  /-- Line 4: `k`. -/
  k₀ : BitVec 64
  /-- Line 4: `r`. -/
  r₀ : BitVec 64
  /-- Line 5: `δ`. -/
  δ : BitVec 64
  /-- Line 5: `k`. -/
  k : BitVec 64
  /-- Line 5: `r`. -/
  r : BitVec 64
  /-- Line 6: `w`. -/
  w : BitVec 64
  /-- Line 7: `u`. -/
  u₁ : BitVec 64
  /-- Line 8: `R_hi`. -/
  Rhi : BitVec 64
  /-- Line 8: `r`. -/
  r₁ : BitVec 64
  /-- Line 9: `u`. -/
  u₂ : BitVec 64
  /-- Line 10: `R_lo`. -/
  Rlo : BitVec 64
  /-- Line 11: `R`. -/
  R₀ : BitVec 64
  /-- Line 12: `R`. -/
  R : BitVec 64

/-- The word `q`. -/
def qw : BitVec 64 := 12289#64

/-- **Algorithm 4 on 64-bit words** (p. 12; operations as on p. 12-13, l. 369-372): `⌊·/2^b⌋` is
the arithmetic shift `sshiftRight`, `· − 2^b⌊·/2^b⌋` and `mod 2³²` are masks, `⌊w/2³²⌋` is the
logical shift, `trunc` is `sdiv`, `[r < 0]` is the signed comparison `slt`, the digit divisions are
`udiv`, `OR` is `|||`, and `+`, `−`, `*` are the wrapping word operations. -/
def runBV (b t : ℕ) (ℓ h : BitVec 64) : TraceBV :=
  let a := ℓ.sshiftRight b
  let ℓ₀ := ℓ &&& BitVec.ofNat 64 (2 ^ b - 1)
  let H := h + a
  let v := H.sshiftRight t
  let h₀ := H &&& BitVec.ofNat 64 (2 ^ t - 1)
  let k₀ := v.sdiv qw
  let r₀ := v - qw * k₀
  let δ := (BitVec.ofBool (r₀.slt 0#64)).setWidth 64
  let k := k₀ - δ
  let r := r₀ + qw * δ
  let w := (BitVec.ofNat 64 (2 ^ b) * h₀ + ℓ₀) * BitVec.ofNat 64 (2 ^ (64 - b - t))
  let u₁ := r * BitVec.ofNat 64 (2 ^ 32) + w >>> 32
  let Rhi := u₁.udiv qw
  let r₁ := u₁ - qw * Rhi
  let u₂ := r₁ * BitVec.ofNat 64 (2 ^ 32) + (w &&& BitVec.ofNat 64 (2 ^ 32 - 1))
  let Rlo := u₂.udiv qw
  let R₀ := Rhi * BitVec.ofNat 64 (2 ^ 32) + Rlo
  let R := R₀ ||| (BitVec.ofBool (R₀ == 0#64)).setWidth 64
  ⟨a, ℓ₀, H, v, h₀, k₀, r₀, δ, k, r, w, u₁, Rhi, r₁, u₂, Rlo, R₀, R⟩

/-- No word operation of `runBV` overflows (Lean core's overflow predicates): signed `+`, `−`, `*`
and `sdiv` on lines 2, 4, 5; unsigned `+`, `−`, `*` on lines 6-9 and 11. -/
structure TraceBV.NoOverflow (b t : ℕ) (h : BitVec 64) (s : TraceBV) : Prop where
  /-- Line 2: `h + a`. -/
  H : ¬ h.saddOverflow s.a
  /-- Line 4: `trunc(v/q)`. -/
  k₀ : ¬ s.v.sdivOverflow qw
  /-- Line 4: `qk`. -/
  qk₀ : ¬ qw.smulOverflow s.k₀
  /-- Line 4: `v − qk`. -/
  r₀ : ¬ s.v.ssubOverflow (qw * s.k₀)
  /-- Line 5: `k − δ`. -/
  k : ¬ s.k₀.ssubOverflow s.δ
  /-- Line 5: `qδ`. -/
  qδ : ¬ qw.smulOverflow s.δ
  /-- Line 5: `r + qδ`. -/
  r : ¬ s.r₀.saddOverflow (qw * s.δ)
  /-- Line 6: `2^b h₀`. -/
  bh₀ : ¬ (BitVec.ofNat 64 (2 ^ b)).umulOverflow s.h₀
  /-- Line 6: `2^b h₀ + ℓ₀`. -/
  bh₀ℓ₀ : ¬ (BitVec.ofNat 64 (2 ^ b) * s.h₀).uaddOverflow s.ℓ₀
  /-- Line 6: `(2^b h₀ + ℓ₀) 2^{64−b−t}`. -/
  w : ¬ (BitVec.ofNat 64 (2 ^ b) * s.h₀ + s.ℓ₀).umulOverflow
    (BitVec.ofNat 64 (2 ^ (64 - b - t)))
  /-- Line 7: `r 2³²`. -/
  r2 : ¬ s.r.umulOverflow (BitVec.ofNat 64 (2 ^ 32))
  /-- Line 7: `r 2³² + ⌊w/2³²⌋`. -/
  u₁ : ¬ (s.r * BitVec.ofNat 64 (2 ^ 32)).uaddOverflow (s.w >>> 32)
  /-- Line 8: `qR_hi`. -/
  qRhi : ¬ qw.umulOverflow s.Rhi
  /-- Line 8: `u − qR_hi`. -/
  r₁ : ¬ s.u₁.usubOverflow (qw * s.Rhi)
  /-- Line 9: `r 2³²`. -/
  r₁2 : ¬ s.r₁.umulOverflow (BitVec.ofNat 64 (2 ^ 32))
  /-- Line 9: `r 2³² + (w mod 2³²)`. -/
  u₂ : ¬ (s.r₁ * BitVec.ofNat 64 (2 ^ 32)).uaddOverflow (s.w &&& BitVec.ofNat 64 (2 ^ 32 - 1))
  /-- Line 11: `R_hi 2³²`. -/
  Rhi2 : ¬ s.Rhi.umulOverflow (BitVec.ofNat 64 (2 ^ 32))
  /-- Line 11: `R_hi 2³² + R_lo`. -/
  R₀ : ¬ (s.Rhi * BitVec.ofNat 64 (2 ^ 32)).uaddOverflow s.Rlo

/-- The words of `s` have the values of `z`: `toInt` for the signed variables, `toNat` for the
unsigned ones. -/
structure TraceBV.Refines (s : TraceBV) (z : Trace) : Prop where
  /-- `a`. -/
  a : s.a.toInt = z.a
  /-- `ℓ₀`. -/
  ℓ₀ : s.ℓ₀.toInt = z.ℓ₀
  /-- `H`. -/
  H : s.H.toInt = z.H
  /-- `v`. -/
  v : s.v.toInt = z.v
  /-- `h₀`. -/
  h₀ : s.h₀.toInt = z.h₀
  /-- `k` of line 4. -/
  k₀ : s.k₀.toInt = z.k₀
  /-- `r` of line 4. -/
  r₀ : s.r₀.toInt = z.r₀
  /-- `δ`. -/
  δ : s.δ.toInt = z.δ
  /-- `k` of line 5. -/
  k : s.k.toInt = z.k
  /-- `r` of line 5. -/
  r : s.r.toInt = z.r
  /-- `w`. -/
  w : (s.w.toNat : ℤ) = z.w
  /-- `u` of line 7. -/
  u₁ : (s.u₁.toNat : ℤ) = z.u₁
  /-- `R_hi`. -/
  Rhi : (s.Rhi.toNat : ℤ) = z.Rhi
  /-- `r` of line 8. -/
  r₁ : (s.r₁.toNat : ℤ) = z.r₁
  /-- `u` of line 9. -/
  u₂ : (s.u₂.toNat : ℤ) = z.u₂
  /-- `R_lo`. -/
  Rlo : (s.Rlo.toNat : ℤ) = z.Rlo
  /-- `R` of line 11. -/
  R₀ : (s.R₀.toNat : ℤ) = z.R₀
  /-- `R` of line 12. -/
  R : (s.R.toNat : ℤ) = z.R

private theorem signed64_toInt (x : BitVec 64) : Signed64 x.toInt :=
  ⟨by simpa using x.le_toInt, by simpa using BitVec.toInt_lt (x := x)⟩

private theorem toNat_of_toInt_nonneg {x : BitVec 64} (h : 0 ≤ x.toInt) :
    (x.toNat : ℤ) = x.toInt := by
  rw [BitVec.toInt_eq_toNat_cond] at h ⊢
  have := x.isLt
  split_ifs at h ⊢ <;> omega

private theorem toNat_ofNat_two_pow {k : ℕ} (hk : k < 64) :
    ((BitVec.ofNat 64 (2 ^ k)).toNat : ℤ) = 2 ^ k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num : 1 < 2) hk)]
  push_cast; rfl

private theorem toNat_and_mask (x : BitVec 64) {k : ℕ} (hk : k ≤ 64) :
    (x &&& BitVec.ofNat 64 (2 ^ k - 1)).toNat = x.toNat % 2 ^ k := by
  have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hk
  have h : 2 ^ k - 1 < 2 ^ 64 := by omega
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.and_two_pow_sub_one_eq_mod]

private theorem toInt_and_mask (x : BitVec 64) {k : ℕ} (hk : k < 64) :
    (x &&& BitVec.ofNat 64 (2 ^ k - 1)).toInt = x.toInt % 2 ^ k := by
  have h₁ := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : k ≤ 63)
  have h₂ := Nat.mod_lt x.toNat (Nat.two_pow_pos k)
  have h₃ : 2 * (x &&& BitVec.ofNat 64 (2 ^ k - 1)).toNat < 2 ^ 64 := by
    rw [toNat_and_mask x hk.le]; omega
  rw [BitVec.toInt_eq_toNat_of_lt h₃, toNat_and_mask x hk.le, BitVec.toInt_eq_toNat_cond]
  push_cast
  split_ifs
  · rfl
  · rw [← Int.add_mul_emod_self_left (x.toNat : ℤ) (2 ^ k) (-2 ^ (64 - k))]
    congr 1
    rw [mul_neg, ← pow_add, Nat.add_sub_of_le hk.le]; ring

private theorem toInt_sshiftRight_eq (x : BitVec 64) (k : ℕ) :
    (x.sshiftRight k).toInt = x.toInt / 2 ^ k := by
  rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]; push_cast; rfl

private theorem toNat_udiv_qw (x : BitVec 64) : ((x.udiv qw).toNat : ℤ) = x.toNat / q := by
  rw [BitVec.udiv_eq, BitVec.toNat_udiv]; push_cast; rfl

private theorem sadd_ok {x y : BitVec 64} {X Y : ℤ} (hx : x.toInt = X) (hy : y.toInt = Y)
    (h : Signed64 (X + Y)) : ¬ x.saddOverflow y ∧ (x + y).toInt = X + Y := by
  have hn : ¬ x.saddOverflow y := by
    have := h.le; have := h.lt
    simp only [BitVec.saddOverflow, hx, hy, Bool.or_eq_true, decide_eq_true_eq,
      Nat.reduceSub]
    omega
  exact ⟨hn, by rw [BitVec.toInt_add_of_not_saddOverflow hn, hx, hy]⟩

private theorem ssub_ok {x y : BitVec 64} {X Y : ℤ} (hx : x.toInt = X) (hy : y.toInt = Y)
    (h : Signed64 (X - Y)) : ¬ x.ssubOverflow y ∧ (x - y).toInt = X - Y := by
  have hn : ¬ x.ssubOverflow y := by
    have := h.le; have := h.lt
    simp only [BitVec.ssubOverflow, hx, hy, Bool.or_eq_true, decide_eq_true_eq,
      Nat.reduceSub]
    omega
  exact ⟨hn, by rw [BitVec.toInt_sub_of_not_ssubOverflow hn, hx, hy]⟩

private theorem smul_ok {x y : BitVec 64} {X Y : ℤ} (hx : x.toInt = X) (hy : y.toInt = Y)
    (h : Signed64 (X * Y)) : ¬ x.smulOverflow y ∧ (x * y).toInt = X * Y := by
  have hn : ¬ x.smulOverflow y := by
    have := h.le; have := h.lt
    simp only [BitVec.smulOverflow, hx, hy, Bool.or_eq_true, decide_eq_true_eq,
      Nat.reduceSub]
    omega
  exact ⟨hn, by rw [BitVec.toInt_mul_of_not_smulOverflow hn, hx, hy]⟩

private theorem sdiv_ok {x : BitVec 64} {X : ℤ} (hx : x.toInt = X) (h : Signed64 (X / q)) :
    ¬ x.sdivOverflow qw ∧ (x.sdiv qw).toInt = X.tdiv q := by
  have hq : qw.toInt = q := rfl
  have hn : ¬ x.sdivOverflow qw := by
    have := h.le; have := h.lt
    simp only [BitVec.sdivOverflow, hx, hq, Bool.or_eq_true, decide_eq_true_eq,
      Nat.reduceSub]
    omega
  exact ⟨hn, by rw [BitVec.toInt_sdiv_of_ne_or_ne x qw (Or.inr (by decide)), hx, hq]⟩

private theorem uadd_ok {x y : BitVec 64} {X Y : ℤ} (hx : (x.toNat : ℤ) = X)
    (hy : (y.toNat : ℤ) = Y) (h : X + Y < 2 ^ 64) :
    ¬ x.uaddOverflow y ∧ ((x + y).toNat : ℤ) = X + Y := by
  have hn : ¬ x.uaddOverflow y := by
    simp only [BitVec.uaddOverflow, decide_eq_true_eq]
    omega
  exact ⟨hn, by rw [BitVec.toNat_add_of_not_uaddOverflow hn, Nat.cast_add, hx, hy]⟩

private theorem umul_ok {x y : BitVec 64} {X Y : ℤ} (hx : (x.toNat : ℤ) = X)
    (hy : (y.toNat : ℤ) = Y) (h : X * Y < 2 ^ 64) :
    ¬ x.umulOverflow y ∧ ((x * y).toNat : ℤ) = X * Y := by
  have h' : ((x.toNat * y.toNat : ℕ) : ℤ) < 2 ^ 64 := by rw [Nat.cast_mul, hx, hy]; exact h
  have hn : ¬ x.umulOverflow y := by
    simp only [BitVec.umulOverflow, decide_eq_true_eq, not_le]
    exact_mod_cast h'
  exact ⟨hn, by rw [BitVec.toNat_mul_of_not_umulOverflow hn, Nat.cast_mul, hx, hy]⟩

private theorem usub_ok {x y : BitVec 64} {X Y : ℤ} (hx : (x.toNat : ℤ) = X)
    (hy : (y.toNat : ℤ) = Y) (h : Y ≤ X) :
    ¬ x.usubOverflow y ∧ ((x - y).toNat : ℤ) = X - Y := by
  have hle : y.toNat ≤ x.toNat := by omega
  have hn : ¬ x.usubOverflow y := by
    simp only [BitVec.usubOverflow, decide_eq_true_eq, not_lt]
    exact hle
  exact ⟨hn, by rw [BitVec.toNat_sub_of_not_usubOverflow hn, Nat.cast_sub hle, hx, hy]⟩

private theorem runBV_spec {b t : ℕ} (hb₀ : 0 < b) (hb : b < 64) (hbt : b + t ≤ 64)
    {ℓ h : BitVec 64} (hH : Signed64 (h.toInt + ℓ.toInt.fdiv (2 ^ b))) :
    (runBV b t ℓ h).NoOverflow b t h ∧ (runBV b t ℓ h).Refines (run b t ℓ.toInt h.toInt) := by
  have hW := run_inWords hb₀ hb hbt (signed64_toInt ℓ) hH
  obtain ⟨hk, -⟩ := run_euclid b t ℓ.toInt h.toInt
  have hra := run_a b t ℓ.toInt h.toInt
  have hrℓ₀ := run_ℓ₀ b t ℓ.toInt h.toInt
  have hrv := run_v b t ℓ.toInt h.toInt
  have hrh₀ := run_h₀ b t ℓ.toInt h.toInt
  have hru₁ := run_u₁ b t ℓ.toInt h.toInt
  have hrRhi := run_Rhi b t ℓ.toInt h.toInt
  have hrRlo := run_Rlo b t ℓ.toInt h.toInt
  have hrR := run_R_eq b t ℓ.toInt h.toInt
  obtain ⟨hs₁, hs₂⟩ := run_r₀_sign b t ℓ.toInt h.toInt
  obtain ⟨hr₀₁, hr₀₂⟩ := run_r₀_mem b t ℓ.toInt h.toInt
  obtain ⟨hr₁, hr₂⟩ := run_r_mem b t ℓ.toInt h.toInt
  obtain ⟨-, hr₁₂⟩ := run_r₁_mem b t ℓ.toInt h.toInt
  obtain ⟨hℓ₀₁, -⟩ := run_ℓ₀_mem b t ℓ.toInt h.toInt
  obtain ⟨hh₀₁, -⟩ := run_h₀_mem b t ℓ.toInt h.toInt
  obtain ⟨-, hX⟩ := run_X_mem b t ℓ.toInt h.toInt
  obtain ⟨⟨-, hu₁⟩, ⟨-, hu₂⟩, -, ⟨-, hRhi⟩, -⟩ := run_dividends hbt ℓ.toInt h.toInt
  have hδ := run_δ b t ℓ.toInt h.toInt
  have hq : q = 12289 := rfl
  have hBT : (2 : ℤ) ^ b * 2 ^ t ≤ 2 ^ 64 := by
    rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) hbt
  set z := run b t ℓ.toInt h.toInt
  set s := runBV b t ℓ h
  have hqI : qw.toInt = q := rfl
  have hqN : (qw.toNat : ℤ) = q := rfl
  have h32 : ((BitVec.ofNat 64 (2 ^ 32)).toNat : ℤ) = 2 ^ 32 := toNat_ofNat_two_pow (by norm_num)
  have ea : s.a.toInt = z.a := by rw [hra]; exact toInt_sshiftRight_eq ℓ b
  have eℓ₀ : s.ℓ₀.toInt = z.ℓ₀ := by rw [hrℓ₀]; exact toInt_and_mask ℓ hb
  have oH := sadd_ok (x := h) (y := s.a) rfl ea hW.H
  have eH : s.H.toInt = z.H := oH.2
  have ev : s.v.toInt = z.v := by rw [hrv, ← eH]; exact toInt_sshiftRight_eq s.H t
  have eh₀ : s.h₀.toInt = z.h₀ := by rw [hrh₀, ← eH]; exact toInt_and_mask s.H (by omega)
  have ok₀ := sdiv_ok (x := s.v) ev (by rw [← hk]; exact hW.k)
  have ek₀ : s.k₀.toInt = z.k₀ := ok₀.2
  have hqk : Signed64 (q * z.k₀) := by
    have e : z.r₀ = z.v - q * z.k₀ := rfl
    have := hW.v.le
    have := hW.v.lt
    rcases le_or_gt 0 z.v with hv | hv
    · have := hs₁ hv; exact ⟨by linarith, by linarith⟩
    · have := hs₂ hv.le; exact ⟨by linarith, by linarith⟩
  have oqk := smul_ok (x := qw) (y := s.k₀) hqI ek₀ hqk
  have or₀ := ssub_ok (x := s.v) (y := qw * s.k₀) ev oqk.2 hW.r₀
  have er₀ : s.r₀.toInt = z.r₀ := or₀.2
  have eδ : s.δ.toInt = z.δ := by
    have e₁ : s.r₀.slt 0#64 = decide (z.r₀ < 0) := by
      simp only [BitVec.slt, er₀, BitVec.toInt_zero]
    change ((BitVec.ofBool (s.r₀.slt 0#64)).setWidth 64).toInt = if z.r₀ < 0 then 1 else 0
    rw [e₁]
    by_cases hn : z.r₀ < 0
    · rw [decide_eq_true hn, ite_eq_left hn]; decide
    · rw [decide_eq_false hn, ite_eq_right hn]; decide
  have ok := ssub_ok (x := s.k₀) (y := s.δ) ek₀ eδ hW.k
  have ek : s.k.toInt = z.k := ok.2
  have hqδ : Signed64 (q * z.δ) := by
    rcases hδ with hδ | hδ <;> rw [hδ, hq] <;> constructor <;> norm_num
  have oqδ := smul_ok (x := qw) (y := s.δ) hqI eδ hqδ
  have oR := sadd_ok (x := s.r₀) (y := qw * s.δ) er₀ oqδ.2 hW.r
  have er : s.r.toInt = z.r := oR.2
  have nh₀ : (s.h₀.toNat : ℤ) = z.h₀ := by
    rw [toNat_of_toInt_nonneg (x := s.h₀) (by omega), eh₀]
  have nℓ₀ : (s.ℓ₀.toNat : ℤ) = z.ℓ₀ := by
    rw [toNat_of_toInt_nonneg (x := s.ℓ₀) (by omega), eℓ₀]
  have nr : (s.r.toNat : ℤ) = z.r := by rw [toNat_of_toInt_nonneg (x := s.r) (by omega), er]
  have m₁ := umul_ok (x := BitVec.ofNat 64 (2 ^ b)) (y := s.h₀) (toNat_ofNat_two_pow hb) nh₀
    (by linarith)
  have m₂ := uadd_ok (x := BitVec.ofNat 64 (2 ^ b) * s.h₀) (y := s.ℓ₀) m₁.2 nℓ₀ (by linarith)
  have m₃ := umul_ok (x := BitVec.ofNat 64 (2 ^ b) * s.h₀ + s.ℓ₀)
    (y := BitVec.ofNat 64 (2 ^ (64 - b - t))) m₂.2 (toNat_ofNat_two_pow (by omega)) hW.w.lt
  have nw : (s.w.toNat : ℤ) = z.w := m₃.2
  have m₄ := umul_ok (x := s.r) (y := BitVec.ofNat 64 (2 ^ 32)) nr h32 (by linarith)
  have nwh : ((s.w >>> 32).toNat : ℤ) = z.w / 2 ^ 32 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; push_cast; rw [nw]
  have m₅ := uadd_ok (x := s.r * BitVec.ofNat 64 (2 ^ 32)) (y := s.w >>> 32) m₄.2 nwh
    (by rw [← hru₁]; linarith)
  have nu₁ : (s.u₁.toNat : ℤ) = z.u₁ := by rw [hru₁]; exact m₅.2
  have nRhi : (s.Rhi.toNat : ℤ) = z.Rhi := by rw [hrRhi, ← nu₁]; exact toNat_udiv_qw s.u₁
  have hqR : q * z.Rhi ≤ z.u₁ := by
    rw [hrRhi, mul_comm]; exact Int.ediv_mul_le _ q_pos.ne'
  have m₆ := umul_ok (x := qw) (y := s.Rhi) hqN nRhi (by linarith)
  have m₇ := usub_ok (x := s.u₁) (y := qw * s.Rhi) nu₁ m₆.2 hqR
  have nr₁ : (s.r₁.toNat : ℤ) = z.r₁ := m₇.2
  have m₈ := umul_ok (x := s.r₁) (y := BitVec.ofNat 64 (2 ^ 32)) nr₁ h32 (by linarith)
  have nwl : ((s.w &&& BitVec.ofNat 64 (2 ^ 32 - 1)).toNat : ℤ) = z.w % 2 ^ 32 := by
    rw [toNat_and_mask s.w (by norm_num)]; push_cast; rw [nw]
  have hu₂' : z.r₁ * 2 ^ 32 + z.w % 2 ^ 32 < q * 2 ^ 32 := hu₂
  have m₉ := uadd_ok (x := s.r₁ * BitVec.ofNat 64 (2 ^ 32))
    (y := s.w &&& BitVec.ofNat 64 (2 ^ 32 - 1)) m₈.2 nwl (by linarith)
  have nu₂ : (s.u₂.toNat : ℤ) = z.u₂ := m₉.2
  have nRlo : (s.Rlo.toNat : ℤ) = z.Rlo := by rw [hrRlo, ← nu₂]; exact toNat_udiv_qw s.u₂
  have m₁₀ := umul_ok (x := s.Rhi) (y := BitVec.ofNat 64 (2 ^ 32)) nRhi h32 (by omega)
  have m₁₁ := uadd_ok (x := s.Rhi * BitVec.ofNat 64 (2 ^ 32)) (y := s.Rlo) m₁₀.2 nRlo
    hW.R₀.lt
  have nR₀ : (s.R₀.toNat : ℤ) = z.R₀ := m₁₁.2
  have nR : (s.R.toNat : ℤ) = z.R := by
    rw [hrR]
    change ((s.R₀ ||| (BitVec.ofBool (s.R₀ == 0#64)).setWidth 64).toNat : ℤ) = _
    by_cases h₀ : s.R₀ = 0#64
    · have h₁ := congrArg BitVec.toNat h₀
      rw [BitVec.toNat_ofNat] at h₁
      have : z.R₀ = 0 := by omega
      rw [h₀, this]; decide
    · have hne : z.R₀ ≠ 0 := fun h' => h₀ (BitVec.eq_of_toNat_eq (by
        rw [BitVec.toNat_ofNat]; omega))
      have e₁ : (BitVec.ofBool (s.R₀ == 0#64)).setWidth 64 = 0#64 := by
        rw [beq_eq_false_iff_ne.2 h₀]; decide
      have h₁ : (1 : ℤ) ≤ z.R₀ := by omega
      rw [e₁, BitVec.or_zero, nR₀, max_eq_right h₁]
  exact ⟨⟨oH.1, ok₀.1, oqk.1, or₀.1, ok.1, oqδ.1, oR.1, m₁.1, m₂.1, m₃.1, m₄.1, m₅.1, m₆.1,
    m₇.1, m₈.1, m₉.1, m₁₀.1, m₁₁.1⟩,
    ⟨ea, eℓ₀, eH, ev, eh₀, ek₀, er₀, eδ, ek, er, nw, nu₁, nRhi, nr₁, nu₂, nRlo, nR₀, nR⟩⟩

/-- "All center-preparation intermediates fit in signed or unsigned 64-bit words" (p. 13,
l. 378-379), as a statement about word operations: if `H = h + ⌊ℓ/2^b⌋` is a signed 64-bit
integer, no operation of `runBV` overflows. -/
theorem runBV_noOverflow {b t : ℕ} (hb₀ : 0 < b) (hb : b < 64) (hbt : b + t ≤ 64)
    {ℓ h : BitVec 64} (hH : Signed64 (h.toInt + ℓ.toInt.fdiv (2 ^ b))) :
    (runBV b t ℓ h).NoOverflow b t h :=
  (runBV_spec hb₀ hb hbt hH).1

/-- Under the same condition the word program computes the values of `run` on `ℓ.toInt`,
`h.toInt`. -/
theorem runBV_refines {b t : ℕ} (hb₀ : 0 < b) (hb : b < 64) (hbt : b + t ≤ 64)
    {ℓ h : BitVec 64} (hH : Signed64 (h.toInt + ℓ.toInt.fdiv (2 ^ b))) :
    (runBV b t ℓ h).Refines (run b t ℓ.toInt h.toInt) :=
  (runBV_spec hb₀ hb hbt hH).2

/-- **The word program computes the Q64 rule**: `k + R 2⁻⁶⁴ = q64Round c` on 64-bit words, when
`H = h + ⌊ℓ/2^b⌋` is a signed 64-bit integer, `0 < b < 64` and `b + t ≤ 64`. -/
theorem runBV_fp {b t : ℕ} (hb₀ : 0 < b) (hb : b < 64) (hbt : b + t ≤ 64)
    {ℓ h : BitVec 64} (hH : Signed64 (h.toInt + ℓ.toInt.fdiv (2 ^ b))) :
    ((runBV b t ℓ h).k.toInt : ℝ) + ((runBV b t ℓ h).R.toNat : ℝ) / 2 ^ 64 =
      q64Round (centre b t ℓ.toInt h.toInt) := by
  have hR := (runBV_spec hb₀ hb hbt hH).2
  have e : ((runBV b t ℓ h).R.toNat : ℝ) = ((run b t ℓ.toInt h.toInt).R : ℝ) := by
    rw [← hR.R]; norm_cast
  rw [hR.k, e]
  exact run_fp hbt _ _

/-- Under the §4.3 bounds (`Table4Input`, not proved here) the word program does not overflow and
computes `q64Round c`. -/
theorem runBV_correct_of_table4 {b t : ℕ} {ℓ h : BitVec 64}
    (hin : Table4Input b t ℓ.toInt h.toInt) :
    (runBV b t ℓ h).NoOverflow b t h ∧ (runBV b t ℓ h).Refines (run b t ℓ.toInt h.toInt) ∧
      ((runBV b t ℓ h).k.toInt : ℝ) + ((runBV b t ℓ h).R.toNat : ℝ) / 2 ^ 64 =
        q64Round (centre b t ℓ.toInt h.toInt) := by
  obtain ⟨hb₀, hb, hbt, -, hH⟩ := hin.bounds
  exact ⟨runBV_noOverflow hb₀ hb hbt hH, runBV_refines hb₀ hb hbt hH, runBV_fp hb₀ hb hbt hH⟩

/-! ### Concrete checks of the definitions -/

/-- `run` at the extreme `Table4Input` (`n = 1024`, `c′₁`), at an integer centre (`c = 3`, so
`R₀ = 0` and line 12 sets `R = 1`) and at a negative centre. -/
theorem run_examples :
    ((run 44 16 (-(2 ^ 59 - 1)) (2 ^ 52 - 1)).k = 5591950 ∧
      (run 44 16 (-(2 ^ 59 - 1)) (2 ^ 52 - 1)).R = 4781683047060525670) ∧
    ((run 43 0 0 36867).k = 3 ∧ (run 43 0 0 36867).R₀ = 0 ∧ (run 43 0 0 36867).R = 1) ∧
    ((run 43 16 (-5) (-7)).k = -1 ∧ (run 43 16 (-5) (-7)).R = 18446743913377153782) := by
  decide

/-- `runBV` on the same inputs. -/
theorem runBV_examples :
    ((runBV 44 16 (BitVec.ofInt 64 (-(2 ^ 59 - 1))) (BitVec.ofInt 64 (2 ^ 52 - 1))).k.toInt =
        5591950 ∧
      (runBV 44 16 (BitVec.ofInt 64 (-(2 ^ 59 - 1))) (BitVec.ofInt 64 (2 ^ 52 - 1))).R.toNat =
        4781683047060525670) ∧
    ((runBV 43 0 0#64 (BitVec.ofInt 64 36867)).k.toInt = 3 ∧
      (runBV 43 0 0#64 (BitVec.ofInt 64 36867)).R.toNat = 1) ∧
    ((runBV 43 16 (BitVec.ofInt 64 (-5)) (BitVec.ofInt 64 (-7))).k.toInt = -1 ∧
      (runBV 43 16 (BitVec.ofInt 64 (-5)) (BitVec.ofInt 64 (-7))).R.toNat =
        18446743913377153782) := by
  decide

end Mitaka.Algorithm4
