/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import Mitaka.Embedding
public import Mitaka.Sampler

/-! # Lemma 2 of [ZKLY26]: the singular values of `B̂`

[ZKLY26] (ePrint 2026/2521), Lemma 2 (p. 7, l. 232-234; proof App. A.1, p. 18, l. 566-576):
"Let `B` be the NTRU trapdoor basis satisfying the condition in Theorem 1 and `u` be its
Gram-Schmidt coefficient. Then `‖B̂‖₂ ≤ β(p_u)` and `σ_min(B̂) ≥ q/β(p_u)`. In particular,
`s² I₂ₙ − B̂B̂* ≻ 0` when `s > β(p_u)`."

Here `B = (g G; -f -F)` (p. 4, l. 137), `U_a = (1 a; 0 1)` (l. 138), the Gram-Schmidt coefficient
`u = (g*G + f*F)/(f*f + g*g)` (l. 139-141), `û = ⌊p_u u⌉/p_u` and `B̂ = B U_{-û}` (p. 5, l. 170),
`Σ_p = s² I − B̂B̂*` (l. 175), and (p. 6, l. 217) `β(p_u) = (√q/2)(√((α + α⁻¹)² + c) +
√((α − α⁻¹)² + c))` with `c = α² csc²(π/(2n))/(4p_u²)`.

The hypotheses are stated per key: condition 1 of Theorem 1 at the embeddings (`Key.Annular`), the
NTRU equation (`Key.NTRU`), `u` as a Gram-Schmidt coefficient (`Key.GSCoeff`), and the rounding
`‖u − û‖∞ ≤ 1/(2p_u)` used in the proof (p. 18, l. 567; `Key.UClose`), which `û = ⌊p_u u⌉/p_u`
implies. `n = 2^ℓ` as in §2.3 (p. 3, l. 116). `Key.NTRU.of_negacyclicConvCoeff` derives `Key.NTRU`
from the coefficient form used in `Mitaka.Sampler`; `Key.Annular.of_isPrimitiveRoot` derives
`Key.Annular` from the paper's wording ("every primitive `2n`-th root of unity").

Proof (App. A.1). At `ζ = φ_k`, with `γ = |f(ζ)|² + |g(ζ)|²` and `δ = (u − û)(ζ)`,
`|δ| ≤ csc(π/(2n))/(2p_u)` (`norm_emb_ofCoeffs_le`), and Lagrange's identity with the
Gram-Schmidt and NTRU equations gives `γ ‖φ_k(B̂)‖_F² = γ²(1 + |δ|²) + q²`; on
`[q/α², α²q]` this is at most `γ T₀` with `T₀ = traceBound` (`Key.frob_sq_embM_bHat_le`; the
convexity step left implicit at p. 18, l. 573 is the factorisation
`γT₀ − (1 + e)γ² − q² = (α²q − γ)((1 + e)γ − q/α²)`). `|det φ_k(B̂)| = q`
(`Key.normSq_det_embM_bHat`), and `β²` is the larger root of `x² − T₀x + q² = 0`
(`traceBound_le_two_mul_sq_beta`, `traceBound_mul_sq_beta_le`). -/

@[expose] public section

open LatticeCrypto
open scoped Matrix ComplexOrder

namespace Mitaka

variable {n : ℕ}

/-- `β(p_u)` [ZKLY26, p. 6, l. 217]. -/
noncomputable def beta (P : Params) (n : ℕ) : ℝ :=
  √(P.q : ℝ) / 2 *
    (√((P.alpha + P.alpha⁻¹) ^ 2 + P.alpha ^ 2 * cscN n ^ 2 / (4 * (P.pu : ℝ) ^ 2)) +
      √((P.alpha - P.alpha⁻¹) ^ 2 + P.alpha ^ 2 * cscN n ^ 2 / (4 * (P.pu : ℝ) ^ 2)))

/-- An integer coefficient vector in `K_ℝ`. -/
noncomputable def intK (v : Fin n → ℤ) : KR n := ofCoeffs (toReal v)

/-- `U_a = (1 a; 0 1)` [ZKLY26, p. 4, l. 138]. -/
noncomputable def uMat (a : KR n) : KMat n := !![1, a; 0, 1]

namespace Key

/-- `B = (g G; -f -F)` [ZKLY26, p. 4, l. 137]. -/
noncomputable def bMat (K : Key n) : KMat n :=
  !![intK K.g, intK K.G; -intK K.f, -intK K.F]

/-- `B̂ = B U_{-û}` [ZKLY26, p. 5, l. 170]. -/
noncomputable def bHat (P : Params) (K : Key n) : KMat n :=
  K.bMat * uMat (-ofCoeffs (K.uHat P))

/-- `U_û B⁻¹` with `B⁻¹ = (1/q)(-F -G; f g)` [ZKLY26, p. 4, l. 137], the matrix that `centre`
applies; it is `B̂⁻¹` under the NTRU equation (`bHatInv_mul_bHat`, `bHat_mul_bHatInv`). -/
noncomputable def bHatInv (P : Params) (K : Key n) : KMat n :=
  uMat (ofCoeffs (K.uHat P)) * ((P.q : ℝ)⁻¹ • !![-intK K.F, -intK K.G; intK K.f, intK K.g])

/-- `Σ_p = s² I − B̂B̂*` [ZKLY26, p. 5, l. 175]. -/
noncomputable def sigmaP (P : Params) (K : Key n) : KMat n :=
  P.s ^ 2 • (1 : KMat n) - K.bHat P * adjM (K.bHat P)

/-- Condition 1 of Theorem 1 [ZKLY26, p. 7, l. 225]: `α ≥ 1` and
`q/α² ≤ |f(ζ)|² + |g(ζ)|² ≤ α² q` at every embedding `ζ = ζ_n^{2k+1}`. -/
structure Annular (P : Params) (K : Key n) : Prop where
  /-- `α ≥ 1`. -/
  one_le_alpha : 1 ≤ P.alpha
  /-- The lower bound `q/α² ≤ |f(ζ)|² + |g(ζ)|²`. -/
  le_normSq : ∀ k : Fin n,
    P.q / P.alpha ^ 2 ≤ ‖emb k (intK K.f)‖ ^ 2 + ‖emb k (intK K.g)‖ ^ 2
  /-- The upper bound `|f(ζ)|² + |g(ζ)|² ≤ α² q`. -/
  normSq_le : ∀ k : Fin n,
    ‖emb k (intK K.f)‖ ^ 2 + ‖emb k (intK K.g)‖ ^ 2 ≤ P.alpha ^ 2 * P.q

/-- The NTRU equation `fG − gF = q` [ZKLY26, p. 4, l. 136]. -/
structure NTRU (P : Params) (K : Key n) : Prop where
  /-- `fG − gF = q`. -/
  eq : intK K.f * intK K.G - intK K.g * intK K.F = (P.q : KR n)

/-- `u` is the Gram-Schmidt coefficient of `B`: `u (f*f + g*g) = g*G + f*F`
[ZKLY26, p. 4, l. 140-141]. -/
structure GSCoeff (K : Key n) (u : Fin n → ℝ) : Prop where
  /-- `u (f*f + g*g) = g*G + f*F`. -/
  eq : ofCoeffs u * (conjK n (intK K.f) * intK K.f + conjK n (intK K.g) * intK K.g) =
    conjK n (intK K.g) * intK K.G + conjK n (intK K.f) * intK K.F

/-- `‖u − û‖∞ ≤ 1/(2p_u)` [ZKLY26, p. 18, l. 567]. -/
structure UClose (P : Params) (K : Key n) (u : Fin n → ℝ) : Prop where
  /-- Every coefficient of `u − û` is at most `1/(2p_u)`. -/
  abs_sub_le : ∀ j, |u j - K.uHat P j| ≤ 1 / (2 * P.pu)

/-- `û = ⌊p_u u⌉/p_u` gives `‖u − û‖∞ ≤ 1/(2p_u)`. -/
theorem UClose.of_round (P : Params) (K : Key n) (u : Fin n → ℝ) (hpu : 0 < P.pu)
    (h : ∀ j, K.uInt j = round (P.pu * u j)) : K.UClose P u := by
  refine ⟨fun j => ?_⟩
  have hp : (0 : ℝ) < P.pu := by exact_mod_cast hpu
  have hr := abs_sub_round ((P.pu : ℝ) * u j)
  rw [Key.uHat, h j, show u j - (round ((P.pu : ℝ) * u j) : ℝ) / P.pu =
      ((P.pu : ℝ) * u j - round ((P.pu : ℝ) * u j)) / P.pu by field_simp, abs_div,
    abs_of_pos hp, div_le_div_iff₀ hp (by positivity)]
  linarith [mul_le_mul_of_nonneg_right hr hp.le]

/-- `fG − gF = q` in `ℝ[X]/(Xⁿ + 1)` from the coefficient form used by `basisApply_centre`. -/
theorem NTRU.of_negacyclicConvCoeff [NeZero n] (P : Params) (K : Key n)
    (hntru : negacyclicConvCoeff K.f K.G - negacyclicConvCoeff K.g K.F = Pi.single 0 (P.q : ℤ)) :
    K.NTRU P := by
  refine ⟨?_⟩
  have h := congrArg (fun x : Fin n → ℤ => ofCoeffs (toReal x)) hntru
  simp only [toReal_sub, toReal_negacyclicConvCoeff, ofCoeffs_sub,
    ofCoeffs_negacyclicConvCoeff (NeZero.pos n), ofCoeffs_toReal_single] at h
  rw [intK, intK, intK, intK, h, Polynomial.C_eq_natCast, map_natCast]

/-- Condition 1 in the paper's wording ("for every primitive `2n`-th root of unity `ζ`",
p. 7, l. 225) gives `Annular`. -/
theorem Annular.of_isPrimitiveRoot {ℓ : ℕ} (hn : n = 2 ^ ℓ) (P : Params) (K : Key n)
    (hα : 1 ≤ P.alpha)
    (h : ∀ ζ : ℂ, IsPrimitiveRoot ζ (2 * n) →
      P.q / P.alpha ^ 2 ≤ ‖∑ j : Fin n, (K.f j : ℂ) * ζ ^ (j : ℕ)‖ ^ 2 +
          ‖∑ j : Fin n, (K.g j : ℂ) * ζ ^ (j : ℕ)‖ ^ 2 ∧
        ‖∑ j : Fin n, (K.f j : ℂ) * ζ ^ (j : ℕ)‖ ^ 2 +
          ‖∑ j : Fin n, (K.g j : ℂ) * ζ ^ (j : ℕ)‖ ^ 2 ≤ P.alpha ^ 2 * P.q) :
    K.Annular P := by
  have he : ∀ (k : Fin n) (v : Fin n → ℤ),
      emb k (intK v) = ∑ j : Fin n, (v j : ℂ) * root n k ^ (j : ℕ) := fun k v => by
    rw [intK, emb_ofCoeffs]
    simp [toReal]
  refine ⟨hα, fun k => ?_, fun k => ?_⟩
  · rw [he, he]
    exact (h _ (isPrimitiveRoot_root hn k)).1
  · rw [he, he]
    exact (h _ (isPrimitiveRoot_root hn k)).2

/-- Under the NTRU equation, `U_û B⁻¹` is a left inverse of `B̂`. -/
theorem bHatInv_mul_bHat (P : Params) (K : Key n) (hq : 0 < P.q) (hN : K.NTRU P) :
    K.bHatInv P * K.bHat P = 1 := by
  have hq' : (P.q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hc : algebraMap ℝ (KR n) (P.q : ℝ)⁻¹ * (P.q : KR n) = 1 := by
    rw [← map_natCast (algebraMap ℝ (KR n)), ← map_mul, inv_mul_cancel₀ hq', map_one]
  have h := hN.eq
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Key.bHatInv, Key.bHat, Key.bMat, uMat, Matrix.mul_apply, Fin.sum_univ_two,
      fun (r : ℝ) (x : KR n) => (Algebra.smul_def r x : r • x = algebraMap ℝ (KR n) r * x)]
  · linear_combination algebraMap ℝ (KR n) (P.q : ℝ)⁻¹ * h + hc
  · ring
  · ring
  · linear_combination algebraMap ℝ (KR n) (P.q : ℝ)⁻¹ * h + hc

/-- Under the NTRU equation, `U_û B⁻¹` is a right inverse of `B̂`. -/
theorem bHat_mul_bHatInv (P : Params) (K : Key n) (hq : 0 < P.q) (hN : K.NTRU P) :
    K.bHat P * K.bHatInv P = 1 :=
  mul_eq_one_comm.1 (bHatInv_mul_bHat P K hq hN)

end Key

/-- The bound `T₀ = q(α² + α⁻² + α² csc²(π/(2n))/(4p_u²))` on the trace of the Gram matrix of
`φ_k(B̂)` [ZKLY26, p. 18, l. 573]. -/
noncomputable def traceBound (P : Params) (n : ℕ) : ℝ :=
  P.q * (P.alpha ^ 2 + P.alpha⁻¹ ^ 2 + P.alpha ^ 2 * cscN n ^ 2 / (4 * (P.pu : ℝ) ^ 2))

private theorem beta_facts (P : Params) (n : ℕ) (hα : 1 ≤ P.alpha) (hq : 0 < P.q) :
    0 < beta P n ∧ traceBound P n ≤ 2 * beta P n ^ 2 ∧
      traceBound P n * beta P n ^ 2 ≤ (beta P n ^ 2) ^ 2 + (P.q : ℝ) ^ 2 := by
  set c := P.alpha ^ 2 * cscN n ^ 2 / (4 * (P.pu : ℝ) ^ 2) with hc
  set X := (P.alpha + P.alpha⁻¹) ^ 2 + c with hX
  set Y := (P.alpha - P.alpha⁻¹) ^ 2 + c with hY
  have hβ : beta P n = √(P.q : ℝ) / 2 * (√X + √Y) := rfl
  have hα0 : 0 < P.alpha := by linarith
  have hai : P.alpha * P.alpha⁻¹ = 1 := mul_inv_cancel₀ hα0.ne'
  have hc0 : 0 ≤ c := by positivity
  have hXY : X - Y = 4 := by
    simp only [hX, hY]
    linear_combination 4 * hai
  have hXYsum : X + Y = 2 * (P.alpha ^ 2 + P.alpha⁻¹ ^ 2 + c) := by
    simp only [hX, hY]
    ring
  have hX0 : 0 < X := by
    have : 0 < P.alpha + P.alpha⁻¹ := by positivity
    positivity
  have hY0 : 0 ≤ Y := by positivity
  have hq0 : (0 : ℝ) < P.q := by exact_mod_cast hq
  set s := √X
  set t := √Y
  set R := √(P.q : ℝ)
  have hs : s ^ 2 = X := Real.sq_sqrt hX0.le
  have ht : t ^ 2 = Y := Real.sq_sqrt hY0
  have hR : R ^ 2 = P.q := Real.sq_sqrt hq0.le
  have hs0 : 0 < s := Real.sqrt_pos.2 hX0
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have hR0 : 0 < R := Real.sqrt_pos.2 hq0
  have hT : traceBound P n = P.q * (s ^ 2 + t ^ 2) / 2 := by
    rw [traceBound, hs, ht, ← hc]
    linear_combination (-(P.q : ℝ) / 2) * hXYsum
  have hβ2 : beta P n ^ 2 = P.q * (s + t) ^ 2 / 4 := by
    rw [hβ, ← hR]
    ring
  have hst : s ^ 2 - t ^ 2 = 4 := by rw [hs, ht, hXY]
  refine ⟨by rw [hβ]; positivity, ?_, ?_⟩
  · rw [hT, hβ2]
    nlinarith [mul_nonneg hq0.le (mul_nonneg hs0.le ht0)]
  · rw [hT, hβ2]
    have e : ((P.q : ℝ) * (s + t) ^ 2 / 4) ^ 2 + (P.q : ℝ) ^ 2 -
        P.q * (s ^ 2 + t ^ 2) / 2 * (P.q * (s + t) ^ 2 / 4) =
          (P.q : ℝ) ^ 2 / 16 * (16 - (s ^ 2 - t ^ 2) ^ 2) := by ring
    rw [hst] at e
    nlinarith [e]

/-- `β(p_u) > 0`. -/
theorem beta_pos (P : Params) (n : ℕ) (hα : 1 ≤ P.alpha) (hq : 0 < P.q) : 0 < beta P n :=
  (beta_facts P n hα hq).1

/-- `T₀ ≤ 2β(p_u)²` (`β²` is the larger root of `x² − T₀ x + q² = 0`, p. 18, l. 574). -/
theorem traceBound_le_two_mul_sq_beta (P : Params) (n : ℕ) (hα : 1 ≤ P.alpha) (hq : 0 < P.q) :
    traceBound P n ≤ 2 * beta P n ^ 2 :=
  (beta_facts P n hα hq).2.1

/-- `T₀ β(p_u)² ≤ β(p_u)⁴ + q²` (with equality, p. 18, l. 574). -/
theorem traceBound_mul_sq_beta_le (P : Params) (n : ℕ) (hα : 1 ≤ P.alpha) (hq : 0 < P.q) :
    traceBound P n * beta P n ^ 2 ≤ (beta P n ^ 2) ^ 2 + (P.q : ℝ) ^ 2 :=
  (beta_facts P n hα hq).2.2

namespace Key

/-- `φ_k(B̂) = (g, g·(−û) + G; −f, −f·(−û) − F)` at the embedding `φ_k`. -/
theorem embM_bHat (P : Params) (K : Key n) (k : Fin n) :
    embM k (K.bHat P) =
      !![emb k (intK K.g), emb k (intK K.g) * emb k (-ofCoeffs (K.uHat P)) + emb k (intK K.G);
        -emb k (intK K.f),
          -emb k (intK K.f) * emb k (-ofCoeffs (K.uHat P)) - emb k (intK K.F)] := by
  rw [Key.bHat, Key.bMat, uMat, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embM_apply, sub_eq_add_neg]

/-- `|det φ_k(B̂)|² = q²` under the NTRU equation. -/
theorem normSq_det_embM_bHat (P : Params) (K : Key n) (hN : K.NTRU P) (k : Fin n) :
    Complex.normSq (embM k (K.bHat P)).det = (P.q : ℝ) ^ 2 := by
  have hdet : emb k (intK K.f) * emb k (intK K.G) - emb k (intK K.g) * emb k (intK K.F) =
      P.q := by
    rw [← map_mul, ← map_mul, ← map_sub, hN.eq, map_natCast]
  rw [embM_bHat, Matrix.det_fin_two_of,
    show emb k (intK K.g) * (-emb k (intK K.f) * emb k (-ofCoeffs (K.uHat P)) - emb k (intK K.F)) -
        (emb k (intK K.g) * emb k (-ofCoeffs (K.uHat P)) + emb k (intK K.G)) * -emb k (intK K.f) =
          (P.q : ℂ) by linear_combination hdet,
    ← Complex.ofReal_natCast, Complex.normSq_ofReal, sq]

/-- `‖φ_k(B̂)‖_F² ≤ T₀` [ZKLY26, p. 18, l. 570-573], under the hypotheses of Lemma 2. -/
theorem frob_sq_embM_bHat_le {ℓ : ℕ} (hn : n = 2 ^ ℓ) (P : Params) (K : Key n) (u : Fin n → ℝ)
    (hq : 0 < P.q) (hK : K.Annular P) (hN : K.NTRU P) (hu : K.GSCoeff u) (hr : K.UClose P u)
    (k : Fin n) : CMat.frob (embM k (K.bHat P)) ^ 2 ≤ traceBound P n := by
  set f' := emb k (intK K.f)
  set g' := emb k (intK K.g)
  set F' := emb k (intK K.F)
  set G' := emb k (intK K.G)
  set a' := emb k (-ofCoeffs (K.uHat P))
  set δ := emb k (ofCoeffs u) + a'
  have hdet : f' * G' - g' * F' = P.q := by
    simp only [f', g', F', G']
    rw [← map_mul, ← map_mul, ← map_sub, hN.eq, map_natCast]
  have hgs : emb k (ofCoeffs u) * (starRingEnd ℂ f' * f' + starRingEnd ℂ g' * g') =
      starRingEnd ℂ g' * G' + starRingEnd ℂ f' * F' := by
    have h := congrArg (emb k) hu.eq
    simpa only [map_mul, map_add, emb_conjK] using h
  set γ := Complex.normSq g' + Complex.normSq f'
  have hγC : (γ : ℂ) = starRingEnd ℂ g' * g' + starRingEnd ℂ f' * f' := by
    simp only [γ, Complex.ofReal_add, Complex.normSq_eq_conj_mul_self]
  have hinner : starRingEnd ℂ g' * (g' * a' + G') + starRingEnd ℂ (-f') * (-f' * a' - F') =
      (γ : ℂ) * δ := by
    rw [hγC, map_neg]
    linear_combination (-1 : ℂ) * hgs
  have hdet' : g' * (-f' * a' - F') - -f' * (g' * a' + G') = P.q := by linear_combination hdet
  have hlag := normSq_lagrange g' (-f') (g' * a' + G') (-f' * a' - F')
  rw [hinner, hdet', Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_neg,
    ← Complex.ofReal_natCast, Complex.normSq_ofReal] at hlag
  have hF : CMat.frob (embM k (K.bHat P)) ^ 2 = γ + (Complex.normSq (g' * a' + G') +
      Complex.normSq (-f' * a' - F')) := by
    rw [CMat.frob_sq, embM_bHat]
    simp only [Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Complex.sq_norm,
      Complex.normSq_neg, γ]
    ring
  have hδ : ‖δ‖ ≤ 1 / (2 * P.pu) * cscN n := by
    have : δ = emb k (ofCoeffs (u - K.uHat P)) := by
      rw [ofCoeffs_sub, map_sub, sub_eq_add_neg, ← map_neg]
    rw [this]
    exact norm_emb_ofCoeffs_le hn k _ fun j => hr.abs_sub_le j
  set e := cscN n ^ 2 / (4 * (P.pu : ℝ) ^ 2)
  have hD : Complex.normSq δ ≤ e := by
    rw [← Complex.sq_norm]
    calc ‖δ‖ ^ 2 ≤ (1 / (2 * P.pu) * cscN n) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hδ 2
      _ = e := by simp only [e]; ring
  have hlo : P.q / P.alpha ^ 2 ≤ γ := by
    have := hK.le_normSq k
    rw [Complex.sq_norm, Complex.sq_norm] at this
    simp only [γ]
    linarith
  have hhi : γ ≤ P.alpha ^ 2 * P.q := by
    have := hK.normSq_le k
    rw [Complex.sq_norm, Complex.sq_norm] at this
    simp only [γ]
    linarith
  have hα0 : 0 < P.alpha := by linarith [hK.one_le_alpha]
  have hq0 : (0 : ℝ) < P.q := by exact_mod_cast hq
  have hγ0 : 0 < γ := lt_of_lt_of_le (by positivity) hlo
  set A := P.alpha ^ 2
  set Ai := P.alpha⁻¹ ^ 2
  have hAAi : A * Ai = 1 := by
    simp only [A, Ai]
    rw [← mul_pow, mul_inv_cancel₀ hα0.ne', one_pow]
  have hlo' : P.q * Ai ≤ γ := by
    simpa only [Ai, inv_pow, div_eq_mul_inv] using hlo
  have he0 : 0 ≤ e := by positivity
  have hT0 : traceBound P n = P.q * (A + Ai + A * e) := by
    simp only [traceBound, A, Ai, e]
    ring
  have hfac : γ * traceBound P n - (1 + e) * γ ^ 2 - (P.q : ℝ) ^ 2 =
      (A * P.q - γ) * ((1 + e) * γ - P.q * Ai) := by
    rw [hT0]
    linear_combination (P.q : ℝ) ^ 2 * hAAi
  have hprod : 0 ≤ (A * P.q - γ) * ((1 + e) * γ - P.q * Ai) :=
    mul_nonneg (by linarith) (by nlinarith [mul_nonneg he0 hγ0.le, hlo'])
  have hγD : γ ^ 2 * Complex.normSq δ ≤ γ ^ 2 * e := mul_le_mul_of_nonneg_left hD (sq_nonneg γ)
  rw [hF]
  refine le_of_mul_le_mul_left ?_ hγ0
  nlinarith [hfac, hprod, hγD, hlag]

private theorem embM_bHat_bounds {ℓ : ℕ} (hn : n = 2 ^ ℓ) (P : Params) (K : Key n)
    (u : Fin n → ℝ) (hq : 0 < P.q) (hK : K.Annular P) (hN : K.NTRU P) (hu : K.GSCoeff u)
    (hr : K.UClose P u) (k : Fin n) :
    CMat.frob (embM k (K.bHat P)) ^ 2 ≤ traceBound P n ∧ traceBound P n ≤ 2 * beta P n ^ 2 ∧
      traceBound P n * beta P n ^ 2 ≤
        (beta P n ^ 2) ^ 2 + Complex.normSq (embM k (K.bHat P)).det := by
  rw [normSq_det_embM_bHat P K hN k]
  exact ⟨frob_sq_embM_bHat_le hn P K u hq hK hN hu hr k,
    traceBound_le_two_mul_sq_beta P n hK.one_le_alpha hq,
    traceBound_mul_sq_beta_le P n hK.one_le_alpha hq⟩

/-- **Lemma 2**, first bound [ZKLY26, p. 7, l. 233]: `‖B̂‖₂ ≤ β(p_u)`. -/
theorem norm2_bHat_le {ℓ : ℕ} (hn : n = 2 ^ ℓ) (P : Params) (K : Key n) (u : Fin n → ℝ)
    (hq : 0 < P.q) (hK : K.Annular P) (hN : K.NTRU P) (hu : K.GSCoeff u) (hr : K.UClose P u) :
    KMat.norm2 (K.bHat P) ≤ beta P n := by
  have hn0 : 0 < n := by
    rw [hn]
    positivity
  have hβ := beta_pos P n hK.one_le_alpha hq
  refine KMat.norm2_le_of hn0 fun k => CMat.sigmaMax_le_of hβ.le fun v => ?_
  obtain ⟨h1, h2, h3⟩ := embM_bHat_bounds hn P K u hq hK hN hu hr k
  exact CMat.vecNormSq_mulVec_le_of_frob _ h1 h2 h3 v

/-- **Lemma 2**, second bound [ZKLY26, p. 7, l. 233]: `σ_min(B̂) ≥ q/β(p_u)`. -/
theorem div_beta_le_sigmaMin_bHat {ℓ : ℕ} (hn : n = 2 ^ ℓ) (P : Params) (K : Key n)
    (u : Fin n → ℝ) (hq : 0 < P.q) (hK : K.Annular P) (hN : K.NTRU P) (hu : K.GSCoeff u)
    (hr : K.UClose P u) :
    P.q / beta P n ≤ KMat.sigmaMin (K.bHat P) := by
  have hn0 : 0 < n := by
    rw [hn]
    positivity
  have hβ := beta_pos P n hK.one_le_alpha hq
  refine KMat.le_sigmaMin_of hn0 fun k => CMat.le_sigmaMin_of (by positivity) fun v => ?_
  obtain ⟨h1, h2, h3⟩ := embM_bHat_bounds hn P K u hq hK hN hu hr k
  have h := CMat.normSq_det_mul_le_of_frob _ h1 h2 h3 v
  rw [normSq_det_embM_bHat P K hN k] at h
  rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  linarith

/-- Per embedding, under the hypotheses of Lemma 2: `(q/β)² ‖v‖² ≤ ‖φ_k(B̂)* v‖² ≤ β² ‖v‖²`. -/
theorem vecNormSq_conjTranspose_embM_bHat {ℓ : ℕ} (hn : n = 2 ^ ℓ) (P : Params) (K : Key n)
    (u : Fin n → ℝ) (hq : 0 < P.q) (hK : K.Annular P) (hN : K.NTRU P) (hu : K.GSCoeff u)
    (hr : K.UClose P u) (k : Fin n) (v : Fin 2 → ℂ) :
    (P.q / beta P n) ^ 2 * CMat.vecNormSq v ≤ CMat.vecNormSq ((embM k (K.bHat P))ᴴ *ᵥ v) ∧
      CMat.vecNormSq ((embM k (K.bHat P))ᴴ *ᵥ v) ≤ beta P n ^ 2 * CMat.vecNormSq v := by
  have hβ := beta_pos P n hK.one_le_alpha hq
  obtain ⟨h1, h2, h3⟩ := embM_bHat_bounds hn P K u hq hK hN hu hr k
  rw [← CMat.frob_conjTranspose] at h1
  rw [show Complex.normSq (embM k (K.bHat P)).det =
      Complex.normSq (embM k (K.bHat P))ᴴ.det by
    rw [Matrix.det_conjTranspose, Complex.star_def, Complex.normSq_conj]] at h3
  refine ⟨?_, CMat.vecNormSq_mulVec_le_of_frob _ h1 h2 h3 v⟩
  have h := CMat.normSq_det_mul_le_of_frob _ h1 h2 h3 v
  rw [Matrix.det_conjTranspose, Complex.star_def, Complex.normSq_conj,
    normSq_det_embM_bHat P K hN k] at h
  rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  linarith

/-- **Lemma 2**, last claim [ZKLY26, p. 7, l. 234]: `Σ_p = s² I − B̂B̂* ≻ 0` when `s > β(p_u)`. -/
theorem posDef_sigmaP {ℓ : ℕ} (hn : n = 2 ^ ℓ) (P : Params) (K : Key n) (u : Fin n → ℝ)
    (hq : 0 < P.q) (hK : K.Annular P) (hN : K.NTRU P) (hu : K.GSCoeff u) (hr : K.UClose P u)
    (hs : beta P n < P.s) :
    KMat.PosDef (K.sigmaP P) := by
  have hn0 : n ≠ 0 := by
    rw [hn]
    positivity
  have hβ := beta_pos P n hK.one_le_alpha hq
  refine ⟨?_, fun k => ?_⟩
  · rw [Key.sigmaP, adjM_sub, adjM_smul_one, adjM_mul, adjM_adjM hn0]
  · have hk : embM k (K.sigmaP P) =
        ((P.s ^ 2 : ℝ) : ℂ) • 1 - embM k (K.bHat P) * (embM k (K.bHat P))ᴴ := by
      rw [Key.sigmaP, map_sub, map_mul, embM_smul_one, embM_adjM]
    rw [hk, Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x hx => ?_⟩
    · simp [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
        Matrix.conjTranspose_mul]
    · rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
        dotProduct_smul, CMat.star_dotProduct_self, CMat.star_dotProduct_mul_conjTranspose,
        smul_eq_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.zero_lt_real]
      have h := (vecNormSq_conjTranspose_embM_bHat hn P K u hq hK hN hu hr k x).2
      have hx0 := CMat.vecNormSq_pos hx
      have hs2 : beta P n ^ 2 < P.s ^ 2 := pow_lt_pow_left₀ hs hβ.le two_ne_zero
      nlinarith [mul_lt_mul_of_pos_right hs2 hx0, h]

end Key

end Mitaka
