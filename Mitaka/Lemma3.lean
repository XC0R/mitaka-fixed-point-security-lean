/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import Mitaka.Lemma2

/-! # Lemma 3 of [ZKLY26] and the sampling-scale estimate

[ZKLY26] (ePrint 2026/2521), Lemma 3 (p. 7, l. 235-236; proof App. A.2, p. 18-19, l. 577-587):
"Using the notation of Algorithm 3, let `Σ_e = Σ_p − ÂÂ*` and `s > β(p_u)`. Then
`‖Σ_e‖₂ ≤ τ̄s²` and `‖Σ_e‖_F ≤ (2√3 n sin(π/(2n))/(1 + √5)) τ̄s²`", with (p. 6, l. 219)
`τ̄ = ((1 + √5) csc(π/(2n))/(2s p_A)) √(1 − q²/(s²β(p_u)²)) + (3 + √5) csc²(π/(2n))/(8s²p_A²)`.

`A` is the lower-triangular Cholesky root of `Σ_p` (`A A* = Σ_p`, p. 5, l. 190-198) and
`Â = ⌊p_A A⌉/p_A` (l. 191), stored as `Key.aInt = p_A Â`. The proof uses `E = A − Â`, lower
triangular with coefficients at most `1/(2p_A)` (p. 18, l. 578; `Key.AClose`, implied by the
rounding), `‖E‖₂ ≤ (1 + √5) csc(π/(2n))/(4p_A)`, `‖E‖_F ≤ √3 n/(2p_A)` (l. 581), with
`‖(1 0; 1 1)‖₂ = (1 + √5)/2` (l. 582), `‖A‖₂ ≤ √(s² − q²/β(p_u)²)` (p. 19, l. 584) and
`Σ_e = AE* + EA* − EE*` (l. 584-586).

The sampling-scale estimate (p. 19, l. 588-590):
`1 + ‖B̂⁻¹Â‖₂² = λ_max(B̂⁻¹(s² I − Σ_e)(B̂⁻¹)*) ≤ (s² + ‖Σ_e‖₂)/σ_min(B̂)² ≤ β(p_u)² s²(1 + τ̄)/q²`
(`one_add_sq_norm2_eq`, `lambdaMax_le`, `one_add_sq_norm2_le`).

`witness_hypotheses`: at `n = 1` the hypotheses of Lemmas 2 and 3 hold together
(`q = 2`, `α = √2`, `s = 3`, `A = diag(√5, √8)`, `Â = diag(2, 3)`), so they are not vacuous. -/

@[expose] public section

open LatticeCrypto
open scoped Matrix

namespace Mitaka

variable {n : ℕ}

/-- `τ̄(p_u, p_A)` [ZKLY26, p. 6, l. 219]. -/
noncomputable def tauBar (P : Params) (n : ℕ) : ℝ :=
  (1 + √5) * cscN n / (2 * P.s * P.pA) * √(1 - (P.q : ℝ) ^ 2 / (P.s ^ 2 * beta P n ^ 2)) +
    (3 + √5) * cscN n ^ 2 / (8 * P.s ^ 2 * (P.pA : ℝ) ^ 2)

/-- A `2 × 2` matrix over `K_ℝ` from coefficient vectors. -/
noncomputable def aMat (A : Fin 2 → Fin 2 → Fin n → ℝ) : KMat n :=
  Matrix.of fun i j => ofCoeffs (A i j)

/-- `‖(1 0; 1 1)‖₂ = (1 + √5)/2` [ZKLY26, p. 18, l. 582]. -/
theorem CMat.sigmaMax_lowerOnes : CMat.sigmaMax !![1, 0; 1, 1] = (1 + √5) / 2 := by
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  apply le_antisymm
  · have h := CMat.sigmaMax_le_of_lower !![(1 : ℂ), 0; 1, 1] (by simp) (ε := 1)
      fun i j => by fin_cases i <;> fin_cases j <;> simp
    rwa [mul_one] at h
  · have hvn : ∀ a b : ℝ, CMat.vecNormSq ![(a : ℂ), (b : ℂ)] = a ^ 2 + b ^ 2 := fun a b => by
      simp [CMat.vecNormSq, Complex.normSq_ofReal, sq]
    set v : Fin 2 → ℂ := ![((1 : ℝ) : ℂ), (((√5 - 1) / 2 : ℝ) : ℂ)]
    have h := CMat.vecNormSq_mulVec_le !![(1 : ℂ), 0; 1, 1] v
    have hLv' : !![(1 : ℂ), 0; 1, 1] *ᵥ v = ![((1 : ℝ) : ℂ), ((1 + (√5 - 1) / 2 : ℝ) : ℂ)] := by
      ext i
      fin_cases i <;> simp [v, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have hLv : CMat.vecNormSq (!![(1 : ℂ), 0; 1, 1] *ᵥ v) = 1 + ((1 + √5) / 2) ^ 2 := by
      rw [hLv', hvn]
      ring
    have hv : CMat.vecNormSq v = 1 + ((√5 - 1) / 2) ^ 2 := by
      rw [hvn]
      ring
    rw [hLv, hv] at h
    have hφ2 : ((1 + √5) / 2) ^ 2 * (1 + ((√5 - 1) / 2) ^ 2) = 1 + ((1 + √5) / 2) ^ 2 := by
      linear_combination (√5 ^ 2 + 3) / 16 * h5
    have hw : 0 < 1 + ((√5 - 1) / 2) ^ 2 := by positivity
    have h2 : ((1 + √5) / 2) ^ 2 ≤ CMat.sigmaMax !![(1 : ℂ), 0; 1, 1] ^ 2 :=
      le_of_mul_le_mul_right (by linarith) hw
    exact (sq_le_sq₀ (by positivity) (CMat.sigmaMax_nonneg _)).1 h2

namespace Key

/-- `Â = Key.aInt / p_A` [ZKLY26, p. 5, l. 191]. -/
noncomputable def aHatMat (P : Params) (K : Key n) : KMat n := aMat (K.aHat P)

/-- `Σ_e = Σ_p − ÂÂ*` [ZKLY26, p. 5, l. 194]. -/
noncomputable def sigmaE (P : Params) (K : Key n) : KMat n :=
  K.sigmaP P - K.aHatMat P * adjM (K.aHatMat P)

/-- `A` is a lower-triangular root of `Σ_p`: `A₀₁ = 0` and `A A* = Σ_p`
[ZKLY26, p. 5, l. 190-198]. -/
structure CholeskyRoot (P : Params) (K : Key n) (A : Fin 2 → Fin 2 → Fin n → ℝ) : Prop where
  /-- `A` is lower triangular. -/
  lower : A 0 1 = 0
  /-- `A A* = Σ_p`. -/
  mul_adjM : aMat A * adjM (aMat A) = K.sigmaP P

/-- `Â` is lower triangular and every coefficient of `A − Â` is at most `1/(2p_A)`
[ZKLY26, p. 18, l. 578]. -/
structure AClose (P : Params) (K : Key n) (A : Fin 2 → Fin 2 → Fin n → ℝ) : Prop where
  /-- `Â₀₁ = 0`. -/
  lower : K.aInt 0 1 = 0
  /-- Every coefficient of `A − Â` is at most `1/(2p_A)`. -/
  abs_sub_le : ∀ i j l, |A i j l - K.aHat P i j l| ≤ 1 / (2 * P.pA)

/-- `Â = ⌊p_A A⌉/p_A` with `A` lower triangular gives `AClose`. -/
theorem AClose.of_round (P : Params) (K : Key n) (A : Fin 2 → Fin 2 → Fin n → ℝ)
    (hpA : 0 < P.pA) (hA : A 0 1 = 0) (h : ∀ i j l, K.aInt i j l = round (P.pA * A i j l)) :
    K.AClose P A := by
  refine ⟨funext fun l => by rw [h, hA]; simp, fun i j l => ?_⟩
  have hp : (0 : ℝ) < P.pA := by exact_mod_cast hpA
  have hr := abs_sub_round ((P.pA : ℝ) * A i j l)
  rw [Key.aHat, h i j l, show A i j l - (round ((P.pA : ℝ) * A i j l) : ℝ) / P.pA =
      ((P.pA : ℝ) * A i j l - round ((P.pA : ℝ) * A i j l)) / P.pA by field_simp, abs_div,
    abs_of_pos hp, div_le_div_iff₀ hp (by positivity)]
  linarith [mul_le_mul_of_nonneg_right hr hp.le]

/-- `Σ_e = AE* + EA* − EE*` with `E = A − Â` [ZKLY26, p. 19, l. 584-585]. -/
theorem sigmaE_eq (P : Params) (K : Key n) (A : Fin 2 → Fin 2 → Fin n → ℝ)
    (hC : K.CholeskyRoot P A) :
    K.sigmaE P = aMat A * adjM (aMat A - K.aHatMat P) + (aMat A - K.aHatMat P) * adjM (aMat A) -
      (aMat A - K.aHatMat P) * adjM (aMat A - K.aHatMat P) := by
  rw [Key.sigmaE, ← hC.mul_adjM, adjM_sub]
  simp only [mul_sub, sub_mul]
  abel

private theorem embM_sub_aHatMat (P : Params) (K : Key n) (A : Fin 2 → Fin 2 → Fin n → ℝ)
    (k : Fin n) (i j : Fin 2) :
    embM k (aMat A - K.aHatMat P) i j = emb k (ofCoeffs (A i j - K.aHat P i j)) := by
  rw [embM_apply, ofCoeffs_sub]
  rfl

private theorem aHat_zero_one (P : Params) (K : Key n) (A : Fin 2 → Fin 2 → Fin n → ℝ)
    (hA : A 0 1 = 0) (hAc : K.AClose P A) : A 0 1 - K.aHat P 0 1 = 0 := by
  funext l
  simp [hA, Key.aHat, hAc.lower]

/-- `‖E‖₂ ≤ (1 + √5) csc(π/(2n))/(4p_A)` for `E = A − Â` [ZKLY26, p. 18, l. 581]. -/
theorem norm2_sub_aHatMat_le {ℓ : ℕ} (hn : n = 2 ^ ℓ) (P : Params) (K : Key n)
    (A : Fin 2 → Fin 2 → Fin n → ℝ) (hA : A 0 1 = 0) (hAc : K.AClose P A) :
    KMat.norm2 (aMat A - K.aHatMat P) ≤ (1 + √5) * cscN n / (4 * P.pA) := by
  have hn0 : 0 < n := by
    rw [hn]
    positivity
  refine KMat.norm2_le_of hn0 fun k => ?_
  have h := CMat.sigmaMax_le_of_lower (embM k (aMat A - K.aHatMat P))
    (by rw [embM_sub_aHatMat, aHat_zero_one P K A hA hAc, ← map_zero (emb k)]; simp [ofCoeffs])
    (ε := 1 / (2 * P.pA) * cscN n) fun i j => by
      rw [embM_sub_aHatMat]
      exact norm_emb_ofCoeffs_le hn k _ fun l => hAc.abs_sub_le i j l
  refine h.trans (le_of_eq ?_)
  ring

/-- `‖E‖_F ≤ √3 n/(2p_A)` for `E = A − Â` [ZKLY26, p. 18, l. 581]. -/
theorem normF_sub_aHatMat_le (P : Params) (K : Key n) (A : Fin 2 → Fin 2 → Fin n → ℝ)
    (hA : A 0 1 = 0) (hAc : K.AClose P A) :
    KMat.normF (aMat A - K.aHatMat P) ≤ √3 * n / (2 * P.pA) := by
  set b := 1 / (2 * (P.pA : ℝ))
  have hb : ∀ i j, ∑ l : Fin n, (A i j l - K.aHat P i j l) ^ 2 ≤ n * b ^ 2 := fun i j => by
    calc ∑ l : Fin n, (A i j l - K.aHat P i j l) ^ 2 ≤ ∑ _l : Fin n, b ^ 2 :=
          Finset.sum_le_sum fun l _ => by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hAc.abs_sub_le i j l) 2
      _ = n * b ^ 2 := by simp
  have h01 : ∑ l : Fin n, (A 0 1 l - K.aHat P 0 1 l) ^ 2 = 0 := by
    have := congrFun (aHat_zero_one P K A hA hAc)
    simp only [Pi.sub_apply, Pi.zero_apply] at this
    simp [this]
  have hsum : KMat.normF (aMat A - K.aHatMat P) ^ 2 =
      ∑ i : Fin 2, ∑ j : Fin 2, n * ∑ l : Fin n, (A i j l - K.aHat P i j l) ^ 2 := by
    rw [KMat.normF_sq]
    simp_rw [CMat.frob_sq, embM_sub_aHatMat]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sum_norm_sq_emb_ofCoeffs]
    rfl
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine (sq_le_sq₀ (KMat.normF_nonneg _) (by positivity)).1 ?_
  rw [hsum]
  simp only [Fin.sum_univ_two, h01, mul_zero, add_zero]
  calc (n : ℝ) * ∑ l : Fin n, (A 0 0 l - K.aHat P 0 0 l) ^ 2 +
        (n * ∑ l : Fin n, (A 1 0 l - K.aHat P 1 0 l) ^ 2 +
          n * ∑ l : Fin n, (A 1 1 l - K.aHat P 1 1 l) ^ 2)
      ≤ n * (n * b ^ 2) + (n * (n * b ^ 2) + n * (n * b ^ 2)) := by
        gcongr <;> exact hb _ _
    _ = (√3 * n / (2 * P.pA)) ^ 2 := by
        have e : (√3 * (n : ℝ) / (2 * P.pA)) ^ 2 = 3 * n ^ 2 / (2 * P.pA) ^ 2 := by
          rw [div_pow, mul_pow, h3]
        rw [e]
        simp only [b]
        ring

/-- `‖A‖₂ ≤ √(s² − q²/β(p_u)²)` [ZKLY26, p. 19, l. 584]. -/
theorem norm2_aMat_le {ℓ : ℕ} (hn : n = 2 ^ ℓ) (P : Params) (K : Key n) (u : Fin n → ℝ)
    (A : Fin 2 → Fin 2 → Fin n → ℝ) (hq : 0 < P.q) (hK : K.Annular P) (hN : K.NTRU P)
    (hu : K.GSCoeff u) (hr : K.UClose P u) (hC : K.CholeskyRoot P A) :
    KMat.norm2 (aMat A) ≤ √(P.s ^ 2 - (P.q : ℝ) ^ 2 / beta P n ^ 2) := by
  have hn0 : 0 < n := by
    rw [hn]
    positivity
  refine KMat.norm2_le_of hn0 fun k => ?_
  rw [← CMat.sigmaMax_conjTranspose]
  refine CMat.sigmaMax_le_of (Real.sqrt_nonneg _) fun v => ?_
  have hk : embM k (aMat A) * (embM k (aMat A))ᴴ =
      ((P.s ^ 2 : ℝ) : ℂ) • 1 - embM k (K.bHat P) * (embM k (K.bHat P))ᴴ := by
    rw [← embM_adjM, ← map_mul, hC.mul_adjM, Key.sigmaP, map_sub, map_mul, embM_smul_one,
      embM_adjM]
  have hv : CMat.vecNormSq ((embM k (aMat A))ᴴ *ᵥ v) =
      P.s ^ 2 * CMat.vecNormSq v - CMat.vecNormSq ((embM k (K.bHat P))ᴴ *ᵥ v) := by
    apply Complex.ofReal_injective
    rw [← CMat.star_dotProduct_mul_conjTranspose, hk, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, CMat.star_dotProduct_self,
      CMat.star_dotProduct_mul_conjTranspose, smul_eq_mul]
    push_cast
    ring
  have hlo := (vecNormSq_conjTranspose_embM_bHat hn P K u hq hK hN hu hr k v).1
  have hsq : P.s ^ 2 - (P.q : ℝ) ^ 2 / beta P n ^ 2 ≤
      √(P.s ^ 2 - (P.q : ℝ) ^ 2 / beta P n ^ 2) ^ 2 := by
    rcases le_total 0 (P.s ^ 2 - (P.q : ℝ) ^ 2 / beta P n ^ 2) with h | h
    · rw [Real.sq_sqrt h]
    · rw [Real.sqrt_eq_zero'.2 h]
      linarith
  rw [hv, ← div_pow] at *
  nlinarith [CMat.vecNormSq_nonneg v]

private theorem tauBar_mul_sq (P : Params) (n : ℕ) (hs : 0 < P.s) (hβ : 0 < beta P n) :
    tauBar P n * P.s ^ 2 = (2 * √(P.s ^ 2 - (P.q : ℝ) ^ 2 / beta P n ^ 2) +
      (1 + √5) * cscN n / (4 * P.pA)) * ((1 + √5) * cscN n / (4 * P.pA)) := by
  have hsa : √(P.s ^ 2 - (P.q : ℝ) ^ 2 / beta P n ^ 2) =
      P.s * √(1 - (P.q : ℝ) ^ 2 / (P.s ^ 2 * beta P n ^ 2)) := by
    rw [show P.s ^ 2 - (P.q : ℝ) ^ 2 / beta P n ^ 2 =
        P.s ^ 2 * (1 - (P.q : ℝ) ^ 2 / (P.s ^ 2 * beta P n ^ 2)) by
      rw [mul_sub, mul_one, mul_div_assoc', mul_div_mul_left _ _ (pow_ne_zero 2 hs.ne')],
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hs.le]
  have h6 : (1 + √5) ^ 2 = 2 * (3 + √5) := by
    linear_combination Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  by_cases hpA : (P.pA : ℝ) = 0
  · simp [tauBar, hpA]
  have he2 : ((1 + √5) * cscN n / (4 * P.pA)) ^ 2 = (3 + √5) * cscN n ^ 2 / (8 * P.pA ^ 2) := by
    rw [div_pow, mul_pow, h6]
    ring
  rw [hsa, add_mul, ← sq, he2, tauBar]
  field_simp
  ring

/-- **Lemma 3**, spectral bound [ZKLY26, p. 7, l. 236]: `‖Σ_e‖₂ ≤ τ̄s²`. -/
theorem norm2_sigmaE_le {ℓ : ℕ} (hn : n = 2 ^ ℓ) (P : Params) (K : Key n) (u : Fin n → ℝ)
    (A : Fin 2 → Fin 2 → Fin n → ℝ) (hq : 0 < P.q) (hK : K.Annular P) (hN : K.NTRU P)
    (hu : K.GSCoeff u) (hr : K.UClose P u) (hC : K.CholeskyRoot P A) (hAc : K.AClose P A)
    (hs : beta P n < P.s) :
    KMat.norm2 (K.sigmaE P) ≤ tauBar P n * P.s ^ 2 := by
  have hn0 : 0 < n := by
    rw [hn]
    positivity
  have hβ := beta_pos P n hK.one_le_alpha hq
  rw [tauBar_mul_sq P n (hβ.trans hs) hβ]
  set a := √(P.s ^ 2 - (P.q : ℝ) ^ 2 / beta P n ^ 2)
  set e := (1 + √5) * cscN n / (4 * P.pA)
  have hA := norm2_aMat_le hn P K u A hq hK hN hu hr hC
  have hE := norm2_sub_aHatMat_le hn P K A hC.lower hAc
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  refine KMat.norm2_le_of hn0 fun k => ?_
  set X := embM k (aMat A)
  set E := embM k (aMat A - K.aHatMat P)
  have hX : CMat.sigmaMax X ≤ a := (KMat.sigmaMax_le_norm2 _ k).trans hA
  have hEk : CMat.sigmaMax E ≤ e := (KMat.sigmaMax_le_norm2 _ k).trans hE
  have hX0 := CMat.sigmaMax_nonneg X
  have hE0 := CMat.sigmaMax_nonneg E
  have he0 : 0 ≤ e := hE0.trans hEk
  have hk : embM k (K.sigmaE P) = X * Eᴴ + E * Xᴴ - E * Eᴴ := by
    rw [sigmaE_eq P K A hC]
    simp only [map_sub, map_add, map_mul, embM_adjM, X, E]
  rw [hk]
  have h1 : CMat.sigmaMax (X * Eᴴ) ≤ a * e := (CMat.sigmaMax_mul_le _ _).trans (by
    rw [CMat.sigmaMax_conjTranspose]
    exact mul_le_mul hX hEk hE0 ha0)
  have h2 : CMat.sigmaMax (E * Xᴴ) ≤ e * a := (CMat.sigmaMax_mul_le _ _).trans (by
    rw [CMat.sigmaMax_conjTranspose]
    exact mul_le_mul hEk hX hX0 he0)
  have h3 : CMat.sigmaMax (E * Eᴴ) ≤ e * e := (CMat.sigmaMax_mul_le _ _).trans (by
    rw [CMat.sigmaMax_conjTranspose]
    exact mul_le_mul hEk hEk hE0 he0)
  calc CMat.sigmaMax (X * Eᴴ + E * Xᴴ - E * Eᴴ)
      ≤ CMat.sigmaMax (X * Eᴴ + E * Xᴴ) + CMat.sigmaMax (E * Eᴴ) := CMat.sigmaMax_sub_le _ _
    _ ≤ CMat.sigmaMax (X * Eᴴ) + CMat.sigmaMax (E * Xᴴ) + CMat.sigmaMax (E * Eᴴ) :=
        add_le_add (CMat.sigmaMax_add_le _ _) le_rfl
    _ ≤ (2 * a + e) * e := by nlinarith [h1, h2, h3]

/-- **Lemma 3**, Frobenius bound [ZKLY26, p. 7, l. 236]:
`‖Σ_e‖_F ≤ (2√3 n sin(π/(2n))/(1 + √5)) τ̄s²`. -/
theorem normF_sigmaE_le {ℓ : ℕ} (hn : n = 2 ^ ℓ) (P : Params) (K : Key n) (u : Fin n → ℝ)
    (A : Fin 2 → Fin 2 → Fin n → ℝ) (hq : 0 < P.q) (hK : K.Annular P) (hN : K.NTRU P)
    (hu : K.GSCoeff u) (hr : K.UClose P u) (hC : K.CholeskyRoot P A) (hAc : K.AClose P A)
    (hs : beta P n < P.s) :
    KMat.normF (K.sigmaE P) ≤
      2 * √3 * n * Real.sin (Real.pi / (2 * n)) / (1 + √5) * tauBar P n * P.s ^ 2 := by
  have hn0 : 0 < n := by
    rw [hn]
    positivity
  have hβ := beta_pos P n hK.one_le_alpha hq
  rw [mul_assoc, tauBar_mul_sq P n (hβ.trans hs) hβ]
  set a := √(P.s ^ 2 - (P.q : ℝ) ^ 2 / beta P n ^ 2)
  set e := (1 + √5) * cscN n / (4 * P.pA)
  have hA := norm2_aMat_le hn P K u A hq hK hN hu hr hC
  have hE := norm2_sub_aHatMat_le hn P K A hC.lower hAc
  have hF := normF_sub_aHatMat_le P K A hC.lower hAc
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have he0 : 0 ≤ e := (CMat.sigmaMax_nonneg _).trans
    ((KMat.sigmaMax_le_norm2 (aMat A - K.aHatMat P) ⟨0, hn0⟩).trans hE)
  have hkey : KMat.normF (K.sigmaE P) ≤
      (2 * a + e) * KMat.normF (aMat A - K.aHatMat P) := by
    refine (sq_le_sq₀ (KMat.normF_nonneg _)
      (mul_nonneg (by positivity) (KMat.normF_nonneg _))).1 ?_
    rw [mul_pow, KMat.normF_sq, KMat.normF_sq, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [← mul_pow]
    refine pow_le_pow_left₀ (CMat.frob_nonneg _) ?_ 2
    set X := embM k (aMat A)
    set E := embM k (aMat A - K.aHatMat P)
    have hX : CMat.sigmaMax X ≤ a := (KMat.sigmaMax_le_norm2 _ k).trans hA
    have hEk : CMat.sigmaMax E ≤ e := (KMat.sigmaMax_le_norm2 _ k).trans hE
    have hF0 := CMat.frob_nonneg E
    have hk : embM k (K.sigmaE P) = X * Eᴴ + E * Xᴴ - E * Eᴴ := by
      rw [sigmaE_eq P K A hC]
      simp only [map_sub, map_add, map_mul, embM_adjM, X, E]
    rw [hk]
    have h1 : CMat.frob (X * Eᴴ) ≤ a * CMat.frob E := (CMat.frob_mul_le _ _).trans (by
      rw [CMat.frob_conjTranspose]
      exact mul_le_mul_of_nonneg_right hX hF0)
    have h2 : CMat.frob (E * Xᴴ) ≤ CMat.frob E * a := (CMat.frob_mul_le' _ _).trans (by
      rw [CMat.sigmaMax_conjTranspose]
      exact mul_le_mul_of_nonneg_left hX hF0)
    have h3 : CMat.frob (E * Eᴴ) ≤ e * CMat.frob E := (CMat.frob_mul_le _ _).trans (by
      rw [CMat.frob_conjTranspose]
      exact mul_le_mul_of_nonneg_right hEk hF0)
    calc CMat.frob (X * Eᴴ + E * Xᴴ - E * Eᴴ)
        ≤ CMat.frob (X * Eᴴ + E * Xᴴ) + CMat.frob (E * Eᴴ) := CMat.frob_sub_le _ _
      _ ≤ CMat.frob (X * Eᴴ) + CMat.frob (E * Xᴴ) + CMat.frob (E * Eᴴ) :=
          add_le_add (CMat.frob_add_le _ _) le_rfl
      _ ≤ (2 * a + e) * CMat.frob E := by nlinarith [h1, h2, h3]
  refine hkey.trans ((mul_le_mul_of_nonneg_left hF (by positivity)).trans (le_of_eq ?_))
  have hsin : 0 < Real.sin (Real.pi / (2 * n)) := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  have h5 : 0 < 1 + √5 := by positivity
  by_cases hpA : (P.pA : ℝ) = 0
  · simp [e, hpA]
  simp only [e, cscN]
  field_simp
  ring

/-- The sampling-scale identity [ZKLY26, p. 19, l. 589]:
`1 + ‖B̂⁻¹Â‖₂² = λ_max(B̂⁻¹(s² I − Σ_e)(B̂⁻¹)*)`. -/
theorem one_add_sq_norm2_eq {ℓ : ℕ} (hn : n = 2 ^ ℓ) (P : Params) (K : Key n) (hq : 0 < P.q)
    (hN : K.NTRU P) :
    1 + KMat.norm2 (K.bHatInv P * K.aHatMat P) ^ 2 =
      KMat.lambdaMax
        (K.bHatInv P * (P.s ^ 2 • (1 : KMat n) - K.sigmaE P) * adjM (K.bHatInv P)) := by
  have hn0 : 0 < n := by
    rw [hn]
    positivity
  have hne : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
  have e1 : P.s ^ 2 • (1 : KMat n) - K.sigmaE P =
      K.bHat P * adjM (K.bHat P) + K.aHatMat P * adjM (K.aHatMat P) := by
    rw [Key.sigmaE, Key.sigmaP]
    abel
  have hid : K.bHatInv P * (P.s ^ 2 • (1 : KMat n) - K.sigmaE P) * adjM (K.bHatInv P) =
      (K.bHatInv P * K.aHatMat P) * adjM (K.bHatInv P * K.aHatMat P) + 1 := by
    calc K.bHatInv P * (P.s ^ 2 • (1 : KMat n) - K.sigmaE P) * adjM (K.bHatInv P)
        = (K.bHatInv P * K.bHat P) * adjM (K.bHatInv P * K.bHat P) +
            (K.bHatInv P * K.aHatMat P) * adjM (K.bHatInv P * K.aHatMat P) := by
          rw [e1, adjM_mul, adjM_mul]
          noncomm_ring
      _ = _ := by rw [bHatInv_mul_bHat P K hq hN, adjM_one, one_mul, add_comm]
  rw [hid]
  set X := K.bHatInv P * K.aHatMat P
  have hk : ∀ k, CMat.lambdaMax (embM k (X * adjM X + 1)) = 1 + CMat.sigmaMax (embM k X) ^ 2 :=
    fun k => by rw [map_add, map_mul, embM_adjM, map_one, CMat.lambdaMax_mul_conjTranspose_add_one]
  obtain ⟨k₀, hk₀⟩ := Finite.exists_max fun k : Fin n => CMat.sigmaMax (embM k X)
  have hnorm : KMat.norm2 X = CMat.sigmaMax (embM k₀ X) :=
    le_antisymm (KMat.norm2_le_of hn0 hk₀) (KMat.sigmaMax_le_norm2 X k₀)
  have hlam : KMat.lambdaMax (X * adjM X + 1) = 1 + CMat.sigmaMax (embM k₀ X) ^ 2 := by
    refine le_antisymm (KMat.lambdaMax_le_of hn0 fun k => ?_) ?_
    · rw [hk]
      have := pow_le_pow_left₀ (CMat.sigmaMax_nonneg _) (hk₀ k) 2
      linarith
    · rw [← hk]
      exact KMat.le_lambdaMax _ k₀
  rw [hnorm, hlam]

/-- [ZKLY26, p. 19, l. 590]: `λ_max(B̂⁻¹(s² I − Σ_e)(B̂⁻¹)*) ≤ (s² + ‖Σ_e‖₂)/σ_min(B̂)²`. -/
theorem lambdaMax_le {ℓ : ℕ} (hn : n = 2 ^ ℓ) (P : Params) (K : Key n) (hq : 0 < P.q)
    (hN : K.NTRU P) :
    KMat.lambdaMax (K.bHatInv P * (P.s ^ 2 • (1 : KMat n) - K.sigmaE P) * adjM (K.bHatInv P)) ≤
      (P.s ^ 2 + KMat.norm2 (K.sigmaE P)) / KMat.sigmaMin (K.bHat P) ^ 2 := by
  have hn0 : 0 < n := by
    rw [hn]
    positivity
  have hne : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
  have h1 := bHat_mul_bHatInv P K hq hN
  have h2 := bHatInv_mul_bHat P K hq hN
  have hpos : ∀ k, 0 < CMat.sigmaMin (embM k (K.bHat P)) := fun k => by
    have hBiB : embM k (K.bHatInv P) * embM k (K.bHat P) = 1 := by rw [← map_mul, h2, map_one]
    have hσ0 : 0 < CMat.sigmaMax (embM k (K.bHatInv P)) := by
      rcases (CMat.sigmaMax_nonneg (embM k (K.bHatInv P))).eq_or_lt with h | h
      · exfalso
        have := CMat.vecNormSq_mulVec_le (embM k (K.bHatInv P)) (embM k (K.bHat P) *ᵥ ![1, 0])
        rw [← h, Matrix.mulVec_mulVec, hBiB, Matrix.one_mulVec] at this
        simp [CMat.vecNormSq] at this
        linarith
      · exact h
    refine lt_of_lt_of_le (by positivity : 0 < 1 / CMat.sigmaMax (embM k (K.bHatInv P)))
      (CMat.le_sigmaMin_of (by positivity) fun v => ?_)
    have := CMat.vecNormSq_mulVec_le (embM k (K.bHatInv P)) (embM k (K.bHat P) *ᵥ v)
    rw [Matrix.mulVec_mulVec, hBiB, Matrix.one_mulVec] at this
    rw [div_pow, one_pow, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    linarith
  obtain ⟨k₀, hk₀⟩ := Finite.exists_min fun k : Fin n => CMat.sigmaMin (embM k (K.bHat P))
  have hm : 0 < KMat.sigmaMin (K.bHat P) := lt_of_lt_of_le (hpos k₀) (KMat.le_sigmaMin_of hn0 hk₀)
  refine KMat.lambdaMax_le_of hn0 fun k => ?_
  have hBBi : embM k (K.bHat P) * embM k (K.bHatInv P) = 1 := by rw [← map_mul, h1, map_one]
  have hmk : KMat.sigmaMin (K.bHat P) ≤ CMat.sigmaMin (embM k (K.bHat P)) := KMat.sigmaMin_le _ k
  have hBi : CMat.sigmaMax (embM k (K.bHatInv P)) ≤ 1 / KMat.sigmaMin (K.bHat P) :=
    CMat.sigmaMax_le_of (by positivity) fun v => by
      have h := CMat.sigmaMin_sq_mul_le (embM k (K.bHat P)) (embM k (K.bHatInv P) *ᵥ v)
      rw [Matrix.mulVec_mulVec, hBBi, Matrix.one_mulVec] at h
      have hm2 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hm.le hmk 2)
        (CMat.vecNormSq_nonneg (embM k (K.bHatInv P) *ᵥ v))
      rw [div_pow, one_pow, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
      linarith
  have hN0 : 0 ≤ KMat.norm2 (K.sigmaE P) :=
    (CMat.sigmaMax_nonneg _).trans (KMat.sigmaMax_le_norm2 _ k)
  have hM : CMat.sigmaMax (embM k (P.s ^ 2 • (1 : KMat n) - K.sigmaE P)) ≤
      P.s ^ 2 + KMat.norm2 (K.sigmaE P) := by
    rw [map_sub, embM_smul_one]
    refine (CMat.sigmaMax_sub_le _ _).trans ?_
    rw [CMat.sigmaMax_smul_one, abs_of_nonneg (sq_nonneg _)]
    exact add_le_add le_rfl (KMat.sigmaMax_le_norm2 _ k)
  rw [map_mul, map_mul, embM_adjM]
  refine (CMat.lambdaMax_le_sigmaMax _).trans ?_
  have hBi0 := CMat.sigmaMax_nonneg (embM k (K.bHatInv P))
  have hM0 := CMat.sigmaMax_nonneg (embM k (P.s ^ 2 • (1 : KMat n) - K.sigmaE P))
  calc CMat.sigmaMax (embM k (K.bHatInv P) * embM k (P.s ^ 2 • (1 : KMat n) - K.sigmaE P) *
        (embM k (K.bHatInv P))ᴴ)
      ≤ CMat.sigmaMax (embM k (K.bHatInv P)) *
          CMat.sigmaMax (embM k (P.s ^ 2 • (1 : KMat n) - K.sigmaE P)) *
            CMat.sigmaMax (embM k (K.bHatInv P)) := by
        refine (CMat.sigmaMax_mul_le _ _).trans ?_
        rw [CMat.sigmaMax_conjTranspose]
        exact mul_le_mul_of_nonneg_right (CMat.sigmaMax_mul_le _ _) hBi0
    _ ≤ 1 / KMat.sigmaMin (K.bHat P) * (P.s ^ 2 + KMat.norm2 (K.sigmaE P)) *
          (1 / KMat.sigmaMin (K.bHat P)) := by gcongr
    _ = (P.s ^ 2 + KMat.norm2 (K.sigmaE P)) / KMat.sigmaMin (K.bHat P) ^ 2 := by ring

/-- **The sampling-scale estimate** [ZKLY26, p. 19, l. 588-590]:
`1 + ‖B̂⁻¹Â‖₂² ≤ β(p_u)² s² (1 + τ̄)/q²`. -/
theorem one_add_sq_norm2_le {ℓ : ℕ} (hn : n = 2 ^ ℓ) (P : Params) (K : Key n) (u : Fin n → ℝ)
    (A : Fin 2 → Fin 2 → Fin n → ℝ) (hq : 0 < P.q) (hK : K.Annular P) (hN : K.NTRU P)
    (hu : K.GSCoeff u) (hr : K.UClose P u) (hC : K.CholeskyRoot P A) (hAc : K.AClose P A)
    (hs : beta P n < P.s) :
    1 + KMat.norm2 (K.bHatInv P * K.aHatMat P) ^ 2 ≤
      beta P n ^ 2 * P.s ^ 2 * (1 + tauBar P n) / (P.q : ℝ) ^ 2 := by
  have hn0 : 0 < n := by
    rw [hn]
    positivity
  have hβ := beta_pos P n hK.one_le_alpha hq
  have hq0 : (0 : ℝ) < P.q := by exact_mod_cast hq
  have hm := div_beta_le_sigmaMin_bHat hn P K u hq hK hN hu hr
  have hN2 := norm2_sigmaE_le hn P K u A hq hK hN hu hr hC hAc hs
  have hN0 : 0 ≤ KMat.norm2 (K.sigmaE P) :=
    (CMat.sigmaMax_nonneg _).trans (KMat.sigmaMax_le_norm2 _ ⟨0, hn0⟩)
  have hqb : 0 < (P.q : ℝ) / beta P n := by positivity
  rw [one_add_sq_norm2_eq hn P K hq hN]
  refine (lambdaMax_le hn P K hq hN).trans ?_
  calc (P.s ^ 2 + KMat.norm2 (K.sigmaE P)) / KMat.sigmaMin (K.bHat P) ^ 2
      ≤ (P.s ^ 2 + tauBar P n * P.s ^ 2) / ((P.q : ℝ) / beta P n) ^ 2 :=
        div_le_div₀ (by nlinarith [sq_nonneg P.s]) (by linarith) (by positivity)
          (pow_le_pow_left₀ hqb.le hm 2)
    _ = beta P n ^ 2 * P.s ^ 2 * (1 + tauBar P n) / (P.q : ℝ) ^ 2 := by
        field_simp

end Key

/-! ### The hypotheses of Lemmas 2 and 3 are satisfiable

At `n = 1` (`ℓ = 0`): `q = 2`, `α = √2`, `p_u = p_A = 1`, `s = 3`, `f = 1`, `g = F = 0`, `G = 2`
(`fG − gF = 2`), `u = û = 0`, `A = diag(√5, √8)` (`Σ_p = diag(5, 8)`), `Â = diag(2, 3)`. -/

/-- The parameters of the witness (`r` and `L` play no role). -/
noncomputable def Params.witness : Params where
  q := 2
  r := 1
  L := 1
  pu := 1
  pA := 1
  s := 3
  alpha := √2

/-- The key of the witness. -/
def Key.witness : Key 1 where
  f := fun _ => 1
  g := 0
  F := 0
  G := fun _ => 2
  uInt := 0
  aInt := ![![fun _ => 2, 0], ![0, fun _ => 3]]

/-- The lower-triangular root `A = diag(√5, √8)` of the witness. -/
noncomputable def witnessA : Fin 2 → Fin 2 → Fin 1 → ℝ :=
  ![![fun _ => √5, 0], ![0, fun _ => √8]]

private theorem ofCoeffs_fin_one (x : Fin 1 → ℝ) : ofCoeffs x = algebraMap ℝ (KR 1) (x 0) := by
  change mkQ ℝ 1 (∑ k : Fin 1, Polynomial.monomial k.val (x k)) = _
  rw [Fin.sum_univ_one, Fin.val_zero, Polynomial.monomial_zero_left]
  rfl

private theorem intK_fin_one (v : Fin 1 → ℤ) : intK v = algebraMap ℝ (KR 1) (v 0) := by
  rw [intK, ofCoeffs_fin_one]
  rfl

private theorem emb_intK_fin_one (k : Fin 1) (v : Fin 1 → ℤ) : emb k (intK v) = (v 0 : ℂ) := by
  rw [intK_fin_one, emb_algebraMap]
  push_cast
  rfl

/-- **Satisfiability**: at `n = 1 = 2⁰`, `Params.witness`, `Key.witness`, `u = 0` and `witnessA`
satisfy every hypothesis of `Key.norm2_sigmaE_le`, `Key.normF_sigmaE_le` and
`Key.one_add_sq_norm2_le` (hence of Lemma 2). -/
theorem witness_hypotheses :
    0 < Params.witness.q ∧ Key.witness.Annular Params.witness ∧ Key.witness.NTRU Params.witness ∧
      Key.witness.GSCoeff 0 ∧ Key.witness.UClose Params.witness 0 ∧
        Key.witness.CholeskyRoot Params.witness witnessA ∧
          Key.witness.AClose Params.witness witnessA ∧
            beta Params.witness 1 < Params.witness.s := by
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h8 : √8 ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  have h20 : 0 ≤ √2 := Real.sqrt_nonneg _
  have h50 : 0 ≤ √5 := Real.sqrt_nonneg _
  have h80 : 0 ≤ √8 := Real.sqrt_nonneg _
  have hα : 1 ≤ √2 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hcsc : cscN 1 = 1 := by simp [cscN]
  have hu : Key.witness.uHat Params.witness = 0 := by
    funext k
    simp [Key.uHat, Key.witness]
  refine ⟨by norm_num [Params.witness], ⟨hα, fun k => ?_, fun k => ?_⟩, ⟨?_⟩, ⟨?_⟩,
    ⟨fun j => ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, fun i j l => ?_⟩, ?_⟩
  · simp [emb_intK_fin_one, Key.witness, Params.witness, h2]
  · norm_num [emb_intK_fin_one, Key.witness, Params.witness, h2]
  · simpa [intK_fin_one, Key.witness, Params.witness] using map_ofNat (algebraMap ℝ (KR 1)) 2
  · simp [intK_fin_one, ofCoeffs_fin_one, Key.witness]
  · rw [hu]
    norm_num [Params.witness]
  · set ψ := algebraMap ℝ (KR 1)
    have hA : aMat witnessA = ψ.mapMatrix !![√5, 0; 0, √8] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [aMat, witnessA, ofCoeffs_fin_one, ψ]
    have hadjA : adjM (ψ.mapMatrix !![√5, 0; 0, √8]) = ψ.mapMatrix !![√5, 0; 0, √8] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [adjM, ψ, AlgHom.commutes]
    have hadjB : adjM (ψ.mapMatrix !![0, 2; -1, 0]) = ψ.mapMatrix !![0, -1; 2, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [adjM, ψ, AlgHom.commutes]
    have hB : Key.witness.bHat Params.witness = ψ.mapMatrix !![0, 2; -1, 0] := by
      rw [Key.bHat, hu]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Key.bMat, uMat, intK_fin_one, Key.witness, ψ, ofCoeffs_fin_one, Matrix.mul_apply,
          Fin.sum_univ_two]
    have hs1 : Params.witness.s ^ 2 • (1 : KMat 1) = ψ.mapMatrix ((3 : ℝ) ^ 2 • 1) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Params.witness, ψ, Algebra.algebraMap_eq_smul_one]
    rw [Key.sigmaP, hB, hA, hadjA, hadjB, hs1, ← map_mul ψ.mapMatrix, ← map_mul ψ.mapMatrix,
      ← map_sub ψ.mapMatrix]
    congr 1
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Real.mul_self_sqrt (show (0 : ℝ) ≤ 5 by norm_num),
        Real.mul_self_sqrt (show (0 : ℝ) ≤ 8 by norm_num)] <;> norm_num
  · fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp [witnessA, Key.aHat, Key.witness, Params.witness, abs_le] <;>
      constructor <;> nlinarith [h5, h50, h8, h80]
  · have hi : (√2)⁻¹ = √2 / 2 := by
      field_simp
      nlinarith [h2]
    have hX : (√2 + (√2)⁻¹) ^ 2 + √2 ^ 2 * cscN 1 ^ 2 / (4 * ((1 : ℕ) : ℝ) ^ 2) = 5 := by
      rw [hi, hcsc]
      push_cast
      linear_combination (9 / 4 + 1 / 4) * h2
    have hY : (√2 - (√2)⁻¹) ^ 2 + √2 ^ 2 * cscN 1 ^ 2 / (4 * ((1 : ℕ) : ℝ) ^ 2) = 1 := by
      rw [hi, hcsc]
      push_cast
      linear_combination (1 / 4 + 1 / 4) * h2
    change √((2 : ℕ) : ℝ) / 2 * (√((√2 + (√2)⁻¹) ^ 2 + √2 ^ 2 * cscN 1 ^ 2 /
      (4 * ((1 : ℕ) : ℝ) ^ 2)) + √((√2 - (√2)⁻¹) ^ 2 + √2 ^ 2 * cscN 1 ^ 2 /
        (4 * ((1 : ℕ) : ℝ) ^ 2))) < 3
    rw [hX, hY, Real.sqrt_one]
    push_cast
    nlinarith [h2, h5, h20, h50]

end Mitaka
