/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.NumTail
public import FalconPrecision.ThetaTail
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mitaka.LatticeGaussian

/-! # The smoothing parameter and Lemma 1 of [ZKLY26] ([Pei10, Lemma 2.4])

[ZKLY26] (ePrint 2026/2521), p. 3, l. 103-107: "Let `η_ϵ(L) = min{s > 0 : ρ_{1/s}(L*) ≤ 1 + ϵ}`
be the smoothing parameter of a lattice `L` for `ϵ > 0` [MR04]. For an invertible `M`, we write
`M ≥ η_ϵ(L)` if `η_ϵ(M⁻¹L) ≤ 1`. In particular, `MMᵗ ⪰ s²I` and `s ≥ η_ϵ(L)` imply
`M ≥ η_ϵ(L)`." **Lemma 1** ([Pei10, Lemma 2.4]): "Let `0 < ϵ < 1` and `M ≥ η_ϵ(L)`. Then, for
every `c ∈ span(L)`, `ρ_{M,c}(L) ∈ [(1 − ϵ)/(1 + ϵ), 1] ρ_M(L)`."

Here `L = L(B)` for an invertible `B`, so `span(L) = ℝ^m` and `M⁻¹L(B) = L(M⁻¹B)`
(`points_inv_mul`).

* `smoothingParam ϵ B = η_ϵ(L(B))`, the infimum of the paper's set; `smoothingParam_le_iff`: for
  `s > 0`, `η_ϵ(L(B)) ≤ s` iff `ρ_{1/s}(L(B)*) ≤ 1 + ϵ` (so the minimum is attained and the bounds
  below are not vacuous); `smoothingParam_pos`: `η_ϵ(L(B)) > 0` for `m ≥ 1`.
* `GeSmoothing ϵ M B` is `M ≥ η_ϵ(L(B))`; `geSmoothing_iff`: it is `ρ(MᵗL(B)*) ≤ 1 + ϵ`
  ([Pei10, Definition 2.3]); `geSmoothing_of_posSemidef` is l. 105.
* `rhoSum_eq_tsum_dual`, `rhoSum_eq_tsum_dual_real`: Poisson summation over `L(B)`,
  `ρ_{M,c}(L(B)) = (|det M|/|det B|) Σ_{w ∈ L(B)*} e^{−π‖Mᵗw‖²} e^{2πi⟨w,c⟩}`.
* `rhoSum_one_mem_Icc` (`L = ℤ^m`) and `rhoSum_mem_Icc` (`L = L(B)`): Lemma 1.
* `smoothingParam_one_le`: `η_ϵ(ℤ^m) ≤ √(ln(2m(1 + 1/ϵ))/π)` ([Pei10, Lemma 2.5], a special
  case of [MR04, Lemma 3.3]). `smoothingParam_one_le_iff_tail`: the exact form
  `η_ϵ(ℤ^m) ≤ s ⇔ (1 + T(s/√(2π)))^m ≤ 1 + ϵ` with the theta tail `T` of
  `FalconPrecision.ThetaTail.tail`. -/

@[expose] public section

open Real
open scoped Matrix

namespace Mitaka.LatticeGaussian

variable {m : ℕ}

/-- The smoothing parameter `η_ϵ(L(B)) = min{s > 0 : ρ_{1/s}(L(B)*) ≤ 1 + ϵ}`
[ZKLY26, p. 3, l. 103], with `L(B)* = L((B⁻¹)ᵗ)` (`points_dualBasis`). It is meaningful for
`B.det ≠ 0` and `0 < ϵ`: `smoothingParam ϵ B = 0` for singular `B` or `ϵ ≤ 0` (the set is then
`∅` or `(0, ∞)`, and `sInf ∅ = 0`). -/
noncomputable def smoothingParam (ϵ : ℝ) (B : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  sInf {s : ℝ | 0 < s ∧ rhoSum (dualBasis B) (s⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)) 0 ≤ 1 + ϵ}

/-- `M ≥ η_ϵ(L(B))`: `η_ϵ(M⁻¹L(B)) ≤ 1` [ZKLY26, p. 3, l. 104]. It holds for every singular `M`
(`M⁻¹ = 0`, so `smoothingParam ϵ (M⁻¹ * B) = 0`); users carry `M.det ≠ 0` and `0 < ϵ`. -/
structure GeSmoothing (ϵ : ℝ) (M B : Matrix (Fin m) (Fin m) ℝ) : Prop where
  /-- `η_ϵ(L(M⁻¹B)) ≤ 1`. -/
  le : smoothingParam ϵ (M⁻¹ * B) ≤ 1

/-- `M⁻¹L(B) = L(M⁻¹B)`. -/
theorem points_inv_mul (M B : Matrix (Fin m) (Fin m) ℝ) :
    points (M⁻¹ * B) = (fun x => M⁻¹ *ᵥ x) '' points B := by
  ext x
  simp [points, Matrix.mulVec_mulVec]

/-- `det(s⁻¹ I) ≠ 0` for `s ≠ 0`. -/
theorem det_inv_smul_one_ne_zero {s : ℝ} (hs : s ≠ 0) :
    (s⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)).det ≠ 0 := by
  rw [Matrix.det_smul, Matrix.det_one, mul_one]
  exact pow_ne_zero _ (inv_ne_zero hs)

private theorem rho_one_zero (x : Fin m → ℝ) :
    rho (1 : Matrix (Fin m) (Fin m) ℝ) 0 x = Real.exp (-π * sqNorm x) := by
  rw [rho, inv_one, Matrix.one_mulVec, sub_zero]

/-- `ρ_{1/s}(x) = exp(−πs²‖x‖²)`. -/
theorem rho_inv_smul_one {s : ℝ} (hs : s ≠ 0) (x : Fin m → ℝ) :
    rho (s⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)) 0 x = Real.exp (-π * s ^ 2 * sqNorm x) := by
  rw [rho_smul_one (inv_ne_zero hs), sub_zero]
  congr 1
  field_simp

/-- `ρ_{1/s}(L(D)) = Σ_y exp(−πs²‖Dy‖²)`. -/
theorem rhoSum_inv_smul_one {s : ℝ} (hs : s ≠ 0) (D : Matrix (Fin m) (Fin m) ℝ) :
    rhoSum D (s⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)) 0 =
      ∑' y : Fin m → ℤ, Real.exp (-π * s ^ 2 * sqNorm (D *ᵥ ofInt y)) :=
  tsum_congr fun _ => rho_inv_smul_one hs _

/-- The weights `exp(−πs²‖Dy‖²)`, `y ∈ ℤ^m`, are summable for invertible `D`, `s ≠ 0`. -/
theorem summable_exp_sqNorm {D : Matrix (Fin m) (Fin m) ℝ} (hD : D.det ≠ 0) {s : ℝ}
    (hs : s ≠ 0) :
    Summable fun y : Fin m → ℤ => Real.exp (-π * s ^ 2 * sqNorm (D *ᵥ ofInt y)) :=
  (summable_rho hD (det_inv_smul_one_ne_zero hs) 0).congr fun _ => rho_inv_smul_one hs _

/-- `det (B⁻¹)ᵗ ≠ 0`. -/
theorem det_dualBasis_ne_zero {B : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0) :
    (dualBasis B).det ≠ 0 := by
  rw [dualBasis, Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact inv_ne_zero hB

/-- `ρ_{1/s}(L(B)*)` summed over the set `L(B)*` of the paper. -/
theorem rhoSum_dualBasis_eq_tsum_dual {B : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0) {s : ℝ}
    (hs : s ≠ 0) :
    rhoSum (dualBasis B) (s⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)) 0 =
      ∑' y : dual (points B), Real.exp (-π * s ^ 2 * sqNorm (y : Fin m → ℝ)) := by
  rw [← points_dualBasis hB, rhoSum_eq_tsum_points (det_dualBasis_ne_zero hB)]
  exact tsum_congr fun _ => rho_inv_smul_one hs _

/-- The terms of Poisson summation over `L(B)`. -/
private theorem poisson_terms {B M : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0)
    (hM : M.det ≠ 0) (c : Fin m → ℝ) :
    (B⁻¹ * M * (B⁻¹ * M)ᵀ).PosDef ∧
    (∀ z : Fin m → ℤ, rho M c (B *ᵥ ofInt z) =
      Real.exp (-π * quadForm (B⁻¹ * M * (B⁻¹ * M)ᵀ)⁻¹ (ofInt z - B⁻¹ *ᵥ c))) ∧
    (∀ y : Fin m → ℤ, quadForm (B⁻¹ * M * (B⁻¹ * M)ᵀ) (ofInt y) =
      sqNorm (Mᵀ *ᵥ (dualBasis B *ᵥ ofInt y))) ∧
    (∀ y : Fin m → ℤ, ofInt y ⬝ᵥ (B⁻¹ *ᵥ c) = (dualBasis B *ᵥ ofInt y) ⬝ᵥ c) ∧
    √(B⁻¹ * M * (B⁻¹ * M)ᵀ).det = |M.det| / |B.det| := by
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.2 hB
  have hN : (B⁻¹ * M).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact mul_ne_zero (inv_ne_zero hB) hM
  have hNt : ((B⁻¹ * M)ᵀ).det ≠ 0 := by rwa [Matrix.det_transpose]
  refine ⟨?_, fun z => ?_, fun y => ?_, fun y => ?_, ?_⟩
  · rw [show B⁻¹ * M * (B⁻¹ * M)ᵀ = ((B⁻¹ * M)ᵀ)ᴴ * (B⁻¹ * M)ᵀ by simp]
    exact Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_iff_isUnit.2
      ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hNt)))
  · rw [← rho_eq_exp_quadForm, rho, rho, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hBu,
      ← Matrix.mulVec_mulVec, Matrix.mulVec_sub B, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hBu, Matrix.one_mulVec]
  · rw [show B⁻¹ * M * (B⁻¹ * M)ᵀ = (B⁻¹ * M)ᵀᵀ * (B⁻¹ * M)ᵀ by rw [Matrix.transpose_transpose],
      quadForm_transpose_mul_self, Matrix.transpose_mul, ← Matrix.mulVec_mulVec, dualBasis]
  · rw [Matrix.dotProduct_mulVec, dualBasis, Matrix.mulVec_transpose]
  · rw [Matrix.det_mul, Matrix.det_transpose, ← sq, Real.sqrt_sq_eq_abs, Matrix.det_mul,
      Matrix.det_nonsing_inv, Ring.inverse_eq_inv', abs_mul, abs_inv]
    ring

/-- **Poisson summation over `L(B)`** [ZKLY26, p. 8, l. 248-249]:
`ρ_{M,c}(L(B)) = (|det M|/|det B|) Σ_{w ∈ L(B)*} e^{−π‖Mᵗw‖²} e^{2πi⟨w,c⟩}`, with
`w = (B⁻¹)ᵗ y`, `y ∈ ℤ^m`. -/
theorem rhoSum_eq_tsum_dual {B M : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0) (hM : M.det ≠ 0)
    (c : Fin m → ℝ) :
    (rhoSum B M c : ℂ) = ((|M.det| / |B.det| : ℝ) : ℂ) * ∑' y : Fin m → ℤ,
      (Real.exp (-π * sqNorm (Mᵀ *ᵥ (dualBasis B *ᵥ ofInt y))) : ℂ) *
        Complex.exp (2 * π * Complex.I * ((dualBasis B *ᵥ ofInt y) ⬝ᵥ c : ℝ)) := by
  obtain ⟨hV, hl, hq, hp, hdet⟩ := poisson_terms hB hM c
  rw [rhoSum, Complex.ofReal_tsum, tsum_congr fun z => congrArg _ (hl z),
    tsum_exp_neg_quadForm_eq hV, hdet]
  congr 1
  exact tsum_congr fun y => by rw [hq, hp]

/-- Real form of `rhoSum_eq_tsum_dual`. -/
theorem rhoSum_eq_tsum_dual_real {B M : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0)
    (hM : M.det ≠ 0) (c : Fin m → ℝ) :
    rhoSum B M c = |M.det| / |B.det| * ∑' y : Fin m → ℤ,
      Real.exp (-π * sqNorm (Mᵀ *ᵥ (dualBasis B *ᵥ ofInt y))) *
        Real.cos (2 * π * ((dualBasis B *ᵥ ofInt y) ⬝ᵥ c)) := by
  obtain ⟨hV, hl, hq, hp, hdet⟩ := poisson_terms hB hM c
  rw [rhoSum, tsum_congr hl, tsum_exp_neg_quadForm_eq_real hV, hdet]
  congr 1
  exact tsum_congr fun y => by rw [hq, hp]

/-- The dual weights `e^{−π‖Mᵗw‖²}`, `w ∈ L(B)*`. -/
private theorem summable_dual_weight {B M : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0)
    (hM : M.det ≠ 0) :
    Summable fun y : Fin m → ℤ => Real.exp (-π * sqNorm (Mᵀ *ᵥ (dualBasis B *ᵥ ofInt y))) := by
  have h : (Mᵀ * dualBasis B).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero hM (det_dualBasis_ne_zero hB)
  refine (summable_rho (M := (1 : Matrix (Fin m) (Fin m) ℝ)) h (by simp) 0).congr fun y => ?_
  rw [rho_one_zero, Matrix.mulVec_mulVec]

private theorem rhoSum_dual_weight (B M : Matrix (Fin m) (Fin m) ℝ) :
    rhoSum (Mᵀ * dualBasis B) (1 : Matrix (Fin m) (Fin m) ℝ) 0 =
      ∑' y : Fin m → ℤ, Real.exp (-π * sqNorm (Mᵀ *ᵥ (dualBasis B *ᵥ ofInt y))) :=
  tsum_congr fun y => by rw [rho_one_zero, Matrix.mulVec_mulVec]

/-- `ρ_{M,c}(L(B)) ≤ ρ_M(L(B))` for every centre (the upper half of Lemma 1, which needs no
smoothing). -/
theorem rhoSum_le_rhoSum_zero {B M : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0)
    (hM : M.det ≠ 0) (c : Fin m → ℝ) : rhoSum B M c ≤ rhoSum B M 0 := by
  have hs := summable_dual_weight hB hM
  rw [rhoSum_eq_tsum_dual_real hB hM c, rhoSum_eq_tsum_dual_real hB hM 0]
  refine mul_le_mul_of_nonneg_left (Summable.tsum_le_tsum (fun y => ?_) ?_ ?_) (by positivity)
  · rw [dotProduct_zero, mul_zero, Real.cos_zero, mul_one]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.cos_le_one _)
  · exact Summable.of_norm_bounded hs fun y => by
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)
  · simpa using hs

private theorem exp_le_exp_of_sq_le {s t q : ℝ} (hq : 0 ≤ q) (h : s ^ 2 ≤ t ^ 2) :
    Real.exp (-π * t ^ 2 * q) ≤ Real.exp (-π * s ^ 2 * q) := by
  refine Real.exp_le_exp.2 ?_
  have := mul_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.2 h)) hq
  linarith

private theorem rhoSum_dualBasis_anti {B : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0) {s t : ℝ}
    (hs : 0 < s) (hst : s ≤ t) :
    rhoSum (dualBasis B) (t⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)) 0 ≤
      rhoSum (dualBasis B) (s⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)) 0 := by
  have ht : 0 < t := hs.trans_le hst
  rw [rhoSum_inv_smul_one ht.ne', rhoSum_inv_smul_one hs.ne']
  exact Summable.tsum_le_tsum
    (fun y => exp_le_exp_of_sq_le (sqNorm_nonneg _) (pow_le_pow_left₀ hs.le hst 2))
    (summable_exp_sqNorm (det_dualBasis_ne_zero hB) ht.ne')
    (summable_exp_sqNorm (det_dualBasis_ne_zero hB) hs.ne')

private theorem exists_rhoSum_dualBasis_le {B : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0)
    {ϵ : ℝ} (hϵ : 0 < ϵ) :
    ∃ s : ℝ, 0 < s ∧ rhoSum (dualBasis B) (s⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)) 0 ≤ 1 + ϵ := by
  have hD := det_dualBasis_ne_zero hB
  have hlim : Filter.Tendsto
      (fun s : ℝ => ∑' y : Fin m → ℤ, Real.exp (-π * s ^ 2 * sqNorm (dualBasis B *ᵥ ofInt y)))
      Filter.atTop (nhds (∑' y : Fin m → ℤ, if y = 0 then (1 : ℝ) else 0)) := by
    refine tendsto_tsum_of_dominated_convergence (summable_exp_sqNorm hD one_ne_zero)
      (fun y => ?_) ?_
    · by_cases hy : y = 0
      · subst hy
        simp [ofInt_zero, sqNorm]
      · have hq : 0 < sqNorm (dualBasis B *ᵥ ofInt y) :=
          sqNorm_pos fun h => hy (injective_mulVec_ofInt hD (h.trans (by
            change (0 : Fin m → ℝ) = dualBasis B *ᵥ ofInt 0
            rw [ofInt_zero, Matrix.mulVec_zero])))
        simp only [hy, ↓reduceIte]
        refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp
          ((Filter.tendsto_pow_atTop two_ne_zero).const_mul_atTop
            (mul_pos Real.pi_pos hq))).congr fun s => ?_
        simp only [Function.comp]
        ring_nf
    · filter_upwards [Filter.eventually_ge_atTop 1] with s hs y
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact exp_le_exp_of_sq_le (sqNorm_nonneg _) (pow_le_pow_left₀ zero_le_one hs 2)
  rw [tsum_ite_eq] at hlim
  obtain ⟨s, hs1, hs2⟩ := ((hlim.eventually (gt_mem_nhds (by linarith : (1 : ℝ) < 1 + ϵ))).and
    (Filter.eventually_gt_atTop 0)).exists
  exact ⟨s, hs2, by rw [rhoSum_inv_smul_one hs2.ne']; exact hs1.le⟩

/-- For `s > 0`, `η_ϵ(L(B)) ≤ s` iff `ρ_{1/s}(L(B)*) ≤ 1 + ϵ`. -/
theorem smoothingParam_le_iff {B : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0) {ϵ s : ℝ}
    (hϵ : 0 < ϵ) (hs : 0 < s) :
    smoothingParam ϵ B ≤ s ↔
      rhoSum (dualBasis B) (s⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)) 0 ≤ 1 + ϵ := by
  have hbdd : BddBelow {s : ℝ | 0 < s ∧
      rhoSum (dualBasis B) (s⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)) 0 ≤ 1 + ϵ} :=
    ⟨0, fun t ht => ht.1.le⟩
  refine ⟨fun hη => ?_, fun h => csInf_le hbdd ⟨hs, h⟩⟩
  by_contra hgt
  replace hgt := not_le.1 hgt
  have hD := det_dualBasis_ne_zero hB
  have hc : ContinuousWithinAt
      (fun s : ℝ => ∑' y : Fin m → ℤ, Real.exp (-π * s ^ 2 * sqNorm (dualBasis B *ᵥ ofInt y)))
      (Set.Ici s) s :=
    continuousOn_tsum (fun y => (by fun_prop : Continuous fun s : ℝ =>
        Real.exp (-π * s ^ 2 * sqNorm (dualBasis B *ᵥ ofInt y))).continuousOn)
      (summable_exp_sqNorm hD hs.ne') (fun y t ht => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact exp_le_exp_of_sq_le (sqNorm_nonneg _) (pow_le_pow_left₀ hs.le ht 2))
      s (Set.mem_Ici.2 le_rfl)
  rw [rhoSum_inv_smul_one hs.ne'] at hgt
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (hc.eventually_const_lt hgt)
  obtain ⟨s₁, hs₁⟩ := exists_rhoSum_dualBasis_le hB hϵ
  obtain ⟨t, htT, htu⟩ := exists_lt_of_csInf_lt ⟨s₁, hs₁⟩ (hη.trans_lt hu)
  rcases le_or_gt s t with hst | hst
  · have h1 := hsub ⟨hst, htu⟩
    have h2 := htT.2
    rw [rhoSum_inv_smul_one htT.1.ne'] at h2
    exact absurd h2 (not_le.2 h1)
  · have h1 := (rhoSum_dualBasis_anti hB htT.1 hst.le).trans htT.2
    rw [rhoSum_inv_smul_one hs.ne'] at h1
    linarith

private theorem le_rhoSum_dualBasis {D : Matrix (Fin m) (Fin m) ℝ} (hD : D.det ≠ 0) {s : ℝ}
    (hs : 0 < s) :
    s⁻¹ ^ m / |D.det| ≤ rhoSum D (s⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)) 0 := by
  have hM := det_inv_smul_one_ne_zero (m := m) hs.ne'
  rw [rhoSum_eq_tsum_dual_real hD hM 0]
  simp only [dotProduct_zero, mul_zero, Real.cos_zero, mul_one]
  have h1 : 1 ≤ ∑' y : Fin m → ℤ, Real.exp (-π * sqNorm ((s⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ))ᵀ *ᵥ
      (dualBasis D *ᵥ ofInt y))) := by
    have := (summable_dual_weight hD hM).le_tsum 0 fun _ _ => (Real.exp_pos _).le
    simpa [ofInt_zero, sqNorm] using this
  rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, abs_pow,
    abs_of_pos (inv_pos.2 hs)]
  exact le_mul_of_one_le_right (div_nonneg (pow_nonneg (inv_nonneg.2 hs.le) _) (abs_nonneg _)) h1

/-- `η_ϵ(L(B)) > 0` in dimension `m ≥ 1`. -/
theorem smoothingParam_pos (hm : 0 < m) {B : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0)
    {ϵ : ℝ} (hϵ : 0 < ϵ) : 0 < smoothingParam ϵ B := by
  have hD := det_dualBasis_ne_zero hB
  have hd : 0 < |(dualBasis B).det| := abs_pos.2 hD
  set a := 2 * |(dualBasis B).det| * (1 + ϵ) with ha
  have ha0 : 0 < a := by positivity
  refine lt_of_lt_of_le (lt_min one_pos (inv_pos.2 ha0)) (le_csInf ?_ fun t ht => ?_)
  · obtain ⟨s, hs⟩ := exists_rhoSum_dualBasis_le hB hϵ
    exact ⟨s, hs⟩
  · by_contra hlt
    replace hlt := not_le.1 hlt
    have ht1 : t < 1 := hlt.trans_le (min_le_left _ _)
    have hta : a < t⁻¹ := (lt_inv_comm₀ ha0 ht.1).2 (hlt.trans_le (min_le_right _ _))
    have h1 : t⁻¹ ≤ t⁻¹ ^ m :=
      le_self_pow₀ (one_le_inv₀ ht.1 |>.2 ht1.le) hm.ne'
    have h2 := (le_rhoSum_dualBasis hD ht.1).trans ht.2
    have h3 : t⁻¹ / |(dualBasis B).det| ≤ 1 + ϵ :=
      (div_le_div_of_nonneg_right h1 hd.le).trans h2
    rw [div_le_iff₀ hd] at h3
    linarith [mul_pos hd hϵ]

/-- `η_ϵ` is antitone in `ϵ`. -/
theorem smoothingParam_anti {B : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0) {ϵ ϵ' : ℝ}
    (hϵ : 0 < ϵ) (h : ϵ ≤ ϵ') : smoothingParam ϵ' B ≤ smoothingParam ϵ B :=
  csInf_le_csInf ⟨0, fun t ht => ht.1.le⟩ (exists_rhoSum_dualBasis_le hB hϵ)
    fun _ ht => ⟨ht.1, ht.2.trans (by linarith)⟩

/-- `M ≥ η_ϵ(L(B))` iff `ρ(MᵗL(B)*) ≤ 1 + ϵ` ([Pei10, Definition 2.3]). -/
theorem geSmoothing_iff {B M : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0) (hM : M.det ≠ 0)
    {ϵ : ℝ} (hϵ : 0 < ϵ) :
    GeSmoothing ϵ M B ↔ rhoSum (Mᵀ * dualBasis B) (1 : Matrix (Fin m) (Fin m) ℝ) 0 ≤ 1 + ϵ := by
  have hN : (M⁻¹ * B).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact mul_ne_zero (inv_ne_zero hM) hB
  have hdb : dualBasis (M⁻¹ * B) = Mᵀ * dualBasis B := by
    rw [dualBasis, dualBasis, Matrix.mul_inv_rev,
      Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.2 hM), Matrix.transpose_mul]
  rw [show GeSmoothing ϵ M B ↔ smoothingParam ϵ (M⁻¹ * B) ≤ 1 from ⟨fun h => h.1, fun h => ⟨h⟩⟩,
    smoothingParam_le_iff hN hϵ one_pos, hdb, inv_one, one_smul]

/-- For `s > 0`, `sI ≥ η_ϵ(L(B))` iff `s ≥ η_ϵ(L(B))`. -/
theorem geSmoothing_smul_one_iff {B : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0) {ϵ s : ℝ}
    (hϵ : 0 < ϵ) (hs : 0 < s) :
    GeSmoothing ϵ (s • (1 : Matrix (Fin m) (Fin m) ℝ)) B ↔ smoothingParam ϵ B ≤ s := by
  have hM : (s • (1 : Matrix (Fin m) (Fin m) ℝ)).det ≠ 0 := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ hs.ne'
  rw [geSmoothing_iff hB hM hϵ, smoothingParam_le_iff hB hϵ hs, rhoSum_inv_smul_one hs.ne',
    rhoSum_dual_weight]
  simp only [Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mulVec, Matrix.one_mulVec,
    sqNorm_smul, mul_assoc]

/-- `MMᵗ ⪰ s²I` and `s ≥ η_ϵ(L(B))` imply `M ≥ η_ϵ(L(B))` [ZKLY26, p. 3, l. 105]. -/
theorem geSmoothing_of_posSemidef {B M : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0)
    (hM : M.det ≠ 0) {ϵ s : ℝ} (hϵ : 0 < ϵ) (hs : 0 < s)
    (hMM : (M * Mᵀ - s ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef)
    (hη : smoothingParam ϵ B ≤ s) : GeSmoothing ϵ M B := by
  rw [geSmoothing_iff hB hM hϵ, rhoSum_dual_weight]
  refine le_trans (Summable.tsum_le_tsum (fun y => ?_) (summable_dual_weight hB hM)
    (summable_exp_sqNorm (det_dualBasis_ne_zero hB) hs.ne')) ?_
  · set v := dualBasis B *ᵥ ofInt y
    have h := hMM.dotProduct_mulVec_nonneg v
    have hq := quadForm_transpose_mul_self Mᵀ v
    rw [Matrix.transpose_transpose, quadForm] at hq
    simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul, hq] at h
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left (sub_nonneg.1 h) Real.pi_pos.le
    unfold sqNorm at this ⊢
    linarith
  · rw [← rhoSum_inv_smul_one hs.ne']
    exact (smoothingParam_le_iff hB hϵ hs).1 hη

/-- **Lemma 1** [ZKLY26, p. 3, l. 106-107] ([Pei10, Lemma 2.4]): if `0 < ϵ < 1` and
`M ≥ η_ϵ(L(B))`, then `ρ_{M,c}(L(B)) ∈ [(1 − ϵ)/(1 + ϵ), 1] ρ_M(L(B))` for every `c`. -/
theorem rhoSum_mem_Icc {B M : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0) (hM : M.det ≠ 0)
    {ϵ : ℝ} (hϵ₀ : 0 < ϵ) (hϵ₁ : ϵ < 1) (h : GeSmoothing ϵ M B) (c : Fin m → ℝ) :
    rhoSum B M c ∈ Set.Icc ((1 - ϵ) / (1 + ϵ) * rhoSum B M 0) (rhoSum B M 0) := by
  refine ⟨?_, rhoSum_le_rhoSum_zero hB hM c⟩
  have hs := summable_dual_weight hB hM
  have hA := (geSmoothing_iff hB hM hϵ₀).1 h
  rw [rhoSum_dual_weight] at hA
  have hcs : Summable fun y : Fin m → ℤ =>
      Real.exp (-π * sqNorm (Mᵀ *ᵥ (dualBasis B *ᵥ ofInt y))) *
        Real.cos (2 * π * ((dualBasis B *ᵥ ofInt y) ⬝ᵥ c)) :=
    Summable.of_norm_bounded hs fun y => by
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)
  have h2 := (hs.add hcs).le_tsum 0 fun y _ => by
    have := mul_nonneg (Real.exp_pos (-π * sqNorm (Mᵀ *ᵥ (dualBasis B *ᵥ ofInt y)))).le
      (neg_le_iff_add_nonneg.1 (Real.neg_one_le_cos (2 * π * ((dualBasis B *ᵥ ofInt y) ⬝ᵥ c))))
    linarith
  have hz : sqNorm (0 : Fin m → ℝ) = 0 := by simp [sqNorm]
  simp only [ofInt_zero, Matrix.mulVec_zero, zero_dotProduct, mul_zero, Real.cos_zero, hz,
    Real.exp_zero, mul_one] at h2
  rw [hs.tsum_add hcs] at h2
  have hk : 0 < |M.det| / |B.det| := div_pos (abs_pos.2 hM) (abs_pos.2 hB)
  rw [rhoSum_eq_tsum_dual_real hB hM c, rhoSum_eq_tsum_dual_real hB hM 0]
  simp only [dotProduct_zero, mul_zero, Real.cos_zero, mul_one]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  have h3 := mul_le_mul_of_nonneg_left (show 2 - ∑' y : Fin m → ℤ,
      Real.exp (-π * sqNorm (Mᵀ *ᵥ (dualBasis B *ᵥ ofInt y))) ≤ ∑' y : Fin m → ℤ,
      Real.exp (-π * sqNorm (Mᵀ *ᵥ (dualBasis B *ᵥ ofInt y))) *
        Real.cos (2 * π * ((dualBasis B *ᵥ ofInt y) ⬝ᵥ c)) by linarith)
    (mul_nonneg hk.le (by linarith : (0 : ℝ) ≤ 1 + ϵ))
  have h4 := mul_nonneg hk.le (sub_nonneg.2 hA)
  linarith

/-- **Lemma 1 for `ℤ^m`** [ZKLY26, p. 3, l. 106-107]: if `0 < ϵ < 1` and `M ≥ η_ϵ(ℤ^m)`, then
`ρ_{M,c}(ℤ^m) ∈ [(1 − ϵ)/(1 + ϵ), 1] ρ_M(ℤ^m)` for every `c`. -/
theorem rhoSum_one_mem_Icc {M : Matrix (Fin m) (Fin m) ℝ} (hM : M.det ≠ 0) {ϵ : ℝ}
    (hϵ₀ : 0 < ϵ) (hϵ₁ : ϵ < 1) (h : GeSmoothing ϵ M 1) (c : Fin m → ℝ) :
    rhoSum 1 M c ∈ Set.Icc ((1 - ϵ) / (1 + ϵ) * rhoSum 1 M 0) (rhoSum 1 M 0) :=
  rhoSum_mem_Icc (by simp) hM hϵ₀ hϵ₁ h c

/-- `ρ_{1/s}(ℤ^m) = (Σ_{k ∈ ℤ} e^{−πs²k²})^m`. -/
theorem rhoSum_dualBasis_one {s : ℝ} (hs : s ≠ 0) :
    rhoSum (dualBasis (1 : Matrix (Fin m) (Fin m) ℝ)) (s⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)) 0 =
      (∑' k : ℤ, Real.exp (-π * s ^ 2 * k ^ 2)) ^ m := by
  rw [rhoSum_inv_smul_one hs, dualBasis, inv_one, Matrix.transpose_one]
  have h := hasSum_prod_pi (f := fun (_ : Fin m) (k : ℤ) => Real.exp (-π * s ^ 2 * (k : ℝ) ^ 2))
    (fun _ _ => (Real.exp_pos _).le) fun _ => by
      simpa using summable_exp_neg_sq (pow_pos (abs_pos.2 hs) 2) 0
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  refine Eq.trans (tsum_congr fun y => ?_) h.tsum_eq
  rw [Matrix.one_mulVec, sqNorm, dotProduct, Finset.mul_sum, Real.exp_sum]
  exact Finset.prod_congr rfl fun i _ => by simp [ofInt, sq, mul_assoc]

/-- `η_ϵ(ℤ^m) ≤ s` iff `(1 + T(s/√(2π)))^m ≤ 1 + ϵ`, with the theta tail
`T(σ) = Σ_{k ∈ ℤ} e^{−2π²σ²k²} − 1` of `FalconPrecision.ThetaTail.tail`. -/
theorem smoothingParam_one_le_iff_tail {ϵ s : ℝ} (hϵ : 0 < ϵ) (hs : 0 < s) :
    smoothingParam ϵ (1 : Matrix (Fin m) (Fin m) ℝ) ≤ s ↔
      (1 + FalconPrecision.ThetaTail.tail (s / √(2 * π))) ^ m ≤ 1 + ϵ := by
  have h : 1 + FalconPrecision.ThetaTail.tail (s / √(2 * π)) =
      ∑' k : ℤ, Real.exp (-π * s ^ 2 * k ^ 2) := by
    rw [FalconPrecision.ThetaTail.tail, add_sub_cancel]
    refine tsum_congr fun k => ?_
    rw [div_pow, Real.sq_sqrt (by positivity)]
    congr 1
    field_simp
  rw [smoothingParam_le_iff (by simp) hϵ hs, rhoSum_dualBasis_one hs.ne', h]

private theorem exp_bound_aux (hm : 0 < m) {ϵ : ℝ} (hϵ : 0 < ϵ) :
    Real.exp (m * (2 * (ϵ / (2 * m * (1 + ϵ))) / (1 - (ϵ / (2 * m * (1 + ϵ))) ^ 3))) ≤
      1 + ϵ := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set x := ϵ / (2 * m * (1 + ϵ)) with hx
  set y := ϵ / (1 + ϵ) with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y < 1 := by rw [hy, div_lt_one (by linarith)]; linarith
  have hxy : 2 * m * x = y := by rw [hx, hy]; field_simp
  have hx0 : 0 < x := by positivity
  have hx2 : x ≤ y / 2 := by linarith [mul_le_mul_of_nonneg_right hm1 hx0.le]
  have hx12 : x ≤ 1 / 2 := by linarith
  have hxsq : x ^ 2 ≤ 1 / 4 := (pow_le_pow_left₀ hx0.le hx12 2).trans_eq (by norm_num)
  have hx3 : x ^ 3 ≤ x / 4 := by linarith [mul_le_mul_of_nonneg_left hxsq hx0.le]
  have hden : 7 / 8 ≤ 1 - x ^ 3 := by linarith
  set z := m * (2 * x / (1 - x ^ 3)) with hz
  have hz' : z = y / (1 - x ^ 3) := by
    rw [hz, ← hxy]
    field_simp
  have hzy : y ≤ z := by
    rw [hz', le_div_iff₀ (by linarith)]
    nlinarith [mul_nonneg hy0.le (pow_nonneg hx0.le 3)]
  have hz_le : z ≤ y + y ^ 2 / 4 := by
    rw [hz', div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hx3 hy0.le, mul_le_mul_of_nonneg_left hx2 hy0.le,
      mul_le_mul_of_nonneg_left hx3 (sq_nonneg y), mul_le_mul_of_nonneg_left hx12 (sq_nonneg y)]
  have hz2 : z / 2 < 1 := by linarith [mul_lt_mul'' hy1 hy1 hy0.le hy0.le]
  have he : Real.exp (z / 2) ≤ 1 / (1 - z / 2) := by
    rw [le_div_iff₀ (by linarith)]
    have h1 := Real.add_one_le_exp (-(z / 2))
    rw [Real.exp_neg] at h1
    have hp := Real.exp_pos (z / 2)
    calc Real.exp (z / 2) * (1 - z / 2) ≤ Real.exp (z / 2) * (Real.exp (z / 2))⁻¹ := by
          gcongr
          linarith
      _ = 1 := mul_inv_cancel₀ hp.ne'
  have hsq : 1 - y ≤ (1 - z / 2) ^ 2 := by nlinarith [mul_self_le_mul_self hy0.le hzy]
  have h1y : 1 - y = 1 / (1 + ϵ) := by
    rw [hy]
    field_simp
    ring
  calc Real.exp z = Real.exp (z / 2) ^ 2 := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
    _ ≤ (1 / (1 - z / 2)) ^ 2 := pow_le_pow_left₀ (Real.exp_pos _).le he 2
    _ = 1 / (1 - z / 2) ^ 2 := by rw [one_div_pow]
    _ ≤ 1 / (1 - y) := one_div_le_one_div_of_le (by linarith) hsq
    _ = 1 + ϵ := by rw [h1y, one_div_one_div]

private theorem tsum_pow_natAbs_sq_le {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1 / 2) :
    ∑' k : ℤ, x ^ (k.natAbs ^ 2) ≤ 1 + 2 * x / (1 - x ^ 3) := by
  have hr1 : x ^ 3 < 1 := by
    have := pow_le_pow_left₀ hx0.le hx1 3
    norm_num at this
    linarith
  have hh := ((FalconPrecision.NumTail.tsum_rpow_natAbs (x ^ 3) (by positivity) hr1).mul_left
    (x⁻¹ ^ 2)).add (hasSum_ite_eq (0 : ℤ) (1 - x⁻¹ ^ 2))
  have hle : ∀ k : ℤ, x ^ (k.natAbs ^ 2) ≤
      x⁻¹ ^ 2 * (x ^ 3) ^ k.natAbs + (if k = 0 then 1 - x⁻¹ ^ 2 else 0) := by
    intro k
    by_cases hk : k = 0
    · subst hk
      simp
    · simp only [hk, ↓reduceIte, add_zero]
      have hK : 1 ≤ k.natAbs := Int.natAbs_pos.2 hk
      have hKK : 3 * k.natAbs ≤ k.natAbs ^ 2 + 2 := by
        rcases Nat.lt_or_ge k.natAbs 3 with h | h
        · interval_cases k.natAbs <;> norm_num
        · linarith [Nat.mul_le_mul_right k.natAbs h]
      rw [← pow_mul, inv_pow, ← div_eq_inv_mul, le_div_iff₀ (by positivity), ← pow_add]
      exact pow_le_pow_of_le_one hx0.le (by linarith) hKK
  have hs : Summable fun k : ℤ => x ^ (k.natAbs ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) hle hh.summable
  have hx3 : 1 - x ^ 3 ≠ 0 := by linarith
  calc ∑' k : ℤ, x ^ (k.natAbs ^ 2) ≤ _ := hasSum_le hle hs.hasSum hh
    _ = 1 + 2 * x / (1 - x ^ 3) := by
      field_simp
      ring

/-- `η_ϵ(ℤ^m) ≤ √(ln(2m(1 + 1/ϵ))/π)` ([Pei10, Lemma 2.5]; [MR04, Lemma 3.3]). -/
theorem smoothingParam_one_le (hm : 0 < m) {ϵ : ℝ} (hϵ : 0 < ϵ) :
    smoothingParam ϵ (1 : Matrix (Fin m) (Fin m) ℝ) ≤ √(Real.log (2 * m * (1 + 1 / ϵ)) / π) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hA : 1 < 2 * (m : ℝ) * (1 + 1 / ϵ) := by
    have : 0 < 1 / ϵ := by positivity
    linarith [mul_pos (by linarith : (0 : ℝ) < m) this]
  have hL := Real.log_pos hA
  have hs : 0 < √(Real.log (2 * m * (1 + 1 / ϵ)) / π) :=
    Real.sqrt_pos.2 (div_pos hL Real.pi_pos)
  rw [smoothingParam_le_iff (by simp) hϵ hs, rhoSum_dualBasis_one hs.ne']
  set x := ϵ / (2 * m * (1 + ϵ)) with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 / 2 := by
    rw [hx, div_le_iff₀ (by positivity)]
    linarith [mul_le_mul_of_nonneg_right hm1 hϵ.le]
  have hterm : ∀ k : ℤ, Real.exp (-π * √(Real.log (2 * m * (1 + 1 / ϵ)) / π) ^ 2 * (k : ℝ) ^ 2) =
      x ^ (k.natAbs ^ 2) := by
    intro k
    have hk : ((k.natAbs ^ 2 : ℕ) : ℝ) = (k : ℝ) ^ 2 := by
      rw [Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs, sq_abs]
    rw [Real.sq_sqrt (div_pos hL Real.pi_pos).le,
      show -π * (Real.log (2 * m * (1 + 1 / ϵ)) / π) * (k : ℝ) ^ 2 =
        ((k.natAbs ^ 2 : ℕ) : ℝ) * -Real.log (2 * m * (1 + 1 / ϵ)) by
          rw [hk]
          field_simp,
      Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by linarith), hx]
    congr 1
    field_simp
    ring
  have hpos : 0 < 1 - x ^ 3 := by
    have := pow_le_pow_left₀ hx0.le hx1 3
    norm_num at this
    linarith
  rw [tsum_congr hterm]
  calc (∑' k : ℤ, x ^ (k.natAbs ^ 2)) ^ m ≤ (1 + 2 * x / (1 - x ^ 3)) ^ m :=
        pow_le_pow_left₀ (tsum_nonneg fun _ => by positivity) (tsum_pow_natAbs_sq_le hx0 hx1) m
    _ ≤ Real.exp (2 * x / (1 - x ^ 3)) ^ m :=
        pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (2 * x / (1 - x ^ 3))]) m
    _ = Real.exp (m * (2 * x / (1 - x ^ 3))) := (Real.exp_nat_mul _ m).symm
    _ ≤ 1 + ϵ := exp_bound_aux hm hϵ

end Mitaka.LatticeGaussian
