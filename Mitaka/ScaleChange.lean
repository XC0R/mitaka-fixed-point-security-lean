/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Taylor2
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mitaka.Lemma4

/-! # The scale change between two lattice Gaussians ([ZKLY26], proof of Theorem 1)

[ZKLY26] (ePrint 2026/2521), p. 7-8, l. 239-258: with `θ₁, …, θ₂ₙ` the eigenvalues of `s⁻²Σ_e`
(`|θᵢ| ≤ τ̄` by Lemma 3), "For `t ∈ [0, 2a]`, define `V_t = r²(s²I₂ₙ − Σ_e)(I₂ₙ + (t − 1)s⁻²Σ_e)⁻¹`.
Its eigenvalues are `r²s²(1 − θᵢ)/(1 + (t − 1)θᵢ)`, and hence `(2a − 1)τ̄ < 1` ensures that `V_t` is
positive definite. Set `φ(t) = log(det(L(B)) det(V_t)^{−1/2} ρ_{√V_t,c}(L(B)))`. Then
`log R_{2a}(𝒬_e‖𝒬₀) = (1/(2(2a − 1))) log(det(V_{2a}) det(V₀)^{2a−1}/det(V₁)^{2a})
+ (φ(2a) − 2aφ(1) + (2a − 1)φ(0))/(2a − 1)`" (l. 242); the determinant term is
`a Σᵢ θᵢ² ∫₀¹ x dx/((1 − xθᵢ)(1 + (2a − 1)xθᵢ)) ≤ a‖Σ_e‖_F²/(2s⁴(1 + τ̄)(1 − (2a − 1)τ̄))` (l. 244);
`V_t ⪰ r²s²(1 − τ̄)(1 + (2a − 1)τ̄)⁻¹ I₂ₙ`, so `√((1 − √(ϵ/2))V_t)` stays above `η_ϵ(L(B))`
(l. 244-246); by Poisson summation `e^{φ(t)} = Σ_{v∈Λ*} e^{−q_t(v)} e^{−2πi⟨v,c⟩}` with
`q_t(v) = πvᵗV_tv` (l. 247-249); termwise differentiation (l. 250-251) and
`|q′_t| ≤ δq_t`, `|q″_t| ≤ 2δ²q_t`, `δ = τ̄/(1 − (2a − 1)τ̄)`, `ξ = √(ϵ/2)`, give
`|φ″(t)| ≤ 5τ̄²/(1 − (2a − 1)τ̄)²` for `ϵ ≤ 1/2` (l. 252-256); so (l. 258)
`log R_{2a}(𝒬_e‖𝒬₀) ≤ a‖Σ_e‖_F²/(2s⁴(1 + τ̄)(1 − (2a − 1)τ̄)) + 5aτ̄²/(1 − (2a − 1)τ̄)²`.

The generic part (namespace `Mitaka.LatticeGaussian`) is stated for any invertible `B`, any
symmetric `Σ` (`Se`) with `|xᵗΣx| ≤ τ s² ‖x‖²` (the eigenvalue bound `|θᵢ| ≤ τ`), any factor `M`
with `MMᵗ = r²(s²I − Σ)` (`𝒬_e` depends on `M` only through `MMᵗ`, `rho_congr`), and the target
width condition (condition 4) for `B`. The paper does not justify the termwise differentiation;
`exists_deriv2_logMass_le` includes it. `Key.renyiDiv_gaussianQe_le` is the
instance for the Mitaka key, with `Σ = Key.sigmaEMat` and `τ = τ̄` (Lemma 3). -/

@[expose] public section

open Real MeasureTheory InformationTheory LatticeCrypto Mitaka.LatticeGaussian
open scoped Matrix MatrixOrder ENNReal

namespace Mitaka.LatticeGaussian

variable {m : ℕ}

/-- `V_t = r²(s²I − Σ)(I + (t − 1)s⁻²Σ)⁻¹` [ZKLY26, p. 7, l. 239]. -/
noncomputable def pathCov (r s : ℝ) (Se : Matrix (Fin m) (Fin m) ℝ) (t : ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  r ^ 2 • ((s ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) - Se) *
    (1 + ((t - 1) / s ^ 2) • Se)⁻¹)

/-- `φ = log(det(L(B)) det(V)^{−1/2} ρ_{√V,c}(L(B)))` [ZKLY26, p. 7, l. 241], with
`ρ_{√V,c}(x) = exp(−π(x − c)ᵗV⁻¹(x − c))` (`rho_eq_exp_quadForm`) and `det(L(B)) = |det B|`. -/
noncomputable def logMass (B V : Matrix (Fin m) (Fin m) ℝ) (c : Fin m → ℝ) : ℝ :=
  Real.log (|B.det| * V.det ^ (-(1 / 2) : ℝ) *
    ∑' z : Fin m → ℤ, Real.exp (-π * quadForm V⁻¹ (B *ᵥ ofInt z - c)))

/-! ### Spectral calculus for a symmetric matrix -/

/-- A symmetric real matrix is `U diag(d) Uᵗ` with `U` orthogonal. -/
private theorem exists_spectral {S : Matrix (Fin m) (Fin m) ℝ} (hS : S.IsSymm) :
    ∃ (U : Matrix (Fin m) (Fin m) ℝ) (d : Fin m → ℝ), Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧
      S = U * Matrix.diagonal d * Uᵀ := by
  have hH : S.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hS
  have hst : star (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ) =
      (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ)ᵀ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  refine ⟨hH.eigenvectorUnitary, hH.eigenvalues, ?_, ?_, ?_⟩
  · rw [← hst]
    exact Unitary.coe_star_mul_self _
  · rw [← hst]
    exact Unitary.coe_mul_star_self _
  · conv_lhs => rw [hH.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, hst]
    congr 2

variable {U : Matrix (Fin m) (Fin m) ℝ}

private theorem spec_mul (hU : Uᵀ * U = 1) (d e : Fin m → ℝ) :
    (U * Matrix.diagonal d * Uᵀ) * (U * Matrix.diagonal e * Uᵀ) =
      U * Matrix.diagonal (fun i => d i * e i) * Uᵀ := by
  rw [show U * Matrix.diagonal d * Uᵀ * (U * Matrix.diagonal e * Uᵀ) =
      U * Matrix.diagonal d * (Uᵀ * U) * Matrix.diagonal e * Uᵀ by simp only [Matrix.mul_assoc],
    hU, Matrix.mul_one, Matrix.mul_assoc U, Matrix.diagonal_mul_diagonal]

private theorem spec_one (hU' : U * Uᵀ = 1) :
    U * Matrix.diagonal (fun _ => (1 : ℝ)) * Uᵀ = 1 := by
  rw [show (Matrix.diagonal fun _ => (1 : ℝ)) = 1 from rfl, Matrix.mul_one, hU']

private theorem spec_smul (c : ℝ) (d : Fin m → ℝ) :
    c • (U * Matrix.diagonal d * Uᵀ) = U * Matrix.diagonal (fun i => c * d i) * Uᵀ := by
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.diagonal_smul]
  rfl

private theorem spec_add (d e : Fin m → ℝ) :
    U * Matrix.diagonal d * Uᵀ + U * Matrix.diagonal e * Uᵀ =
      U * Matrix.diagonal (fun i => d i + e i) * Uᵀ := by
  rw [← Matrix.add_mul, ← Matrix.mul_add, Matrix.diagonal_add]

private theorem spec_sub (d e : Fin m → ℝ) :
    U * Matrix.diagonal d * Uᵀ - U * Matrix.diagonal e * Uᵀ =
      U * Matrix.diagonal (fun i => d i - e i) * Uᵀ := by
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub]

private theorem spec_inv (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1) {d : Fin m → ℝ}
    (hd : ∀ i, d i ≠ 0) :
    (U * Matrix.diagonal d * Uᵀ)⁻¹ = U * Matrix.diagonal (fun i => (d i)⁻¹) * Uᵀ :=
  Matrix.inv_eq_right_inv (by
    rw [spec_mul hU, ← spec_one hU', show (fun i => d i * (d i)⁻¹) = fun _ => (1 : ℝ) from
      funext fun i => mul_inv_cancel₀ (hd i)])

private theorem spec_transpose (d : Fin m → ℝ) :
    (U * Matrix.diagonal d * Uᵀ)ᵀ = U * Matrix.diagonal d * Uᵀ := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.diagonal_transpose, Matrix.mul_assoc]

private theorem sqNorm_transpose_mulVec (hU' : U * Uᵀ = 1) (w : Fin m → ℝ) :
    sqNorm (Uᵀ *ᵥ w) = sqNorm w := by
  rw [sqNorm, dotProduct_transpose_mulVec_left, Matrix.mulVec_mulVec, hU', Matrix.one_mulVec,
    sqNorm]

private theorem quadForm_spec (d : Fin m → ℝ) (w : Fin m → ℝ) :
    quadForm (U * Matrix.diagonal d * Uᵀ) w = ∑ i, d i * (Uᵀ *ᵥ w) i ^ 2 := by
  rw [quadForm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem det_spec (hU : Uᵀ * U = 1) (d : Fin m → ℝ) :
    (U * Matrix.diagonal d * Uᵀ).det = ∏ i, d i := by
  have h : U.det * U.det = 1 := by
    have h0 := congrArg Matrix.det hU
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h0
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_transpose]
  linear_combination (∏ i, d i) * h

private theorem posDef_spec (hU' : U * Uᵀ = 1) {d : Fin m → ℝ}
    (hd : ∀ i, 0 < d i) : (U * Matrix.diagonal d * Uᵀ).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨by rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial,
    spec_transpose], fun w hw => ?_⟩
  rw [star_trivial, show w ⬝ᵥ (U * Matrix.diagonal d * Uᵀ) *ᵥ w =
    quadForm (U * Matrix.diagonal d * Uᵀ) w from rfl, quadForm_spec]
  have hv : Uᵀ *ᵥ w ≠ 0 := fun h0 => hw (by
    rw [← Matrix.one_mulVec w, ← hU', ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero])
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hd j).le (sq_nonneg _))
    ⟨i, Finset.mem_univ _, mul_pos (hd i)
      (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (by simpa using hi))))⟩

private theorem posSemidef_spec {d : Fin m → ℝ} (hd : ∀ i, 0 ≤ d i) :
    (U * Matrix.diagonal d * Uᵀ).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨by rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial,
    spec_transpose], fun w => ?_⟩
  rw [star_trivial, show w ⬝ᵥ (U * Matrix.diagonal d * Uᵀ) *ᵥ w =
    quadForm (U * Matrix.diagonal d * Uᵀ) w from rfl, quadForm_spec]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hd j) (sq_nonneg _)

private theorem sum_sq_spec (hU : Uᵀ * U = 1) (d : Fin m → ℝ) :
    ∑ i, ∑ j, (U * Matrix.diagonal d * Uᵀ) i j ^ 2 = ∑ i, d i ^ 2 := by
  have h1 : ∀ M : Matrix (Fin m) (Fin m) ℝ, ∑ i, ∑ j, M i j ^ 2 = (M * Mᵀ).trace := fun M => by
    simp [Matrix.trace, Matrix.mul_apply, sq]
  rw [h1, spec_transpose, spec_mul hU, Matrix.trace_mul_cycle, hU,
    Matrix.one_mul, Matrix.trace_diagonal]
  exact Finset.sum_congr rfl fun i _ => (sq _).symm

private theorem quadForm_spec_single (hU : Uᵀ * U = 1) (d : Fin m → ℝ) (i : Fin m) :
    quadForm (U * Matrix.diagonal d * Uᵀ) (U *ᵥ Pi.single i 1) = d i := by
  rw [quadForm_spec, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
  simp [Pi.single_apply]

private theorem sqNorm_mulVec_single (hU : Uᵀ * U = 1) (i : Fin m) :
    sqNorm (U *ᵥ Pi.single i 1) = 1 := by
  rw [sqNorm, ← dotProduct_transpose_mulVec_left, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
  simp

/-- The eigenvalue bound `|λᵢ| ≤ τ s²` from the quadratic-form bound. -/
private theorem abs_le_of_quadForm (hU : Uᵀ * U = 1) {lam : Fin m → ℝ} {τ s : ℝ}
    (hτ : ∀ x, |x ⬝ᵥ ((U * Matrix.diagonal lam * Uᵀ) *ᵥ x)| ≤ τ * s ^ 2 * sqNorm x) (i : Fin m) :
    |lam i| ≤ τ * s ^ 2 := by
  have h := hτ (U *ᵥ Pi.single i 1)
  rwa [show (U *ᵥ Pi.single i 1) ⬝ᵥ ((U * Matrix.diagonal lam * Uᵀ) *ᵥ (U *ᵥ Pi.single i 1)) =
    quadForm (U * Matrix.diagonal lam * Uᵀ) (U *ᵥ Pi.single i 1) from rfl,
    quadForm_spec_single hU, sqNorm_mulVec_single hU, mul_one] at h

/-- In the eigenbasis of `Σ`, `V_t = U diag(r²(s² − λᵢ)/(1 + (t − 1)λᵢ/s²)) Uᵗ`. -/
private theorem pathCov_spec (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1) {lam : Fin m → ℝ}
    {r s t : ℝ} (hd : ∀ i, 1 + (t - 1) / s ^ 2 * lam i ≠ 0) :
    pathCov r s (U * Matrix.diagonal lam * Uᵀ) t = U * Matrix.diagonal
      (fun i => r ^ 2 * ((s ^ 2 - lam i) * (1 + (t - 1) / s ^ 2 * lam i)⁻¹)) * Uᵀ := by
  have e1 : s ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) - U * Matrix.diagonal lam * Uᵀ =
      U * Matrix.diagonal (fun i => s ^ 2 - lam i) * Uᵀ := by
    rw [← spec_one hU', spec_smul, spec_sub]
    simp only [mul_one]
  have e2 : (1 : Matrix (Fin m) (Fin m) ℝ) + ((t - 1) / s ^ 2) • (U * Matrix.diagonal lam * Uᵀ) =
      U * Matrix.diagonal (fun i => 1 + (t - 1) / s ^ 2 * lam i) * Uᵀ := by
    rw [spec_smul, ← spec_one hU', spec_add]
  rw [pathCov, e1, e2, spec_inv hU hU' hd, spec_mul hU, spec_smul]

/-- `1 − (2a − 1)τ ≤ 1 + (t − 1)θ` for `|θ| ≤ τ` and `t ∈ [0, 2a]`. -/
private theorem one_sub_le_one_add {θ τ a t : ℝ} (hθ : |θ| ≤ τ) (ha : 1 < a)
    (ht : t ∈ Set.Icc 0 (2 * a)) : 1 - (2 * a - 1) * τ ≤ 1 + (t - 1) * θ := by
  have h1 : |(t - 1) * θ| ≤ (2 * a - 1) * τ := by
    rw [abs_mul]
    exact mul_le_mul (abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩) hθ (abs_nonneg _)
      (by linarith)
  linarith [neg_abs_le ((t - 1) * θ)]

/-- `(1 − τ)/(1 + (2a − 1)τ) ≤ (1 − θ)/(1 + (t − 1)θ)` for `|θ| ≤ τ` and `t ∈ [0, 2a]`. -/
private theorem ratio_le {θ τ a t : ℝ} (hθ : |θ| ≤ τ) (ha : 1 < a) (haτ : (2 * a - 1) * τ < 1)
    (ht : t ∈ Set.Icc 0 (2 * a)) :
    (1 - τ) / (1 + (2 * a - 1) * τ) ≤ (1 - θ) / (1 + (t - 1) * θ) := by
  have hτ0 : 0 ≤ τ := (abs_nonneg θ).trans hθ
  have hθτ := (abs_le.1 hθ)
  have hτ1 : τ < 1 := by nlinarith [hτ0, haτ]
  have hd := one_sub_le_one_add hθ ha ht
  have hp : 0 < 1 + (2 * a - 1) * τ := by
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * a - 1) hτ0
    linarith
  rw [div_le_div_iff₀ hp (by linarith)]
  nlinarith [mul_nonneg ht.1 (sub_nonneg.2 hθτ.2), mul_nonneg (sub_nonneg.2 ht.2)
    (mul_nonneg hτ0 (sub_nonneg.2 (hθτ.2.trans hτ1.le)))]

/-- Per-eigenvalue facts: `|λ/s²| ≤ τ`, `s² − λ > 0`, `1 + (t − 1)λ/s² ≥ 1 − (2a − 1)τ > 0`. -/
private theorem eig_facts {lam τ s a t : ℝ} (hs : 0 < s) (hl : |lam| ≤ τ * s ^ 2) (ha : 1 < a)
    (haτ : (2 * a - 1) * τ < 1) (ht : t ∈ Set.Icc 0 (2 * a)) :
    |lam / s ^ 2| ≤ τ ∧ 0 < s ^ 2 - lam ∧ 1 - (2 * a - 1) * τ ≤ 1 + (t - 1) / s ^ 2 * lam ∧
      0 < 1 - (2 * a - 1) * τ := by
  have hs2 : 0 < s ^ 2 := by positivity
  have hθ : |lam / s ^ 2| ≤ τ := by
    rw [abs_div, abs_of_pos hs2, div_le_iff₀ hs2]
    exact hl
  have hτ0 : 0 ≤ τ := (abs_nonneg _).trans hθ
  have hτ1 : τ < 1 := by
    have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 2 * a - 1 by linarith) hτ0
    linarith
  have hk : (t - 1) / s ^ 2 * lam = (t - 1) * (lam / s ^ 2) := by ring
  refine ⟨hθ, ?_, hk ▸ one_sub_le_one_add hθ ha ht, by linarith⟩
  have := (abs_le.1 hl).2
  have := mul_lt_mul_of_pos_right hτ1 hs2
  linarith

/-- A function vanishing at `0` whose derivative has the sign of `x` on `[−τ, τ]` is nonnegative
there (mean value theorem). -/
private theorem nonneg_of_mul_deriv_nonneg {g g' : ℝ → ℝ} {τ θ : ℝ} (hθ : |θ| ≤ τ)
    (hg : ∀ x, |x| ≤ τ → HasDerivAt g (g' x) x) (hsign : ∀ x, |x| ≤ τ → 0 ≤ x * g' x)
    (hg0 : g 0 = 0) : 0 ≤ g θ := by
  have hcont : ∀ u v, -τ ≤ u → v ≤ τ → ContinuousOn g (Set.Icc u v) := fun u v hu hv x hx =>
    (hg x (abs_le.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩)).continuousAt.continuousWithinAt
  obtain ⟨hθl, hθu⟩ := abs_le.1 hθ
  rcases lt_trichotomy θ 0 with h | h | h
  · obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope g g' h (hcont θ 0 hθl (by linarith))
      fun x hx => hg x (abs_le.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    have hs := hsign ξ (abs_le.2 ⟨by linarith [hξ.1], by linarith [hξ.2]⟩)
    rw [hg0] at hξe
    have hneg : g' ξ ≤ 0 := not_lt.1 fun hpos => by nlinarith [hξ.2]
    have e : g θ = θ * g' ξ := by
      rw [hξe]
      field_simp
      ring
    rw [e]
    exact mul_nonneg_of_nonpos_of_nonpos h.le hneg
  · rw [h, hg0]
  · obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope g g' h (hcont 0 θ (by linarith) hθu)
      fun x hx => hg x (abs_le.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    have hs := hsign ξ (abs_le.2 ⟨by linarith [hξ.1], by linarith [hξ.2]⟩)
    rw [hg0] at hξe
    have hpos : 0 ≤ g' ξ := not_lt.1 fun hneg => by nlinarith [hξ.1]
    have e : g θ = θ * g' ξ := by
      rw [hξe]
      field_simp
      ring
    rw [e]
    exact mul_nonneg h.le hpos

/-- `−log(1 + bθ) − b log(1 − θ) ≤ b(b + 1)θ²/(2(1 + τ)(1 − bτ))` for `|θ| ≤ τ`, `bτ < 1`
(the integral of [ZKLY26, p. 7, l. 244], by the mean value theorem). -/
private theorem log_bound {θ τ b : ℝ} (hb : 1 ≤ b) (hθ : |θ| ≤ τ) (hbτ : b * τ < 1) :
    -Real.log (1 + b * θ) - b * Real.log (1 - θ) ≤
      b * (b + 1) * θ ^ 2 / (2 * ((1 + τ) * (1 - b * τ))) := by
  have hτ0 : 0 ≤ τ := (abs_nonneg θ).trans hθ
  have hτ1 : τ < 1 := by
    have := mul_le_mul_of_nonneg_right hb hτ0
    linarith
  have hbτ0 : 0 ≤ b * τ := mul_nonneg (by linarith) hτ0
  set D := (1 + τ) * (1 - b * τ) with hDdef
  have hD : 0 < D := mul_pos (by linarith) (by linarith)
  have hdom : ∀ x, |x| ≤ τ → 0 < 1 + b * x ∧ 0 < 1 - x ∧ D ≤ (1 - x) * (1 + b * x) := by
    intro x hx
    obtain ⟨hxl, hxu⟩ := abs_le.1 hx
    have hbx : -(b * τ) ≤ b * x := by
      have := mul_le_mul_of_nonneg_left hxl (by linarith : (0 : ℝ) ≤ b)
      linarith
    refine ⟨by linarith, by linarith, ?_⟩
    have e : (1 - x) * (1 + b * x) - D = (x + τ) * ((b - 1) + b * (τ - x)) := by
      rw [hDdef]
      ring
    have h1 : 0 ≤ (x + τ) * ((b - 1) + b * (τ - x)) :=
      mul_nonneg (by linarith) (add_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith)))
    linarith
  set C := b * (b + 1) / (2 * D) with hCdef
  set g : ℝ → ℝ := fun x => C * x ^ 2 + Real.log (1 + b * x) + b * Real.log (1 - x) with hgdef
  set g' : ℝ → ℝ := fun x => 2 * C * x + b / (1 + b * x) - b / (1 - x) with hg'def
  have hg : ∀ x, |x| ≤ τ → HasDerivAt g (g' x) x := by
    intro x hx
    obtain ⟨h1, h2, -⟩ := hdom x hx
    have e1 := (((hasDerivAt_id x).const_mul b).const_add 1).log h1.ne'
    have e2 := ((hasDerivAt_id x).const_sub 1).log h2.ne'
    have e3 := (hasDerivAt_pow 2 x).const_mul C
    have h := (e3.add e1).add (e2.const_mul b)
    convert h using 1
    · funext y
      simp only [hgdef, Pi.add_apply, id]
    · simp only [hg'def, id]
      field_simp
      ring
  have hsign : ∀ x, |x| ≤ τ → 0 ≤ x * g' x := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := hdom x hx
    have h1' : 1 + x * b ≠ 0 := by rw [mul_comm]; exact h1.ne'
    have h2' := h2.ne'
    have hD' := hD.ne'
    have e : x * g' x = b * (b + 1) * x ^ 2 * (1 / D - 1 / ((1 - x) * (1 + b * x))) := by
      simp only [hg'def, hCdef]
      field_simp
      ring
    rw [e]
    exact mul_nonneg (by positivity) (sub_nonneg.2 (one_div_le_one_div_of_le hD h3))
  have key := nonneg_of_mul_deriv_nonneg hθ hg hsign (by simp [hgdef])
  have e : g θ = C * θ ^ 2 - (-Real.log (1 + b * θ) - b * Real.log (1 - θ)) := by
    simp only [hgdef]
    ring
  have e2 : b * (b + 1) * θ ^ 2 / (2 * D) = C * θ ^ 2 := by
    rw [hCdef]
    ring
  rw [e2]
  linarith

/-- `quadForm` is additive in the matrix. -/
private theorem quadForm_add (P Q : Matrix (Fin m) (Fin m) ℝ) (w : Fin m → ℝ) :
    quadForm (P + Q) w = quadForm P w + quadForm Q w := by
  simp [quadForm, Matrix.add_mulVec, dotProduct_add]

/-- `V₁ = r²(s²I − Σ)`. -/
theorem pathCov_one (r s : ℝ) (Se : Matrix (Fin m) (Fin m) ℝ) :
    pathCov r s Se 1 = r ^ 2 • (s ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) - Se) := by
  simp [pathCov]

/-- `V₀ = (rs)² I`. -/
theorem pathCov_zero {Se : Matrix (Fin m) (Fin m) ℝ} {r s τ : ℝ} (hs : 0 < s)
    (hτ : ∀ x, |x ⬝ᵥ (Se *ᵥ x)| ≤ τ * s ^ 2 * sqNorm x) (hτ1 : τ < 1) :
    pathCov r s Se 0 = (r * s) ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) := by
  have hs2 : 0 < s ^ 2 := by positivity
  set N : Matrix (Fin m) (Fin m) ℝ := 1 + ((0 - 1) / s ^ 2) • Se with hNdef
  have hN : s ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) - Se = s ^ 2 • N := by
    rw [hNdef, smul_add, smul_smul, show s ^ 2 * ((0 - 1) / s ^ 2) = -1 by field_simp; norm_num,
      neg_one_smul,
      sub_eq_add_neg]
  have hdet : IsUnit N.det := by
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hSx : Se *ᵥ x = s ^ 2 • x := by
      have h1 : x - (1 / s ^ 2) • (Se *ᵥ x) = 0 := by
        rw [← hx, hNdef, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
        rw [sub_eq_add_neg, ← neg_smul]
        congr 2
        ring
      rw [sub_eq_zero] at h1
      calc Se *ᵥ x = s ^ 2 • ((1 / s ^ 2) • (Se *ᵥ x)) := by
            rw [smul_smul, mul_one_div_cancel hs2.ne', one_smul]
        _ = s ^ 2 • x := by rw [← h1]
    have h2 := hτ x
    rw [hSx, dotProduct_smul, smul_eq_mul] at h2
    change |s ^ 2 * sqNorm x| ≤ τ * s ^ 2 * sqNorm x at h2
    rw [abs_of_nonneg (mul_nonneg hs2.le (sqNorm_nonneg x))] at h2
    have h3 := sqNorm_pos hx0
    have : s ^ 2 * sqNorm x ≤ τ * s ^ 2 * sqNorm x := h2
    nlinarith [mul_pos hs2 h3]
  rw [pathCov, hN, Matrix.smul_mul, Matrix.mul_nonsing_inv _ hdet, smul_smul, mul_pow]

/-- `V_t ≻ 0` for `t ∈ [0, 2a]` [ZKLY26, p. 7, l. 240]. -/
theorem posDef_pathCov {Se : Matrix (Fin m) (Fin m) ℝ} (hSe : Se.IsSymm) {r s τ a : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hτ : ∀ x, |x ⬝ᵥ (Se *ᵥ x)| ≤ τ * s ^ 2 * sqNorm x) (ha : 1 < a)
    (haτ : (2 * a - 1) * τ < 1) {t : ℝ} (ht : t ∈ Set.Icc 0 (2 * a)) :
    (pathCov r s Se t).PosDef := by
  obtain ⟨U, lam, hU, hU', rfl⟩ := exists_spectral hSe
  have hf := fun i => eig_facts hs (abs_le_of_quadForm hU hτ i) ha haτ ht
  rw [pathCov_spec hU hU' fun i => ((hf i).2.2.2.trans_le (hf i).2.2.1).ne']
  exact posDef_spec hU' fun i => mul_pos (pow_pos hr 2)
    (mul_pos (hf i).2.1 (inv_pos.2 ((hf i).2.2.2.trans_le (hf i).2.2.1)))

/-- `V_t⁻¹ = t V₁⁻¹ + (1 − t) V₀⁻¹` for `t ∈ [0, 2a]` (the path interpolates the precisions). -/
theorem inv_pathCov {Se : Matrix (Fin m) (Fin m) ℝ} (hSe : Se.IsSymm) {r s τ a : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hτ : ∀ x, |x ⬝ᵥ (Se *ᵥ x)| ≤ τ * s ^ 2 * sqNorm x) (ha : 1 < a)
    (haτ : (2 * a - 1) * τ < 1) {t : ℝ} (ht : t ∈ Set.Icc 0 (2 * a)) :
    (pathCov r s Se t)⁻¹ = t • (pathCov r s Se 1)⁻¹ + (1 - t) • (pathCov r s Se 0)⁻¹ := by
  obtain ⟨U, lam, hU, hU', rfl⟩ := exists_spectral hSe
  have hl := abs_le_of_quadForm hU hτ
  have h0 : (0 : ℝ) ∈ Set.Icc 0 (2 * a) := ⟨le_rfl, by linarith⟩
  have h1 : (1 : ℝ) ∈ Set.Icc 0 (2 * a) := ⟨zero_le_one, by linarith⟩
  have hft := fun i => eig_facts hs (hl i) ha haτ ht
  have hf0 := fun i => eig_facts hs (hl i) ha haτ h0
  have hf1 := fun i => eig_facts hs (hl i) ha haτ h1
  have hne : ∀ {u : ℝ}, (∀ i, 1 - (2 * a - 1) * τ ≤ 1 + (u - 1) / s ^ 2 * lam i) →
      ∀ i, 1 + (u - 1) / s ^ 2 * lam i ≠ 0 := fun h i =>
    ((hft i).2.2.2.trans_le (h i)).ne'
  rw [pathCov_spec hU hU' (hne fun i => (hft i).2.2.1),
    pathCov_spec hU hU' (hne fun i => (hf1 i).2.2.1),
    pathCov_spec hU hU' (hne fun i => (hf0 i).2.2.1), spec_inv hU hU', spec_inv hU hU',
    spec_inv hU hU', spec_smul, spec_smul, spec_add]
  · refine congrArg (fun d => U * Matrix.diagonal d * Uᵀ) (funext fun i => ?_)
    have ha1 := (hft i).2.1.ne'
    have ha2 := ((hft i).2.2.2.trans_le (hft i).2.2.1).ne'
    have ha3 := ((hf0 i).2.2.2.trans_le (hf0 i).2.2.1).ne'
    have hs0 := hs.ne'
    have hr0 := hr.ne'
    field_simp
    ring
  all_goals intro i
  · exact mul_ne_zero (pow_ne_zero _ hr.ne') (mul_ne_zero (hf0 i).2.1.ne'
      (inv_ne_zero ((hf0 i).2.2.2.trans_le (hf0 i).2.2.1).ne'))
  · exact mul_ne_zero (pow_ne_zero _ hr.ne') (mul_ne_zero (hf1 i).2.1.ne'
      (inv_ne_zero ((hf1 i).2.2.2.trans_le (hf1 i).2.2.1).ne'))
  · exact mul_ne_zero (pow_ne_zero _ hr.ne') (mul_ne_zero (hft i).2.1.ne'
      (inv_ne_zero ((hft i).2.2.2.trans_le (hft i).2.2.1).ne'))

/-- `V_t ⪰ r²s²(1 − τ)(1 + (2a − 1)τ)⁻¹ I` for `t ∈ [0, 2a]` [ZKLY26, p. 7, l. 244-245]. -/
theorem posSemidef_pathCov_sub {Se : Matrix (Fin m) (Fin m) ℝ} (hSe : Se.IsSymm) {r s τ a : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hτ : ∀ x, |x ⬝ᵥ (Se *ᵥ x)| ≤ τ * s ^ 2 * sqNorm x) (ha : 1 < a)
    (haτ : (2 * a - 1) * τ < 1) {t : ℝ} (ht : t ∈ Set.Icc 0 (2 * a)) :
    (pathCov r s Se t -
      (r ^ 2 * s ^ 2 * (1 - τ) / (1 + (2 * a - 1) * τ)) • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef
    := by
  obtain ⟨U, lam, hU, hU', rfl⟩ := exists_spectral hSe
  have hf := fun i => eig_facts hs (abs_le_of_quadForm hU hτ i) ha haτ ht
  rw [pathCov_spec hU hU' fun i => ((hf i).2.2.2.trans_le (hf i).2.2.1).ne', ← spec_one hU',
    spec_smul, spec_sub]
  refine posSemidef_spec fun i => ?_
  have hr2 := ratio_le (hf i).1 ha haτ ht
  have hpos := (hf i).2.2.2.trans_le (hf i).2.2.1
  have hs0 := hs.ne'
  have e : r ^ 2 * ((s ^ 2 - lam i) * (1 + (t - 1) / s ^ 2 * lam i)⁻¹) =
      r ^ 2 * s ^ 2 * ((1 - lam i / s ^ 2) / (1 + (t - 1) * (lam i / s ^ 2))) := by
    rw [show (t - 1) * (lam i / s ^ 2) = (t - 1) / s ^ 2 * lam i by ring]
    field_simp
  rw [e, mul_one, sub_nonneg, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hr2 (by positivity)

/-- The target-width condition keeps `√((1 − √(ϵ/2))V_t)` above `η_ϵ(L(B))` for `t ∈ [0, 2a]`
[ZKLY26, p. 8, l. 245-246]. -/
theorem geSmoothing_pathCov {B Se : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0)
    (hSe : Se.IsSymm) {r s τ a ϵ : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hτ : ∀ x, |x ⬝ᵥ (Se *ᵥ x)| ≤ τ * s ^ 2 * sqNorm x) (ha : 1 < a)
    (haτ : (2 * a - 1) * τ < 1) (hϵ₀ : 0 < ϵ) (hϵ : ϵ ≤ 1 / 2)
    (hη : smoothingParam ϵ B ≤
      r * s * √((1 - √(ϵ / 2)) * (1 - τ) / (1 + (2 * a - 1) * τ)))
    {t : ℝ} (ht : t ∈ Set.Icc 0 (2 * a)) :
    GeSmoothing ϵ (CFC.sqrt ((1 - √(ϵ / 2)) • pathCov r s Se t)) B := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨csInf_le ⟨0, fun x hx => hx.1.le⟩ ⟨one_pos, ?_⟩⟩
    simp [rhoSum, rho, sqNorm]
    linarith
  have hs2 : 0 < s ^ 2 := by positivity
  have hτ0 : 0 ≤ τ := by
    have h := hτ (Pi.single ⟨0, hm⟩ 1)
    have h1 : sqNorm (Pi.single ⟨0, hm⟩ (1 : ℝ) : Fin m → ℝ) = 1 := by simp [sqNorm]
    rw [h1, mul_one] at h
    exact nonneg_of_mul_nonneg_left ((abs_nonneg _).trans h) hs2
  have hτ1 : τ < 1 := by
    have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 2 * a - 1 by linarith) hτ0
    linarith
  have hξ : √(ϵ / 2) < 1 := by
    rw [Real.sqrt_lt' one_pos]
    linarith
  have hs' := (smoothingParam_pos hm hB hϵ₀).trans_le hη
  have hW : ((1 - √(ϵ / 2)) • pathCov r s Se t).PosDef :=
    (posDef_pathCov hSe hr hs hτ ha haτ ht).smul (by linarith)
  have hMM := sqrt_mul_transpose_sqrt hW.posSemidef
  refine geSmoothing_of_posSemidef hB (det_ne_zero_of_mul_transpose hMM hW.det_pos.ne') hϵ₀ hs'
    ?_ hη
  have hX : 0 ≤ (1 - √(ϵ / 2)) * (1 - τ) / (1 + (2 * a - 1) * τ) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith))
      (by have := mul_nonneg (show (0 : ℝ) ≤ 2 * a - 1 by linarith) hτ0; linarith)
  have e : (r * s * √((1 - √(ϵ / 2)) * (1 - τ) / (1 + (2 * a - 1) * τ))) ^ 2 =
      (1 - √(ϵ / 2)) * (r ^ 2 * s ^ 2 * (1 - τ) / (1 + (2 * a - 1) * τ)) := by
    rw [mul_pow, Real.sq_sqrt hX]
    ring
  rw [hMM, e, ← smul_smul, ← smul_sub]
  exact (posSemidef_pathCov_sub hSe hr hs hτ ha haτ ht).smul (by linarith)

/-- **The exact Rényi identity on `L(B)`** [ZKLY26, p. 7, l. 242]. -/
theorem renyiDiv_gaussianMeasure_eq {B Se M : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0)
    (hSe : Se.IsSymm) {r s τ a : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hτ : ∀ x, |x ⬝ᵥ (Se *ᵥ x)| ≤ τ * s ^ 2 * sqNorm x) (ha : 1 < a)
    (haτ : (2 * a - 1) * τ < 1) (hM : M * Mᵀ = pathCov r s Se 1) (c : Fin m → ℝ) :
    renyiDiv (2 * a) (gaussianMeasure B M c)
        (gaussianMeasure B ((r * s) • (1 : Matrix (Fin m) (Fin m) ℝ)) c) =
      ENNReal.ofReal (Real.exp (1 / (2 * (2 * a - 1)) *
          Real.log ((pathCov r s Se (2 * a)).det * (pathCov r s Se 0).det ^ (2 * a - 1) /
            (pathCov r s Se 1).det ^ (2 * a)) +
        (logMass B (pathCov r s Se (2 * a)) c - 2 * a * logMass B (pathCov r s Se 1) c +
          (2 * a - 1) * logMass B (pathCov r s Se 0) c) / (2 * a - 1))) := by
  have hτ1 : τ < 1 := not_le.1 fun h => by
    have := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ 2 * a - 1 by linarith)
    linarith
  have h0 : (0 : ℝ) ∈ Set.Icc 0 (2 * a) := ⟨le_rfl, by linarith⟩
  have h1 : (1 : ℝ) ∈ Set.Icc 0 (2 * a) := ⟨zero_le_one, by linarith⟩
  have h2 : (2 * a) ∈ Set.Icc 0 (2 * a) := ⟨by linarith, le_rfl⟩
  have hVPD := fun t (ht : t ∈ Set.Icc 0 (2 * a)) => posDef_pathCov hSe hr hs hτ ha haτ ht
  set ρ : ℝ → (Fin m → ℤ) → ℝ :=
    fun t z => Real.exp (-π * quadForm (pathCov r s Se t)⁻¹ (B *ᵥ ofInt z - c)) with hρdef
  have hsqrt := fun t (ht : t ∈ Set.Icc 0 (2 * a)) =>
    sqrt_mul_transpose_sqrt (hVPD t ht).posSemidef
  have hsum : ∀ t ∈ Set.Icc 0 (2 * a), Summable (ρ t) := fun t ht =>
    (summable_rho hB (det_ne_zero_of_mul_transpose (hsqrt t ht) (hVPD t ht).det_pos.ne') c).congr
      fun z => rho_eq_of_mul_transpose (hsqrt t ht) c _
  have hZ : ∀ t ∈ Set.Icc 0 (2 * a), 0 < ∑' z, ρ t z := fun t ht =>
    (hsum t ht).tsum_pos (fun _ => (Real.exp_pos _).le) 0 (Real.exp_pos _)
  have hM0 : ((r * s) • (1 : Matrix (Fin m) (Fin m) ℝ)) * ((r * s) • 1)ᵀ = pathCov r s Se 0 := by
    rw [smul_mul_transpose_smul, Matrix.transpose_one, Matrix.mul_one, pathCov_zero hs hτ hτ1]
  have hmass : ∀ {N : Matrix (Fin m) (Fin m) ℝ} {t : ℝ}, N * Nᵀ = pathCov r s Se t →
      ∀ z, gaussianMeasure B N c {z} = ENNReal.ofReal (ρ t z / ∑' z', ρ t z') := by
    intro N t hN z
    rw [gaussianMeasure_singleton, gaussianPMF, rhoSum, rho_eq_of_mul_transpose hN]
    simp_rw [rho_eq_of_mul_transpose hN]
    rfl
  have := isProbabilityMeasure_gaussianMeasure hB
    (det_ne_zero_of_mul_transpose hM (hVPD 1 h1).det_pos.ne') c
  have := isProbabilityMeasure_gaussianMeasure hB
    (det_ne_zero_of_mul_transpose hM0 (hVPD 0 h0).det_pos.ne') c
  rw [renyiDiv_eq_rpow (by linarith), FalconPrecision.RenyiHybrid.renyiMGF_eq_tsum (by linarith)]
  simp only [hmass hM, hmass hM0]
  have hq : ∀ z, ρ 1 z ^ (2 * a) * ρ 0 z ^ (1 - 2 * a) = ρ (2 * a) z := fun z => by
    simp only [hρdef]
    rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, inv_pathCov hSe hr hs hτ ha haτ h2,
      quadForm_add, quadForm_smul, quadForm_smul]
    ring_nf
  have hterm : ∀ z, ENNReal.ofReal (ρ 1 z / ∑' z', ρ 1 z') ^ (2 * a) *
      ENNReal.ofReal (ρ 0 z / ∑' z', ρ 0 z') ^ (1 - 2 * a) = ENNReal.ofReal (ρ (2 * a) z /
        ((∑' z', ρ 1 z') ^ (2 * a) * (∑' z', ρ 0 z') ^ (1 - 2 * a))) := fun z => by
    rw [ENNReal.ofReal_rpow_of_pos (div_pos (Real.exp_pos _) (hZ 1 h1)),
      ENNReal.ofReal_rpow_of_pos (div_pos (Real.exp_pos _) (hZ 0 h0)),
      ← ENNReal.ofReal_mul (by positivity), Real.div_rpow (Real.exp_pos _).le (hZ 1 h1).le,
      Real.div_rpow (Real.exp_pos _).le (hZ 0 h0).le, div_mul_div_comm, hq]
  have hpow : 0 < (∑' z', ρ 1 z') ^ (2 * a) * (∑' z', ρ 0 z') ^ (1 - 2 * a) :=
    mul_pos (Real.rpow_pos_of_pos (hZ 1 h1) _) (Real.rpow_pos_of_pos (hZ 0 h0) _)
  rw [tsum_congr hterm, ← ENNReal.ofReal_tsum_of_nonneg
    (fun z => div_nonneg (Real.exp_pos _).le hpow.le) ((hsum (2 * a) h2).div_const _),
    tsum_div_const, ENNReal.ofReal_rpow_of_nonneg (div_nonneg (hZ (2 * a) h2).le hpow.le)
      (inv_nonneg.2 (by linarith))]
  congr 1
  rw [Real.rpow_def_of_pos (div_pos (hZ (2 * a) h2) hpow)]
  congr 1
  have hφ : ∀ t, logMass B (pathCov r s Se t) c =
      Real.log (|B.det| * (pathCov r s Se t).det ^ (-(1 / 2) : ℝ) * ∑' z, ρ t z) := fun t => rfl
  have hBd : 0 < |B.det| := abs_pos.2 hB
  have hd := fun t (ht : t ∈ Set.Icc 0 (2 * a)) => (hVPD t ht).det_pos
  rw [hφ, hφ, hφ, Real.log_div (hZ (2 * a) h2).ne' hpow.ne',
    Real.log_mul (Real.rpow_pos_of_pos (hZ 1 h1) _).ne' (Real.rpow_pos_of_pos (hZ 0 h0) _).ne',
    Real.log_rpow (hZ 1 h1), Real.log_rpow (hZ 0 h0),
    Real.log_div (mul_pos (hd _ h2) (Real.rpow_pos_of_pos (hd _ h0) _)).ne'
      (Real.rpow_pos_of_pos (hd _ h1) _).ne',
    Real.log_mul (hd _ h2).ne' (Real.rpow_pos_of_pos (hd _ h0) _).ne', Real.log_rpow (hd _ h0),
    Real.log_rpow (hd _ h1)]
  rw [Real.log_mul (mul_pos hBd (Real.rpow_pos_of_pos (hd _ h2) _)).ne' (hZ _ h2).ne',
    Real.log_mul hBd.ne' (Real.rpow_pos_of_pos (hd _ h2) _).ne', Real.log_rpow (hd _ h2),
    Real.log_mul (mul_pos hBd (Real.rpow_pos_of_pos (hd _ h1) _)).ne' (hZ _ h1).ne',
    Real.log_mul hBd.ne' (Real.rpow_pos_of_pos (hd _ h1) _).ne', Real.log_rpow (hd _ h1),
    Real.log_mul (mul_pos hBd (Real.rpow_pos_of_pos (hd _ h0) _)).ne' (hZ _ h0).ne',
    Real.log_mul hBd.ne' (Real.rpow_pos_of_pos (hd _ h0) _).ne', Real.log_rpow (hd _ h0)]
  have hb : 2 * a - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- **The determinant term** [ZKLY26, p. 7, l. 244]:
`(1/(2(2a − 1))) log(det(V_{2a}) det(V₀)^{2a−1}/det(V₁)^{2a})
≤ a‖Σ‖_F²/(2s⁴(1 + τ)(1 − (2a − 1)τ))`. -/
theorem detTerm_le {Se : Matrix (Fin m) (Fin m) ℝ} (hSe : Se.IsSymm) {r s τ a : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hτ : ∀ x, |x ⬝ᵥ (Se *ᵥ x)| ≤ τ * s ^ 2 * sqNorm x) (ha : 1 < a)
    (haτ : (2 * a - 1) * τ < 1) :
    1 / (2 * (2 * a - 1)) *
        Real.log ((pathCov r s Se (2 * a)).det * (pathCov r s Se 0).det ^ (2 * a - 1) /
          (pathCov r s Se 1).det ^ (2 * a)) ≤
      a * (∑ i, ∑ j, Se i j ^ 2) / (2 * s ^ 4 * (1 + τ) * (1 - (2 * a - 1) * τ)) := by
  obtain ⟨U, lam, hU, hU', rfl⟩ := exists_spectral hSe
  have hl := abs_le_of_quadForm hU hτ
  have h0 : (0 : ℝ) ∈ Set.Icc 0 (2 * a) := ⟨le_rfl, by linarith⟩
  have h1 : (1 : ℝ) ∈ Set.Icc 0 (2 * a) := ⟨zero_le_one, by linarith⟩
  have h2 : (2 * a) ∈ Set.Icc 0 (2 * a) := ⟨by linarith, le_rfl⟩
  have hf0 := fun i => eig_facts hs (hl i) ha haτ h0
  have hf1 := fun i => eig_facts hs (hl i) ha haτ h1
  have hf2 := fun i => eig_facts hs (hl i) ha haτ h2
  have hne : ∀ {u : ℝ}, (∀ i, 1 - (2 * a - 1) * τ ≤ 1 + (u - 1) / s ^ 2 * lam i) →
      ∀ i, 1 + (u - 1) / s ^ 2 * lam i ≠ 0 := fun h i =>
    ((hf0 i).2.2.2.trans_le (h i)).ne'
  have hpos : ∀ {u : ℝ}, (∀ i, 1 - (2 * a - 1) * τ ≤ 1 + (u - 1) / s ^ 2 * lam i) →
      ∀ i, 0 < r ^ 2 * ((s ^ 2 - lam i) * (1 + (u - 1) / s ^ 2 * lam i)⁻¹) := fun h i =>
    mul_pos (pow_pos hr 2) (mul_pos (hf0 i).2.1 (inv_pos.2 ((hf0 i).2.2.2.trans_le (h i))))
  have hp2 := hpos fun i => (hf2 i).2.2.1
  have hp1 := hpos fun i => (hf1 i).2.2.1
  have hp0 := hpos fun i => (hf0 i).2.2.1
  rw [pathCov_spec hU hU' (hne fun i => (hf2 i).2.2.1),
    pathCov_spec hU hU' (hne fun i => (hf0 i).2.2.1),
    pathCov_spec hU hU' (hne fun i => (hf1 i).2.2.1), det_spec hU, det_spec hU, det_spec hU,
    sum_sq_spec hU]
  set b := 2 * a - 1 with hbdef
  have hb1 : 1 ≤ b := by linarith
  have hP := fun {f : Fin m → ℝ} (hf : ∀ i, 0 < f i) =>
    (Finset.prod_pos fun i _ => hf i : 0 < ∏ i, f i)
  have key : Real.log ((∏ i, r ^ 2 * ((s ^ 2 - lam i) * (1 + (2 * a - 1) / s ^ 2 * lam i)⁻¹)) *
      (∏ i, r ^ 2 * ((s ^ 2 - lam i) * (1 + (0 - 1) / s ^ 2 * lam i)⁻¹)) ^ b /
        (∏ i, r ^ 2 * ((s ^ 2 - lam i) * (1 + (1 - 1) / s ^ 2 * lam i)⁻¹)) ^ (2 * a)) =
      ∑ i, (-Real.log (1 + b * (lam i / s ^ 2)) - b * Real.log (1 - lam i / s ^ 2)) := by
    rw [Real.log_div (mul_pos (hP hp2) (Real.rpow_pos_of_pos (hP hp0) _)).ne'
        (Real.rpow_pos_of_pos (hP hp1) _).ne',
      Real.log_mul (hP hp2).ne' (Real.rpow_pos_of_pos (hP hp0) _).ne', Real.log_rpow (hP hp0),
      Real.log_rpow (hP hp1), Real.log_prod fun i _ => (hp2 i).ne',
      Real.log_prod fun i _ => (hp0 i).ne', Real.log_prod fun i _ => (hp1 i).ne',
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hA : 0 < r ^ 2 * (s ^ 2 - lam i) := mul_pos (pow_pos hr 2) (hf0 i).2.1
    have he2 : 0 < 1 + b * (lam i / s ^ 2) := by
      have := (hf2 i).2.2.2.trans_le (hf2 i).2.2.1
      rw [show b * (lam i / s ^ 2) = (2 * a - 1) / s ^ 2 * lam i by rw [hbdef]; ring]
      exact this
    have he0 : 0 < 1 - lam i / s ^ 2 := by
      have := (hf0 i).2.2.2.trans_le (hf0 i).2.2.1
      rw [show 1 - lam i / s ^ 2 = 1 + (0 - 1) / s ^ 2 * lam i by ring]
      exact this
    rw [show r ^ 2 * ((s ^ 2 - lam i) * (1 + (2 * a - 1) / s ^ 2 * lam i)⁻¹) =
        r ^ 2 * (s ^ 2 - lam i) * (1 + b * (lam i / s ^ 2))⁻¹ by rw [hbdef]; ring,
      show r ^ 2 * ((s ^ 2 - lam i) * (1 + (0 - 1) / s ^ 2 * lam i)⁻¹) =
        r ^ 2 * (s ^ 2 - lam i) * (1 - lam i / s ^ 2)⁻¹ by ring,
      show r ^ 2 * ((s ^ 2 - lam i) * (1 + (1 - 1) / s ^ 2 * lam i)⁻¹) =
        r ^ 2 * (s ^ 2 - lam i) by simp,
      Real.log_mul hA.ne' (inv_pos.2 he2).ne', Real.log_mul hA.ne' (inv_pos.2 he0).ne',
      Real.log_inv, Real.log_inv, hbdef]
    ring
  rw [key]
  have hτ0 : ∀ i, 0 ≤ τ := fun i => (abs_nonneg _).trans (hf0 i).1
  have hsum : ∑ i, (-Real.log (1 + b * (lam i / s ^ 2)) - b * Real.log (1 - lam i / s ^ 2)) ≤
      b * (b + 1) / (2 * ((1 + τ) * (1 - b * τ))) * ∑ i, (lam i / s ^ 2) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => (log_bound hb1 (hf0 i).1 haτ).trans_eq (by ring)
  have hs4 : ∑ i, (lam i / s ^ 2) ^ 2 = (∑ i, lam i ^ 2) / s ^ 4 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hs4] at hsum
  have hb0 : (0 : ℝ) < 2 * b := by linarith
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hτ0' := hτ0 ⟨0, hm⟩
  have hD1 : 1 + τ ≠ 0 := by linarith
  have hD2 : 1 - (2 * a - 1) * τ ≠ 0 := by linarith
  have hs0 := hs.ne'
  have hb2 : 2 * a - 1 ≠ 0 := by linarith
  have hb3 : -1 + a * 2 ≠ 0 := by linarith
  calc 1 / (2 * b) * ∑ i, (-Real.log (1 + b * (lam i / s ^ 2)) - b * Real.log (1 - lam i / s ^ 2))
      ≤ 1 / (2 * b) * (b * (b + 1) / (2 * ((1 + τ) * (1 - b * τ))) * ((∑ i, lam i ^ 2) / s ^ 4)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = a * (∑ i, lam i ^ 2) / (2 * s ^ 4 * (1 + τ) * (1 - (2 * a - 1) * τ)) := by
        rw [hbdef]
        field_simp
        ring

/-- **Poisson summation for `φ`** [ZKLY26, p. 8, l. 247-249]:
`e^{φ} = Σ_{v∈L(B)*} e^{−πvᵗVv} cos(2π⟨v, c⟩)`, with `L(B)* = L((B⁻¹)ᵗ)` (`points_dualBasis`). -/
theorem exp_logMass_eq {B V : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0) (hV : V.PosDef)
    (c : Fin m → ℝ) :
    Real.exp (logMass B V c) =
      ∑' y : Fin m → ℤ, Real.exp (-π * quadForm V (dualBasis B *ᵥ ofInt y)) *
        Real.cos (2 * π * ((dualBasis B *ᵥ ofInt y) ⬝ᵥ c)) := by
  have hMM := sqrt_mul_transpose_sqrt hV.posSemidef
  have hMd := det_ne_zero_of_mul_transpose hMM hV.det_pos.ne'
  have hsum : ∑' z : Fin m → ℤ, Real.exp (-π * quadForm V⁻¹ (B *ᵥ ofInt z - c)) =
      rhoSum B (CFC.sqrt V) c :=
    tsum_congr fun z => (rho_eq_of_mul_transpose hMM c _).symm
  have hdetV : V.det = |(CFC.sqrt V).det| ^ 2 := by
    have h := congrArg Matrix.det hMM
    rw [Matrix.det_mul, Matrix.det_transpose] at h
    rw [sq_abs, sq]
    exact h.symm
  have hpowd : V.det ^ (-(1 / 2) : ℝ) = |(CFC.sqrt V).det|⁻¹ := by
    rw [hdetV, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    norm_num
    rw [Real.rpow_neg_one]
  rw [logMass, hsum, Real.exp_log (mul_pos (mul_pos (abs_pos.2 hB)
    (Real.rpow_pos_of_pos hV.det_pos _)) (rhoSum_pos hB hMd c)), rhoSum_eq_tsum_dual_real hB hMd c,
    hpowd]
  have hB' := abs_pos.2 hB
  have hM' := abs_pos.2 hMd
  rw [← mul_assoc, show |B.det| * |(CFC.sqrt V).det|⁻¹ * (|(CFC.sqrt V).det| / |B.det|) = 1 by
    field_simp, one_mul]
  refine tsum_congr fun y => ?_
  rw [← quadForm_transpose_mul_self, Matrix.transpose_transpose, hMM]

/-- `x e^{−x} ≤ 2 e^{−x/2}` for `x ≥ 0`. -/
private theorem mul_exp_neg_le (x : ℝ) : x * Real.exp (-x) ≤ 2 * Real.exp (-(x / 2)) := by
  have h := Real.add_one_le_exp (x / 2)
  calc x * Real.exp (-x) ≤ 2 * Real.exp (x / 2) * Real.exp (-x) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    _ = 2 * Real.exp (-(x / 2)) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf

/-- `x² e^{−x} ≤ 16 e^{−x/2}` for `x ≥ 0`. -/
private theorem sq_mul_exp_neg_le {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 * Real.exp (-x) ≤ 16 * Real.exp (-(x / 2)) := by
  have h := Real.add_one_le_exp (x / 4)
  have h1 : x ≤ 4 * Real.exp (x / 4) := by linarith
  have h2 : x ^ 2 ≤ 16 * Real.exp (x / 2) := by
    have := pow_le_pow_left₀ hx h1 2
    rw [mul_pow, ← Real.exp_nat_mul] at this
    norm_num at this
    rwa [show (2 : ℝ) * (x / 4) = x / 2 by ring] at this
  calc x ^ 2 * Real.exp (-x) ≤ 16 * Real.exp (x / 2) * Real.exp (-x) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = 16 * Real.exp (-(x / 2)) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf

/-- `x e^{−x} ≤ e^{−(1−ξ)x}/(eξ)` for `x ≥ 0`, `ξ > 0` [ZKLY26, p. 8, l. 254]. -/
private theorem mul_exp_neg_le_xi {x ξ : ℝ} (hξ : 0 < ξ) :
    x * Real.exp (-x) ≤ Real.exp (-((1 - ξ) * x)) / (Real.exp 1 * ξ) := by
  have h := Real.add_one_le_exp (ξ * x - 1)
  rw [le_div_iff₀ (mul_pos (Real.exp_pos _) hξ)]
  calc x * Real.exp (-x) * (Real.exp 1 * ξ) = (ξ * x) * Real.exp (-x) * Real.exp 1 := by ring
    _ ≤ Real.exp (ξ * x - 1) * Real.exp (-x) * Real.exp 1 := by
        gcongr
        linarith
    _ = Real.exp (-((1 - ξ) * x)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        ring_nf

/-- `x² e^{−x} ≤ 4 e^{−(1−ξ)x}/(e²ξ²)` for `ξ > 0` [ZKLY26, p. 8, l. 254]. -/
private theorem sq_mul_exp_neg_le_xi {x ξ : ℝ} (hx : 0 ≤ x) (hξ : 0 < ξ) :
    x ^ 2 * Real.exp (-x) ≤ 4 * Real.exp (-((1 - ξ) * x)) / (Real.exp 1 ^ 2 * ξ ^ 2) := by
  have h := Real.add_one_le_exp (ξ * x / 2 - 1)
  have h0 : 0 ≤ ξ * x / 2 := by positivity
  have h1 : (ξ * x / 2) ^ 2 ≤ Real.exp (ξ * x / 2 - 1) ^ 2 := pow_le_pow_left₀ h0 (by linarith) 2
  rw [le_div_iff₀ (by positivity)]
  calc x ^ 2 * Real.exp (-x) * (Real.exp 1 ^ 2 * ξ ^ 2)
      = 4 * (ξ * x / 2) ^ 2 * Real.exp (-x) * Real.exp 1 ^ 2 := by ring
    _ ≤ 4 * Real.exp (ξ * x / 2 - 1) ^ 2 * Real.exp (-x) * Real.exp 1 ^ 2 := by gcongr
    _ = 4 * Real.exp (-((1 - ξ) * x)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, mul_assoc, mul_assoc, ← Real.exp_add,
          ← Real.exp_add]
        ring_nf

/-- The eigenvalue path `A/(1 + (t − 1)θ)` and its first two derivatives. -/
private theorem hasDerivAt_path (A θ t : ℝ) (he : 1 + (t - 1) * θ ≠ 0) :
    HasDerivAt (fun t => A / (1 + (t - 1) * θ)) (-(A * θ) / (1 + (t - 1) * θ) ^ 2) t ∧
      HasDerivAt (fun t => -(A * θ) / (1 + (t - 1) * θ) ^ 2)
        (2 * A * θ ^ 2 / (1 + (t - 1) * θ) ^ 3) t := by
  have hd : HasDerivAt (fun t => 1 + (t - 1) * θ) θ t := by
    simpa using (((hasDerivAt_id t).sub_const 1).mul_const θ).const_add 1
  constructor
  · convert (hasDerivAt_const t A).div hd he using 1
    ring
  · convert (hasDerivAt_const t (-(A * θ))).div (hd.pow 2) (pow_ne_zero 2 he) using 1
    simp only [Pi.pow_apply]
    generalize 1 + (t - 1) * θ = E at he ⊢
    field_simp
    ring

/-- `|θ/e| ≤ τ/μ` gives `|−Aθ/e²| ≤ (τ/μ)(A/e)` and `|2Aθ²/e³| ≤ 2(τ/μ)²(A/e)`. -/
private theorem path_bounds {A θ τ e μ : ℝ} (hA : 0 ≤ A) (hθ : |θ| ≤ τ) (hμ : 0 < μ)
    (he : μ ≤ e) :
    |-(A * θ) / e ^ 2| ≤ τ / μ * (A / e) ∧ |2 * A * θ ^ 2 / e ^ 3| ≤ 2 * (τ / μ) ^ 2 * (A / e) := by
  have he0 : 0 < e := hμ.trans_le he
  have hq : |θ| / e ≤ τ / μ := div_le_div₀ ((abs_nonneg _).trans hθ) hθ hμ he
  constructor
  · rw [abs_div, abs_neg, abs_mul, abs_of_nonneg hA, abs_of_pos (pow_pos he0 2)]
    calc A * |θ| / e ^ 2 = |θ| / e * (A / e) := by field_simp
      _ ≤ τ / μ * (A / e) := mul_le_mul_of_nonneg_right hq (div_nonneg hA he0.le)
  · rw [abs_div, abs_mul, abs_mul, abs_of_nonneg hA, abs_of_pos (pow_pos he0 3), abs_two,
      abs_pow]
    calc 2 * A * |θ| ^ 2 / e ^ 3 = 2 * (|θ| / e) ^ 2 * (A / e) := by field_simp
      _ ≤ 2 * (τ / μ) ^ 2 * (A / e) := by
        gcongr

/-- Termwise differentiation of `t ↦ Σ_y e^{−Q_t(y)} c_y` twice on an open interval `J`, given
`|Q′| ≤ KQ`, `|Q″| ≤ 2K²Q`, `Q ≥ 0` and a summable majorant of `e^{−Q/2}`. -/
private theorem hasDerivAt_dualSum {ι : Type*} {J : Set ℝ} (hJ : IsOpen J)
    (hJc : IsPreconnected J) {t0 : ℝ} (ht0 : t0 ∈ J) {Q Q1 Q2 : ℝ → ι → ℝ} {cs g : ι → ℝ}
    {K : ℝ} (hK : 0 ≤ K) (hg : Summable g) (hcs : ∀ y, |cs y| ≤ 1)
    (hQd : ∀ y, ∀ t ∈ J, HasDerivAt (fun t => Q t y) (Q1 t y) t)
    (hQ1d : ∀ y, ∀ t ∈ J, HasDerivAt (fun t => Q1 t y) (Q2 t y) t)
    (hQnn : ∀ t ∈ J, ∀ y, 0 ≤ Q t y) (hb1 : ∀ t ∈ J, ∀ y, |Q1 t y| ≤ K * Q t y)
    (hb2 : ∀ t ∈ J, ∀ y, |Q2 t y| ≤ 2 * K ^ 2 * Q t y)
    (hexp : ∀ t ∈ J, ∀ y, Real.exp (-(Q t y / 2)) ≤ g y) (t : ℝ) (ht : t ∈ J) :
    HasDerivAt (fun t => ∑' y, Real.exp (-Q t y) * cs y)
        (∑' y, -Q1 t y * Real.exp (-Q t y) * cs y) t ∧
      HasDerivAt (fun t => ∑' y, -Q1 t y * Real.exp (-Q t y) * cs y)
        (∑' y, (Q1 t y ^ 2 - Q2 t y) * Real.exp (-Q t y) * cs y) t := by
  have hGd : ∀ y, ∀ t ∈ J, HasDerivAt (fun t => Real.exp (-Q t y) * cs y)
      (-Q1 t y * Real.exp (-Q t y) * cs y) t := fun y t ht => by
    have h := (((hQd y t ht).neg).exp).mul_const (cs y)
    convert h using 1
    simp only [Pi.neg_apply]
    ring
  have hG1d : ∀ y, ∀ t ∈ J, HasDerivAt (fun t => -Q1 t y * Real.exp (-Q t y) * cs y)
      ((Q1 t y ^ 2 - Q2 t y) * Real.exp (-Q t y) * cs y) t := fun y t ht => by
    have h := ((((hQ1d y t ht).neg).mul ((hQd y t ht).neg.exp))).mul_const (cs y)
    convert h using 1
    simp only [Pi.neg_apply]
    ring
  have hG0b : ∀ t ∈ J, ∀ y, ‖Real.exp (-Q t y) * cs y‖ ≤ g y := fun t ht y => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-Q t y) * |cs y| ≤ Real.exp (-(Q t y / 2)) * 1 :=
          mul_le_mul (Real.exp_le_exp.2 (by linarith [hQnn t ht y])) (hcs y) (abs_nonneg _)
            (Real.exp_pos _).le
      _ ≤ g y := by rw [mul_one]; exact hexp t ht y
  have hG1b : ∀ t ∈ J, ∀ y, ‖-Q1 t y * Real.exp (-Q t y) * cs y‖ ≤ 2 * K * g y :=
    fun t ht y => by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _)]
    have h2 := mul_exp_neg_le (Q t y)
    calc |Q1 t y| * Real.exp (-Q t y) * |cs y| ≤ K * Q t y * Real.exp (-Q t y) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right (hb1 t ht y) (Real.exp_pos _).le) (hcs y)
            (abs_nonneg _) (mul_nonneg (mul_nonneg hK (hQnn t ht y)) (Real.exp_pos _).le)
      _ ≤ K * (2 * Real.exp (-(Q t y / 2))) := by
          rw [mul_one, mul_assoc]
          exact mul_le_mul_of_nonneg_left h2 hK
      _ ≤ 2 * K * g y := by
          rw [← mul_assoc, mul_comm K 2]
          exact mul_le_mul_of_nonneg_left (hexp t ht y) (by positivity)
  have hG2b : ∀ t ∈ J, ∀ y, ‖(Q1 t y ^ 2 - Q2 t y) * Real.exp (-Q t y) * cs y‖ ≤
      20 * K ^ 2 * g y := fun t ht y => by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hq := hQnn t ht y
    have h3 := mul_exp_neg_le (Q t y)
    have h4 := sq_mul_exp_neg_le hq
    have hsq : Q1 t y ^ 2 ≤ K ^ 2 * Q t y ^ 2 := by
      rw [← sq_abs (Q1 t y), ← mul_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hb1 t ht y) 2
    have hab : |Q1 t y ^ 2 - Q2 t y| ≤ K ^ 2 * Q t y ^ 2 + 2 * K ^ 2 * Q t y :=
      (abs_sub _ _).trans (by rw [abs_of_nonneg (sq_nonneg _)]; linarith [hb2 t ht y])
    have he := Real.exp_pos (-Q t y)
    calc |Q1 t y ^ 2 - Q2 t y| * Real.exp (-Q t y) * |cs y|
        ≤ (K ^ 2 * Q t y ^ 2 + 2 * K ^ 2 * Q t y) * Real.exp (-Q t y) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right hab he.le) (hcs y) (abs_nonneg _)
            (by positivity)
      _ = K ^ 2 * (Q t y ^ 2 * Real.exp (-Q t y)) + 2 * K ^ 2 * (Q t y * Real.exp (-Q t y)) := by
          ring
      _ ≤ K ^ 2 * (16 * Real.exp (-(Q t y / 2))) + 2 * K ^ 2 * (2 * Real.exp (-(Q t y / 2))) := by
          gcongr
      _ = 20 * K ^ 2 * Real.exp (-(Q t y / 2)) := by ring
      _ ≤ 20 * K ^ 2 * g y := mul_le_mul_of_nonneg_left (hexp t ht y) (by positivity)
  exact ⟨hasDerivAt_tsum_of_isPreconnected (hg.mul_left (2 * K)) hJ hJc hGd
      (fun y t ht => hG1b t ht y) ht0 (Summable.of_norm_bounded hg (hG0b t0 ht0)) ht,
    hasDerivAt_tsum_of_isPreconnected (hg.mul_left (20 * K ^ 2)) hJ hJc hG1d
      (fun y t ht => hG2b t ht y) ht0 (Summable.of_norm_bounded (hg.mul_left _) (hG1b t0 ht0)) ht⟩

/-- The bracket of [ZKLY26, p. 8, l. 256]: `16/e² + 8ξ/e + 16ξ²/e² ≤ 5` for `0 ≤ ξ ≤ 1/2`, from
`e > 2.7182818283`. -/
private theorem bracket_le_five {ξ E : ℝ} (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 2)
    (hE : 2.7182818283 < E) :
    16 * (1 / E) ^ 2 + 8 * (ξ * (1 / E)) + 16 * (ξ ^ 2 * (1 / E) ^ 2) ≤ 5 := by
  have hE0 : 0 < E := by linarith
  have hx : 1 / E ≤ 368 / 1000 := by
    rw [div_le_div_iff₀ hE0 (by norm_num)]
    linarith
  have hx0 : 0 ≤ 1 / E := by positivity
  have h1 : (1 / E) ^ 2 ≤ (368 / 1000) ^ 2 := pow_le_pow_left₀ hx0 hx 2
  have h2 : ξ * (1 / E) ≤ 1 / 2 * (368 / 1000) := mul_le_mul hξ1 hx hx0 (by norm_num)
  have h3 : ξ ^ 2 ≤ 1 / 4 := by nlinarith [hξ1, hξ0]
  have h4 : ξ ^ 2 * (1 / E) ^ 2 ≤ 1 / 4 * (368 / 1000) ^ 2 :=
    mul_le_mul h3 h1 (sq_nonneg _) (by norm_num)
  norm_num at h1 h2 h4 ⊢
  linarith

/-- The `|φ″|` bracket [ZKLY26, p. 8, l. 252-256] at one `t`: with `|Q′| ≤ δQ`, `|Q″| ≤ 2δ²Q`,
`Q ≥ 0`, `Q(y₀) = 0` and `Σ_y e^{−(1−ξ)Q(y)} ≤ 1 + ϵ` (`ξ = √(ϵ/2)`, `ϵ ≤ 1/2`), the sums
`F = Σ e^{−Q}c`, `F′`, `F″` satisfy `F > 0` and `|(F″F − F′²)/F²| ≤ 5δ²`. -/
private theorem dualSum_bound {ι : Type*} (y0 : ι) {Q Q1 Q2 cs : ι → ℝ}
    {δ ϵ F F1 F2 : ℝ} (hδ : 0 ≤ δ) (hϵ₀ : 0 < ϵ) (hϵ : ϵ ≤ 1 / 2) (hcs : ∀ y, |cs y| ≤ 1)
    (hcs0 : cs y0 = 1) (hQnn : ∀ y, 0 ≤ Q y) (hQ0 : Q y0 = 0) (hQ10 : Q1 y0 = 0)
    (hQ20 : Q2 y0 = 0) (hb1 : ∀ y, |Q1 y| ≤ δ * Q y) (hb2 : ∀ y, |Q2 y| ≤ 2 * δ ^ 2 * Q y)
    (hsumH : Summable fun y => Real.exp (-((1 - √(ϵ / 2)) * Q y)))
    (hH : ∑' y, Real.exp (-((1 - √(ϵ / 2)) * Q y)) ≤ 1 + ϵ)
    (hF : F = ∑' y, Real.exp (-Q y) * cs y) (hF1 : F1 = ∑' y, -Q1 y * Real.exp (-Q y) * cs y)
    (hF2 : F2 = ∑' y, (Q1 y ^ 2 - Q2 y) * Real.exp (-Q y) * cs y) :
    0 < F ∧ |(F2 * F - F1 * F1) / F ^ 2| ≤ 5 * δ ^ 2 := by
  classical
  set ξ := √(ϵ / 2) with hξdef
  have hξ0 : 0 < ξ := Real.sqrt_pos.2 (by positivity)
  have hξ2 : ξ ^ 2 = ϵ / 2 := Real.sq_sqrt (by positivity)
  have hξ1 : ξ ≤ 1 / 2 := by nlinarith [hξ2, hξ0, hϵ]
  set E := Real.exp 1 with hEdef
  have hE : 2.7182818283 < E := Real.exp_one_gt_d9
  set H : ι → ℝ := fun y => Real.exp (-((1 - ξ) * Q y)) with hHdef
  set H' : ι → ℝ := fun y => if y = y0 then 0 else H y with hH'def
  have hH'le : ∀ y, H' y ≤ H y := fun y => by
    simp only [hH'def]
    split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl
  have hH'0 : ∀ y, 0 ≤ H' y := fun y => by
    simp only [hH'def]
    split_ifs
    · exact le_rfl
    · exact (Real.exp_pos _).le
  have hsumH' : Summable H' := Summable.of_nonneg_of_le hH'0 hH'le hsumH
  have hind : Summable fun y : ι => if y = y0 then (1 : ℝ) else 0 :=
    (hasSum_ite_eq y0 (1 : ℝ)).summable
  have hHsplit : ∀ y, H y = (if y = y0 then 1 else 0) + H' y := fun y => by
    simp only [hH'def]
    split_ifs with h
    · rw [h, hHdef]
      simp [hQ0]
    · ring
  have hHz : ∑' y, H' y ≤ ϵ := by
    have h : ∑' y, H y = ∑' y, ((if y = y0 then (1 : ℝ) else 0) + H' y) := tsum_congr hHsplit
    rw [hind.tsum_add hsumH', tsum_ite_eq] at h
    linarith
  have hGlow : ∀ y, (if y = y0 then 1 else 0) - H' y ≤ Real.exp (-Q y) * cs y := fun y => by
    by_cases h : y = y0
    · subst h
      simp [hQ0, hcs0, hH'def]
    · simp only [h, ↓reduceIte, hH'def, zero_sub]
      have h1 : -Real.exp (-Q y) ≤ Real.exp (-Q y) * cs y := by
        have := (abs_le.1 (hcs y)).1
        nlinarith [Real.exp_pos (-Q y)]
      have h2 : Real.exp (-Q y) ≤ H y :=
        Real.exp_le_exp.2 (by nlinarith [hQnn y, hξ0])
      linarith
  have hG1up : ∀ y, |-Q1 y * Real.exp (-Q y) * cs y| ≤ δ / (E * ξ) * H' y := fun y => by
    by_cases h : y = y0
    · subst h
      simp [hQ10, hH'def]
    · simp only [hH'def, h, ↓reduceIte]
      rw [abs_mul, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _)]
      have h3 := mul_exp_neg_le_xi (x := Q y) hξ0
      calc |Q1 y| * Real.exp (-Q y) * |cs y| ≤ δ * Q y * Real.exp (-Q y) * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_right (hb1 y) (Real.exp_pos _).le) (hcs y)
              (abs_nonneg _) (mul_nonneg (mul_nonneg hδ (hQnn y)) (Real.exp_pos _).le)
        _ ≤ δ * (H y / (E * ξ)) := by
            rw [mul_one, mul_assoc]
            exact mul_le_mul_of_nonneg_left h3 hδ
        _ = δ / (E * ξ) * H y := by ring
  have hG2up : ∀ y, |(Q1 y ^ 2 - Q2 y) * Real.exp (-Q y) * cs y| ≤
      δ ^ 2 * (4 / (E ^ 2 * ξ ^ 2) + 2 / (E * ξ)) * H' y := fun y => by
    by_cases h : y = y0
    · subst h
      simp [hQ10, hQ20, hH'def]
    · simp only [hH'def, h, ↓reduceIte]
      rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
      have hq := hQnn y
      have hsq : Q1 y ^ 2 ≤ δ ^ 2 * Q y ^ 2 := by
        rw [← sq_abs (Q1 y), ← mul_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hb1 y) 2
      have hab : |Q1 y ^ 2 - Q2 y| ≤ δ ^ 2 * Q y ^ 2 + 2 * δ ^ 2 * Q y :=
        (abs_sub _ _).trans (by rw [abs_of_nonneg (sq_nonneg _)]; linarith [hb2 y])
      have h3 := mul_exp_neg_le_xi (x := Q y) hξ0
      have h4 := sq_mul_exp_neg_le_xi hq hξ0
      have he := Real.exp_pos (-Q y)
      calc |Q1 y ^ 2 - Q2 y| * Real.exp (-Q y) * |cs y|
          ≤ (δ ^ 2 * Q y ^ 2 + 2 * δ ^ 2 * Q y) * Real.exp (-Q y) * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_right hab he.le) (hcs y) (abs_nonneg _)
              (by positivity)
        _ = δ ^ 2 * (Q y ^ 2 * Real.exp (-Q y)) + 2 * δ ^ 2 * (Q y * Real.exp (-Q y)) := by
            ring
        _ ≤ δ ^ 2 * (4 * H y / (E ^ 2 * ξ ^ 2)) + 2 * δ ^ 2 * (H y / (E * ξ)) := by
            gcongr
        _ = δ ^ 2 * (4 / (E ^ 2 * ξ ^ 2) + 2 / (E * ξ)) * H y := by ring
  have hsumG : Summable fun y => Real.exp (-Q y) * cs y :=
    Summable.of_norm_bounded hsumH fun y => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc Real.exp (-Q y) * |cs y| ≤ Real.exp (-Q y) * 1 :=
            mul_le_mul_of_nonneg_left (hcs y) (Real.exp_pos _).le
        _ ≤ H y := by
            rw [mul_one]
            exact Real.exp_le_exp.2 (by nlinarith [hQnn y, hξ0])
  have habs : ∀ {f : ι → ℝ} {C : ℝ}, 0 ≤ C → (∀ y, |f y| ≤ C * H' y) →
      |∑' y, f y| ≤ C * ϵ := by
    intro f C hC hfy
    have hn : Summable fun y => ‖f y‖ := Summable.of_nonneg_of_le (fun y => norm_nonneg _)
      (fun y => (hfy y)) (hsumH'.mul_left C)
    calc |∑' y, f y| = ‖∑' y, f y‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑' y, ‖f y‖ := norm_tsum_le_tsum_norm hn
      _ ≤ ∑' y, C * H' y := Summable.tsum_le_tsum hfy hn (hsumH'.mul_left C)
      _ = C * ∑' y, H' y := tsum_mul_left
      _ ≤ C * ϵ := mul_le_mul_of_nonneg_left hHz hC
  have hE0 : 0 < E := by linarith
  have hF1b := habs (div_nonneg hδ (mul_pos hE0 hξ0).le) hG1up
  have hF2b := habs (by positivity) hG2up
  rw [← hF1] at hF1b
  rw [← hF2] at hF2b
  have hFl : 1 - ϵ ≤ F := by
    have h := Summable.tsum_le_tsum hGlow (hind.sub hsumH') hsumG
    rw [hind.tsum_sub hsumH', tsum_ite_eq, ← hF] at h
    linarith
  have hFp : 0 < F := by linarith
  refine ⟨hFp, ?_⟩
  have hϵ1 : 1 / 2 ≤ F := by linarith
  rw [show (F2 * F - F1 * F1) / F ^ 2 = F2 / F - (F1 / F) ^ 2 by field_simp]
  have hA1 : |F1 / F| ≤ 2 * (δ / (E * ξ) * ϵ) := by
    rw [abs_div, abs_of_pos hFp, div_le_iff₀ hFp]
    nlinarith [hF1b, abs_nonneg F1, hϵ1]
  have hA2 : |F2 / F| ≤ 2 * (δ ^ 2 * (4 / (E ^ 2 * ξ ^ 2) + 2 / (E * ξ)) * ϵ) := by
    rw [abs_div, abs_of_pos hFp, div_le_iff₀ hFp]
    nlinarith [hF2b, abs_nonneg F2, hϵ1]
  have hϵξ : ϵ = 2 * ξ ^ 2 := by rw [hξ2]; ring
  have k1 : δ / (E * ξ) * ϵ = 2 * δ * ξ / E := by
    rw [hϵξ]
    field_simp
  have k2 : δ ^ 2 * (4 / (E ^ 2 * ξ ^ 2) + 2 / (E * ξ)) * ϵ =
      δ ^ 2 * (8 / E ^ 2 + 4 * ξ / E) := by
    rw [hϵξ]
    field_simp
    ring
  rw [k1] at hA1
  rw [k2] at hA2
  have e2 : 2 * (δ ^ 2 * (8 / E ^ 2 + 4 * ξ / E)) + (2 * (2 * δ * ξ / E)) ^ 2 =
      δ ^ 2 * (16 * (1 / E) ^ 2 + 8 * (ξ * (1 / E)) + 16 * (ξ ^ 2 * (1 / E) ^ 2)) := by
    field_simp
    ring
  have hb := bracket_le_five hξ0.le hξ1 hE
  calc |F2 / F - (F1 / F) ^ 2| ≤ |F2 / F| + |F1 / F| ^ 2 := by
        rw [← abs_pow]
        exact abs_sub _ _
    _ ≤ 2 * (δ ^ 2 * (8 / E ^ 2 + 4 * ξ / E)) + (2 * (2 * δ * ξ / E)) ^ 2 :=
        add_le_add hA2 (pow_le_pow_left₀ (abs_nonneg _) hA1 2)
    _ = δ ^ 2 * (16 * (1 / E) ^ 2 + 8 * (ξ * (1 / E)) + 16 * (ξ ^ 2 * (1 / E) ^ 2)) := e2
    _ ≤ 5 * δ ^ 2 := by
        rw [mul_comm 5]
        exact mul_le_mul_of_nonneg_left hb (sq_nonneg δ)

/-- On `(−ρ, 2a + ρ)` with `ρτ ≤ (1 − (2a − 1)τ)/2`, the denominators `1 + (t − 1)θ` of the path
lie in `[(1 − (2a − 1)τ)/2, 2]` for `|θ| ≤ τ`. -/
private theorem one_add_mem_Icc_of_mem_Ioo {θ τ a ρ t : ℝ} (hθ : |θ| ≤ τ) (ha : 1 < a)
    (haτ : (2 * a - 1) * τ < 1) (hρ : 0 ≤ ρ) (hρτ : ρ * τ ≤ (1 - (2 * a - 1) * τ) / 2)
    (ht : t ∈ Set.Ioo (-ρ) (2 * a + ρ)) :
    (1 - (2 * a - 1) * τ) / 2 ≤ 1 + (t - 1) * θ ∧ 1 + (t - 1) * θ ≤ 2 := by
  have h1 : |t - 1| ≤ 2 * a - 1 + ρ := abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h2 : |(t - 1) * θ| ≤ (2 * a - 1 + ρ) * τ := by
    rw [abs_mul]
    exact mul_le_mul h1 hθ (abs_nonneg _) (by linarith)
  have h4 : (2 * a - 1 + ρ) * τ = (2 * a - 1) * τ + ρ * τ := by ring
  exact ⟨by linarith [neg_abs_le ((t - 1) * θ)], by linarith [le_abs_self ((t - 1) * θ)]⟩

/-- A termwise bound `|wᵢ| ≤ K vᵢ` passes to `π Σᵢ wᵢ uᵢ²`. -/
private theorem abs_pi_sum_le {w v : Fin m → ℝ} {K : ℝ} (u : Fin m → ℝ)
    (h : ∀ i, |w i| ≤ K * v i) : |π * ∑ i, w i * u i ^ 2| ≤ K * (π * ∑ i, v i * u i ^ 2) := by
  rw [abs_mul, abs_of_pos Real.pi_pos, mul_left_comm, Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun i _ => ?_)) Real.pi_pos.le
  rw [abs_mul, abs_of_nonneg (sq_nonneg (u i)), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (h i) (sq_nonneg _)

/-- **The `|φ″|` bound** [ZKLY26, p. 8, l. 250-256], including the termwise differentiation of
the dual sum: on `[0, 2a]`, `φ(t) = logMass B V_t c` is twice differentiable with
`|φ″(t)| ≤ 5τ²/(1 − (2a − 1)τ)²`, for `0 < ϵ ≤ 1/2` under the target-width condition. -/
theorem exists_deriv2_logMass_le {B Se : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0)
    (hSe : Se.IsSymm) {r s τ a ϵ : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hτ : ∀ x, |x ⬝ᵥ (Se *ᵥ x)| ≤ τ * s ^ 2 * sqNorm x) (ha : 1 < a)
    (haτ : (2 * a - 1) * τ < 1) (hϵ₀ : 0 < ϵ) (hϵ : ϵ ≤ 1 / 2)
    (hη : smoothingParam ϵ B ≤
      r * s * √((1 - √(ϵ / 2)) * (1 - τ) / (1 + (2 * a - 1) * τ)))
    (c : Fin m → ℝ) :
    ∃ φ' φ'' : ℝ → ℝ, ∀ t ∈ Set.Icc 0 (2 * a),
      HasDerivAt (fun t => logMass B (pathCov r s Se t) c) (φ' t) t ∧
        HasDerivAt φ' (φ'' t) t ∧ |φ'' t| ≤ 5 * τ ^ 2 / (1 - (2 * a - 1) * τ) ^ 2 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨fun _ => 0, fun _ => 0, fun t _ => ⟨?_, hasDerivAt_const _ _, ?_⟩⟩
    · have hc : (fun t => logMass B (pathCov r s Se t) c) =
          fun _ => logMass B (pathCov r s Se 0) c :=
        funext fun t => by rw [Subsingleton.elim (pathCov r s Se t) (pathCov r s Se 0)]
      rw [hc]
      exact hasDerivAt_const _ _
    · rw [abs_zero]
      positivity
  obtain ⟨U, lam, hU, hU', rfl⟩ := exists_spectral hSe
  have hl := abs_le_of_quadForm hU hτ
  have hs2 : 0 < s ^ 2 := by positivity
  have hτ0 : 0 ≤ τ := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hl ⟨0, hm⟩)) hs2
  have hτ1 : τ < 1 := by
    have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 2 * a - 1 by linarith) hτ0
    linarith
  set θ : Fin m → ℝ := fun i => lam i / s ^ 2 with hθdef
  have hθ : ∀ i, |θ i| ≤ τ := fun i => by
    rw [hθdef, abs_div, abs_of_pos hs2, div_le_iff₀ hs2]
    exact hl i
  set Av : Fin m → ℝ := fun i => r ^ 2 * (s ^ 2 - lam i) with hAdef
  have hA : ∀ i, r ^ 2 * s ^ 2 * (1 - τ) ≤ Av i := fun i => by
    have h1 := (abs_le.1 (hl i)).2
    have h2 := pow_pos hr 2
    rw [hAdef]
    nlinarith [mul_le_mul_of_nonneg_left h1 h2.le]
  have hAp : ∀ i, 0 < Av i := fun i =>
    lt_of_lt_of_le (mul_pos (mul_pos (pow_pos hr 2) hs2) (by linarith)) (hA i)
  set μ0 := (1 - (2 * a - 1) * τ) / 2 with hμ0
  have hμ0p : 0 < μ0 := by rw [hμ0]; linarith
  set ρ0 := μ0 / (τ + 1) with hρ0def
  have hρ0 : 0 < ρ0 := div_pos hμ0p (by linarith)
  have hρτ : ρ0 * τ ≤ μ0 := by
    rw [hρ0def, div_mul_eq_mul_div, div_le_iff₀ (by linarith), mul_add, mul_one]
    linarith
  set J := Set.Ioo (-ρ0) (2 * a + ρ0) with hJdef
  have hIJ : Set.Icc 0 (2 * a) ⊆ J := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have heJ : ∀ i, ∀ t ∈ J, μ0 ≤ 1 + (t - 1) * θ i := fun i t ht =>
    (one_add_mem_Icc_of_mem_Ioo (hθ i) ha haτ hρ0.le hρτ ht).1
  have heI : ∀ i, ∀ t ∈ Set.Icc 0 (2 * a), 1 - (2 * a - 1) * τ ≤ 1 + (t - 1) * θ i :=
    fun i t ht => one_sub_le_one_add (hθ i) ha ht
  have hden : 0 < 1 - (2 * a - 1) * τ := by linarith
  set v : Fin m → ℝ → ℝ := fun i t => Av i / (1 + (t - 1) * θ i) with hvdef
  set v1 : Fin m → ℝ → ℝ := fun i t => -(Av i * θ i) / (1 + (t - 1) * θ i) ^ 2 with hv1def
  set v2 : Fin m → ℝ → ℝ := fun i t => 2 * Av i * θ i ^ 2 / (1 + (t - 1) * θ i) ^ 3 with hv2def
  have hvJ : ∀ i, ∀ t ∈ J, 0 < v i t := fun i t ht =>
    div_pos (hAp i) (hμ0p.trans_le (heJ i t ht))
  have hpath : ∀ t ∈ J, pathCov r s (U * Matrix.diagonal lam * Uᵀ) t =
      U * Matrix.diagonal (fun i => v i t) * Uᵀ := fun t ht => by
    have hne : ∀ i, 1 + (t - 1) / s ^ 2 * lam i ≠ 0 := fun i => by
      rw [show (t - 1) / s ^ 2 * lam i = (t - 1) * θ i by rw [hθdef]; ring]
      exact (hμ0p.trans_le (heJ i t ht)).ne'
    rw [pathCov_spec hU hU' hne]
    refine congrArg (fun d => U * Matrix.diagonal d * Uᵀ) (funext fun i => ?_)
    rw [hvdef, hAdef, hθdef]
    simp only
    ring
  set wv : (Fin m → ℤ) → Fin m → ℝ := fun y => dualBasis B *ᵥ ofInt y with hwvdef
  set uv : (Fin m → ℤ) → Fin m → ℝ := fun y => Uᵀ *ᵥ wv y with huvdef
  set cs : (Fin m → ℤ) → ℝ := fun y => Real.cos (2 * π * (wv y ⬝ᵥ c)) with hcsdef
  set Q : ℝ → (Fin m → ℤ) → ℝ := fun t y => π * ∑ i, v i t * uv y i ^ 2 with hQdef
  set Q1 : ℝ → (Fin m → ℤ) → ℝ := fun t y => π * ∑ i, v1 i t * uv y i ^ 2 with hQ1def
  set Q2 : ℝ → (Fin m → ℤ) → ℝ := fun t y => π * ∑ i, v2 i t * uv y i ^ 2 with hQ2def
  have hQd : ∀ y, ∀ t ∈ J, HasDerivAt (fun t => Q t y) (Q1 t y) t := fun y t ht => by
    have h := (HasDerivAt.sum (u := Finset.univ) fun i _ =>
      ((hasDerivAt_path (Av i) (θ i) t (hμ0p.trans_le (heJ i t ht)).ne').1.mul_const
        (uv y i ^ 2))).const_mul π
    convert h using 1
    funext t'
    simp only [hQdef, hvdef, Finset.sum_apply]
  have hQ1d : ∀ y, ∀ t ∈ J, HasDerivAt (fun t => Q1 t y) (Q2 t y) t := fun y t ht => by
    have h := (HasDerivAt.sum (u := Finset.univ) fun i _ =>
      ((hasDerivAt_path (Av i) (θ i) t (hμ0p.trans_le (heJ i t ht)).ne').2.mul_const
        (uv y i ^ 2))).const_mul π
    convert h using 1
    funext t'
    simp only [hQ1def, hv1def, Finset.sum_apply]
  have hquad : ∀ t ∈ J, ∀ y, π * quadForm (pathCov r s (U * Matrix.diagonal lam * Uᵀ) t) (wv y) =
      Q t y := fun t ht y => by
    rw [hpath t ht, quadForm_spec]
  have hQnn : ∀ t ∈ J, ∀ y, 0 ≤ Q t y := fun t ht y =>
    mul_nonneg Real.pi_pos.le (Finset.sum_nonneg fun i _ =>
      mul_nonneg (hvJ i t ht).le (sq_nonneg _))
  have hbd : ∀ {K μ : ℝ} (t : ℝ), 0 < μ → (∀ i, μ ≤ 1 + (t - 1) * θ i) → K = τ / μ →
      (∀ y, |Q1 t y| ≤ K * Q t y) ∧ (∀ y, |Q2 t y| ≤ 2 * K ^ 2 * Q t y) := by
    intro K μ t hμ he hK
    subst hK
    have hb := fun i => path_bounds (hAp i).le (hθ i) hμ (he i)
    exact ⟨fun y => abs_pi_sum_le (uv y) fun i => (hb i).1,
      fun y => abs_pi_sum_le (uv y) fun i => (hb i).2⟩
  set Λ := r ^ 2 * s ^ 2 * (1 - τ) / 2 with hΛdef
  have hΛ : 0 < Λ := by
    rw [hΛdef]
    exact div_pos (mul_pos (mul_pos (pow_pos hr 2) hs2) (by linarith)) two_pos
  have he2 : ∀ i, ∀ t ∈ J, 1 + (t - 1) * θ i ≤ 2 := fun i t ht =>
    (one_add_mem_Icc_of_mem_Ioo (hθ i) ha haτ hρ0.le hρτ ht).2
  have hQlow : ∀ t ∈ J, ∀ y, π * Λ * sqNorm (wv y) ≤ Q t y := fun t ht y => by
    change π * Λ * sqNorm (wv y) ≤ π * ∑ i, v i t * (Uᵀ *ᵥ wv y) i ^ 2
    rw [← sqNorm_transpose_mulVec hU' (wv y), sqNorm, dotProduct, mul_assoc, Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) Real.pi_pos.le
    have hvi : Λ ≤ v i t := by
      rw [hvdef, hΛdef, le_div_iff₀ (hμ0p.trans_le (heJ i t ht))]
      have h0 := mul_pos (mul_pos (pow_pos hr 2) hs2) (by linarith : 0 < 1 - τ)
      nlinarith [hA i, he2 i t ht, h0]
    rw [← sq]
    exact mul_le_mul_of_nonneg_right hvi (sq_nonneg _)
  set K0 := τ / μ0 with hK0def
  have hK0 : 0 ≤ K0 := div_nonneg hτ0 hμ0p.le
  have hbJ := fun t (ht : t ∈ J) => hbd t hμ0p (fun i => heJ i t ht) hK0def
  set g : (Fin m → ℤ) → ℝ := fun y => Real.exp (-(π * Λ * sqNorm (wv y) / 2)) with hgdef
  have hgsum : Summable g := by
    have h := summable_exp_sqNorm (det_dualBasis_ne_zero hB) (s := √(Λ / 2))
      (Real.sqrt_pos.2 (by positivity)).ne'
    refine h.congr fun y => ?_
    rw [Real.sq_sqrt (by positivity), hgdef]
    simp only
    ring_nf
    rfl
  have hexp : ∀ t ∈ J, ∀ y, Real.exp (-(Q t y / 2)) ≤ g y := fun t ht y =>
    Real.exp_le_exp.2 (by linarith [hQlow t ht y])
  have hcs : ∀ y, |cs y| ≤ 1 := fun y => Real.abs_cos_le_one _
  have h1J : (1 : ℝ) ∈ J := ⟨by linarith, by linarith⟩
  have hD := hasDerivAt_dualSum isOpen_Ioo isPreconnected_Ioo h1J hK0 hgsum hcs hQd hQ1d hQnn
    (fun t ht => (hbJ t ht).1) (fun t ht => (hbJ t ht).2) hexp
  set F : ℝ → ℝ := fun t => ∑' y, Real.exp (-Q t y) * cs y with hFdef
  set F1 : ℝ → ℝ := fun t => ∑' y, -Q1 t y * Real.exp (-Q t y) * cs y with hF1def
  set F2 : ℝ → ℝ := fun t => ∑' y, (Q1 t y ^ 2 - Q2 t y) * Real.exp (-Q t y) * cs y with hF2def
  have hid : ∀ t ∈ J, Real.exp (logMass B (pathCov r s (U * Matrix.diagonal lam * Uᵀ) t) c) =
      F t := fun t ht => by
    have hPD : (pathCov r s (U * Matrix.diagonal lam * Uᵀ) t).PosDef := by
      rw [hpath t ht]
      exact posDef_spec hU' fun i => hvJ i t ht
    rw [exp_logMass_eq hB hPD c]
    change _ = ∑' y, Real.exp (-Q t y) * cs y
    refine tsum_congr fun y => ?_
    rw [← hquad t ht y, neg_mul]
  have hFpos : ∀ t ∈ J, 0 < F t := fun t ht => by
    rw [← hid t ht]
    exact Real.exp_pos _
  refine ⟨fun t => F1 t / F t, fun t => (F2 t * F t - F1 t * F1 t) / F t ^ 2,
    fun t ht => ⟨?_, ?_, ?_⟩⟩
  · have hJn : J ∈ nhds t := isOpen_Ioo.mem_nhds (hIJ ht)
    have hloc : (fun t => logMass B (pathCov r s (U * Matrix.diagonal lam * Uᵀ) t) c) =ᶠ[nhds t]
        fun t => Real.log (F t) :=
      Filter.eventually_of_mem hJn fun t' ht' => by
        simp only
        rw [← hid t' ht', Real.log_exp]
    exact ((hD t (hIJ ht)).1.log (hFpos t (hIJ ht)).ne').congr_of_eventuallyEq hloc
  · exact (hD t (hIJ ht)).2.div (hD t (hIJ ht)).1 (hFpos t (hIJ ht)).ne'
  have htJ := hIJ ht
  set ξ := √(ϵ / 2) with hξdef
  have hξ0 : 0 < ξ := Real.sqrt_pos.2 (by positivity)
  have hξ1 : ξ < 1 := by
    rw [hξdef, Real.sqrt_lt' one_pos]
    linarith
  set δ := τ / (1 - (2 * a - 1) * τ) with hδdef
  have hδ0 : 0 ≤ δ := div_nonneg hτ0 hden.le
  have hbI := hbd t hden (fun i => heI i t ht) hδdef
  have hgs := geSmoothing_pathCov hB hSe hr hs hτ ha haτ hϵ₀ hϵ hη ht
  have hPD : ((1 - ξ) • pathCov r s (U * Matrix.diagonal lam * Uᵀ) t).PosDef :=
    (posDef_pathCov hSe hr hs hτ ha haτ ht).smul (by linarith)
  have hMM := sqrt_mul_transpose_sqrt hPD.posSemidef
  have hMd := det_ne_zero_of_mul_transpose hMM hPD.det_pos.ne'
  have hrs := (geSmoothing_iff hB hMd hϵ₀).1 hgs
  have hHeq : ∀ y, rho 1 0 (((CFC.sqrt ((1 - ξ) • pathCov r s (U * Matrix.diagonal lam * Uᵀ) t))ᵀ *
      dualBasis B) *ᵥ ofInt y) = Real.exp (-((1 - ξ) * Q t y)) := fun y => by
    rw [rho, inv_one, Matrix.one_mulVec, sub_zero, ← Matrix.mulVec_mulVec,
      ← quadForm_transpose_mul_self, Matrix.transpose_transpose, hMM, quadForm_smul,
      ← hquad t htJ y]
    ring_nf
    rfl
  have hsumH : Summable fun y => Real.exp (-((1 - ξ) * Q t y)) :=
    (summable_rho (B := (CFC.sqrt ((1 - ξ) • pathCov r s (U * Matrix.diagonal lam * Uᵀ) t))ᵀ *
      dualBasis B) (by
        rw [Matrix.det_mul, Matrix.det_transpose]
        exact mul_ne_zero hMd (det_dualBasis_ne_zero hB)) (M := 1) (by simp) 0).congr hHeq
  have hHle : ∑' y, Real.exp (-((1 - ξ) * Q t y)) ≤ 1 + ϵ := by
    rw [← tsum_congr hHeq]
    exact hrs
  have hwv0 : wv 0 = 0 := by rw [hwvdef]; simp [ofInt_zero]
  have huv0 : uv 0 = 0 := by rw [huvdef]; simp only [hwv0, Matrix.mulVec_zero]
  have hQ0 : Q t 0 = 0 := by simp [hQdef, huv0]
  have hQ10 : Q1 t 0 = 0 := by simp [hQ1def, huv0]
  have hQ20 : Q2 t 0 = 0 := by simp [hQ2def, huv0]
  have hcs0 : cs 0 = 1 := by simp [hcsdef, hwv0]
  obtain ⟨-, hb⟩ := dualSum_bound (0 : Fin m → ℤ) (Q := Q t) (Q1 := Q1 t) (Q2 := Q2 t) (cs := cs)
    hδ0 hϵ₀ hϵ hcs hcs0 (hQnn t htJ) hQ0 hQ10 hQ20 hbI.1 hbI.2 hsumH hHle rfl rfl rfl
  have e1 : 5 * τ ^ 2 / (1 - (2 * a - 1) * τ) ^ 2 = 5 * δ ^ 2 := by
    rw [hδdef, div_pow]
    ring
  rw [e1]
  exact hb

/-- **The scale change** [ZKLY26, p. 7-8, l. 239-258, first line of l. 258]:
`log R_{2a}(D_{L(B),M,c} ‖ D_{L(B),rs,c}) ≤ a‖Σ‖_F²/(2s⁴(1 + τ)(1 − (2a − 1)τ))
+ 5aτ²/(1 − (2a − 1)τ)²` for `MMᵗ = r²(s²I − Σ)`, `|xᵗΣx| ≤ τs²‖x‖²`, `(2a − 1)τ < 1`,
`0 < ϵ ≤ 1/2` and `rs √((1 − √(ϵ/2))(1 − τ)/(1 + (2a − 1)τ)) ≥ η_ϵ(L(B))`. -/
theorem renyiDiv_gaussianMeasure_scale_le {B Se M : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0)
    (hSe : Se.IsSymm) {r s τ a ϵ : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hτ : ∀ x, |x ⬝ᵥ (Se *ᵥ x)| ≤ τ * s ^ 2 * sqNorm x) (ha : 1 < a)
    (haτ : (2 * a - 1) * τ < 1) (hϵ₀ : 0 < ϵ) (hϵ : ϵ ≤ 1 / 2)
    (hη : smoothingParam ϵ B ≤
      r * s * √((1 - √(ϵ / 2)) * (1 - τ) / (1 + (2 * a - 1) * τ)))
    (hM : M * Mᵀ = r ^ 2 • (s ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) - Se)) (c : Fin m → ℝ) :
    renyiDiv (2 * a) (gaussianMeasure B M c)
        (gaussianMeasure B ((r * s) • (1 : Matrix (Fin m) (Fin m) ℝ)) c) ≤
      ENNReal.ofReal (Real.exp
        (a * (∑ i, ∑ j, Se i j ^ 2) / (2 * s ^ 4 * (1 + τ) * (1 - (2 * a - 1) * τ)) +
          5 * a * τ ^ 2 / (1 - (2 * a - 1) * τ) ^ 2)) := by
  rw [renyiDiv_gaussianMeasure_eq hB hSe hr hs hτ ha haτ (by rw [hM, pathCov_one]) c]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have hdet := detTerm_le hSe hr hs hτ ha haτ
  obtain ⟨φ', φ'', hφ⟩ := exists_deriv2_logMass_le hB hSe hr hs hτ ha haτ hϵ₀ hϵ hη c
  set K := 5 * τ ^ 2 / (1 - (2 * a - 1) * τ) ^ 2 with hKdef
  have hs1 : ∀ y ∈ Set.uIcc (1 : ℝ) (1 + (2 * a - 1)), y ∈ Set.Icc 0 (2 * a) := fun y hy => by
    rw [Set.uIcc_of_le (by linarith)] at hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hs2 : ∀ y ∈ Set.uIcc (1 : ℝ) (1 + -1), y ∈ Set.Icc 0 (2 * a) := fun y hy => by
    rw [Set.uIcc_of_ge (by linarith)] at hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have t1 := FalconPrecision.Taylor2.sub_le_of_deriv2_le_on
    (g := fun t => logMass B (pathCov r s Se t) c) (M := K) (x := 1) (h := 2 * a - 1)
    (fun y hy => (hφ y (hs1 y hy)).1) (fun y hy => (hφ y (hs1 y hy)).2.1)
    (fun y hy => (abs_le.1 (hφ y (hs1 y hy)).2.2).2)
  have t2 := FalconPrecision.Taylor2.sub_le_of_deriv2_le_on
    (g := fun t => logMass B (pathCov r s Se t) c) (M := K) (x := 1) (h := -1)
    (fun y hy => (hφ y (hs2 y hy)).1) (fun y hy => (hφ y (hs2 y hy)).2.1)
    (fun y hy => (abs_le.1 (hφ y (hs2 y hy)).2.2).2)
  simp only [show (1 : ℝ) + (2 * a - 1) = 2 * a by ring, show (1 : ℝ) + -1 = 0 by ring] at t1 t2
  have hb : (0 : ℝ) < 2 * a - 1 := by linarith
  have t2' := mul_le_mul_of_nonneg_left t2 hb.le
  have hsd : (logMass B (pathCov r s Se (2 * a)) c - 2 * a * logMass B (pathCov r s Se 1) c +
      (2 * a - 1) * logMass B (pathCov r s Se 0) c) / (2 * a - 1) ≤ a * K := by
    rw [div_le_iff₀ hb]
    nlinarith [t1, t2']
  have hK : 5 * a * τ ^ 2 / (1 - (2 * a - 1) * τ) ^ 2 = a * K := by
    rw [hKdef]
    ring
  rw [hK]
  linarith

end Mitaka.LatticeGaussian

namespace Mitaka.Key

variable {n : ℕ}

/-- **The scale change for the Mitaka key** [ZKLY26, p. 8, l. 258, first line]:
`log R_{2a}(𝒬_e‖𝒬₀) ≤ a‖Σ_e‖_F²/(2s⁴(1 + τ̄)(1 − (2a − 1)τ̄)) + 5aτ̄²/(1 − (2a − 1)τ̄)²`, for
`n = 2^ℓ`, `0 < q`, condition 1, NTRU, condition 2, condition 4, `0 < ϵ ≤ 1/2` and `a > 1`.
Assumed, not proved: `Key.GSCoeff u` and the key-expansion facts `Key.UClose`,
`Key.CholeskyRoot`, `Key.AClose` (`hu`, `hr`, `hC`, `hAc`; Lemma 3). -/
theorem renyiDiv_gaussianQe_le {ℓ : ℕ} (hn : n = 2 ^ ℓ) (P : Params) (K : Key n) (u : Fin n → ℝ)
    (A : Fin 2 → Fin 2 → Fin n → ℝ) (hq : 0 < P.q) (hK : K.Annular P) (hN : K.NTRU P)
    (hu : K.GSCoeff u) (hr : K.UClose P u) (hC : K.CholeskyRoot P A) (hAc : K.AClose P A)
    (hs : beta P n < P.s) {ϵ a : ℝ} (hϵ₀ : 0 < ϵ) (hϵ : ϵ ≤ 1 / 2) (ha : 1 < a)
    (h4a : (2 * a - 1) * tauBar P n < 1)
    (h4η : smoothingParam ϵ K.basisMat ≤
      P.r * P.s * √((1 - √(ϵ / 2)) * (1 - tauBar P n) / (1 + (2 * a - 1) * tauBar P n)))
    (c : Fin 2 → Fin n → ℝ) :
    renyiDiv (2 * a) (K.gaussianQe P c) (K.gaussianQ0 P c) ≤
      ENNReal.ofReal (Real.exp
        (a * KMat.normF (K.sigmaE P) ^ 2 /
            (2 * P.s ^ 4 * (1 + tauBar P n) * (1 - (2 * a - 1) * tauBar P n)) +
          5 * a * tauBar P n ^ 2 / (1 - (2 * a - 1) * tauBar P n) ^ 2)) := by
  have hn0 : 0 < n := by
    rw [hn]
    positivity
  have hs0 : 0 < P.s := (beta_pos P n hK.one_le_alpha hq).trans hs
  have hB := det_basisMat_ne_zero P K hq hN
  have hτ : ∀ x, |x ⬝ᵥ (K.sigmaEMat P *ᵥ x)| ≤ tauBar P n * P.s ^ 2 * sqNorm x := fun x =>
    (abs_dotProduct_sigmaEMat_le hn0 P K x).trans (mul_le_mul_of_nonneg_right
      (norm2_sigmaE_le hn P K u A hq hK hN hu hr hC hAc hs) (sqNorm_nonneg x))
  have hSym : (K.sigmaEMat P).IsSymm := by
    rw [Matrix.IsSymm, sigmaEMat]
    simp [Matrix.transpose_sub, Matrix.transpose_mul]
  have hr0 : 0 < P.r := by
    have h1 := (smoothingParam_pos (by omega) hB hϵ₀).trans_le h4η
    have h2 : 0 < P.r * P.s := pos_of_mul_pos_left h1 (Real.sqrt_nonneg _)
    exact pos_of_mul_pos_left h2 hs0.le
  have hPD := posDef_sub_sigmaEMat P K hq hN
  have hMM : (P.r • CFC.sqrt (P.s ^ 2 • (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ) -
      K.sigmaEMat P)) * (P.r • CFC.sqrt (P.s ^ 2 • (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ) -
        K.sigmaEMat P))ᵀ = P.r ^ 2 • (P.s ^ 2 • 1 - K.sigmaEMat P) := by
    rw [smul_mul_transpose_smul, sqrt_mul_transpose_sqrt hPD.posSemidef]
  have h := renyiDiv_gaussianMeasure_scale_le hB hSym hr0 hs0 hτ ha h4a hϵ₀ hϵ h4η hMM
    (Fin.append (c 0) (c 1))
  rw [sum_sq_sigmaEMat hn0] at h
  have hM0 := isProbabilityMeasure_gaussianMeasure hB (det_ne_zero_of_mul_transpose hMM (by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hr0.ne')) hPD.det_pos.ne'))
    (Fin.append (c 0) (c 1))
  have hM1 := isProbabilityMeasure_gaussianMeasure hB
    (M := (P.r * P.s) • (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ)) (by
      rw [Matrix.det_smul, Matrix.det_one, mul_one]
      exact pow_ne_zero _ (mul_pos hr0 hs0).ne') (Fin.append (c 0) (c 1))
  exact (renyiDiv_map_le (2 * a) (by linarith) _ _ (measurable_of_countable _)).trans h

/-- **The scale change with Lemma 3 substituted** [ZKLY26, p. 8, l. 258, second line]:
`log R_{2a}(𝒬_e‖𝒬₀) ≤ 3an² sin²(π/(2n)) τ̄²/((3 + √5)(1 + τ̄)(1 − (2a − 1)τ̄))
+ 5aτ̄²/(1 − (2a − 1)τ̄)²`, under the hypotheses of `Key.renyiDiv_gaussianQe_le`. Assumed, not
proved: `Key.GSCoeff u` and the key-expansion facts `Key.UClose`, `Key.CholeskyRoot`,
`Key.AClose` (`hu`, `hr`, `hC`, `hAc`; Lemma 3). -/
theorem renyiDiv_gaussianQe_le_tauBar {ℓ : ℕ} (hn : n = 2 ^ ℓ) (P : Params) (K : Key n)
    (u : Fin n → ℝ) (A : Fin 2 → Fin 2 → Fin n → ℝ) (hq : 0 < P.q) (hK : K.Annular P)
    (hN : K.NTRU P) (hu : K.GSCoeff u) (hr : K.UClose P u) (hC : K.CholeskyRoot P A)
    (hAc : K.AClose P A) (hs : beta P n < P.s) {ϵ a : ℝ} (hϵ₀ : 0 < ϵ) (hϵ : ϵ ≤ 1 / 2)
    (ha : 1 < a) (h4a : (2 * a - 1) * tauBar P n < 1)
    (h4η : smoothingParam ϵ K.basisMat ≤
      P.r * P.s * √((1 - √(ϵ / 2)) * (1 - tauBar P n) / (1 + (2 * a - 1) * tauBar P n)))
    (c : Fin 2 → Fin n → ℝ) :
    renyiDiv (2 * a) (K.gaussianQe P c) (K.gaussianQ0 P c) ≤
      ENNReal.ofReal (Real.exp
        (3 * a * n ^ 2 * Real.sin (π / (2 * n)) ^ 2 * tauBar P n ^ 2 /
            ((3 + √5) * (1 + tauBar P n) * (1 - (2 * a - 1) * tauBar P n)) +
          5 * a * tauBar P n ^ 2 / (1 - (2 * a - 1) * tauBar P n) ^ 2)) := by
  refine (renyiDiv_gaussianQe_le hn P K u A hq hK hN hu hr hC hAc hs hϵ₀ hϵ ha h4a h4η c).trans
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (add_le_add ?_ le_rfl)))
  have hs0 : 0 < P.s := (beta_pos P n hK.one_le_alpha hq).trans hs
  have hτ0 := tauBar_nonneg P n hs0.le
  have hD : 0 < (1 + tauBar P n) * (1 - (2 * a - 1) * tauBar P n) :=
    mul_pos (by linarith) (by linarith)
  have hF := normF_sigmaE_le hn P K u A hq hK hN hu hr hC hAc hs
  have hF2 := pow_le_pow_left₀ (KMat.normF_nonneg _) hF 2
  have h5 : (1 + √5) ^ 2 = 2 * (3 + √5) := by
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
    nlinarith [this]
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hp5 : 0 < 3 + √5 := by positivity
  calc a * KMat.normF (K.sigmaE P) ^ 2 /
        (2 * P.s ^ 4 * (1 + tauBar P n) * (1 - (2 * a - 1) * tauBar P n))
      ≤ a * (2 * √3 * n * Real.sin (π / (2 * n)) / (1 + √5) * tauBar P n * P.s ^ 2) ^ 2 /
          (2 * P.s ^ 4 * (1 + tauBar P n) * (1 - (2 * a - 1) * tauBar P n)) := by
        gcongr
    _ = 3 * a * n ^ 2 * Real.sin (π / (2 * n)) ^ 2 * tauBar P n ^ 2 /
          ((3 + √5) * (1 + tauBar P n) * (1 - (2 * a - 1) * tauBar P n)) := by
        have hs4 : P.s ≠ 0 := hs0.ne'
        have hD1 : 1 + tauBar P n ≠ 0 := by linarith
        have hD2 : 1 - (2 * a - 1) * tauBar P n ≠ 0 := by linarith
        have h1 : (1 + √5) ≠ 0 := by positivity
        have hp5' := hp5.ne'
        have k1 : (2 * √3 * n * Real.sin (π / (2 * n)) / (1 + √5) * tauBar P n * P.s ^ 2) ^ 2 =
            (2 * √3 * n * Real.sin (π / (2 * n)) * tauBar P n * P.s ^ 2) ^ 2 / (1 + √5) ^ 2 := by
          rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_pow]
        have k2 : (2 * √3 * n * Real.sin (π / (2 * n)) * tauBar P n * P.s ^ 2) ^ 2 =
            12 * n ^ 2 * Real.sin (π / (2 * n)) ^ 2 * tauBar P n ^ 2 * P.s ^ 4 := by
          ring_nf
          rw [h3]
          ring
        rw [k1, k2, h5]
        field_simp
        ring

end Mitaka.Key
