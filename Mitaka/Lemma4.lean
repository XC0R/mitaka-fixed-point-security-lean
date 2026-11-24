/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import Mitaka.BoundedRatio
public import Mitaka.KeyMatrix

/-! # Lemma 4 of [ZKLY26]: the output law of Algorithm 3

[ZKLY26] (ePrint 2026/2521), Lemma 4 (p. 7, l. 237; proof App. A.3, p. 19, l. 591-612): "Under the
conditions in Theorem 1, the output distribution `𝒫` has support `L(B)` and can be written as
`𝒫(z) = 𝒬_e(z) a_z/E_{𝒬_e}[a_z]` with `𝒬_e = D_{L(B), r√(s²I₂ₙ − Σ_e), c}` and
`a_z ∈ [κ⁻¹, κ²]`. Consequently, for every `v > 1`, `log R_v(𝒫‖𝒬_e) ≤ (9v/8)(log κ)²`", with
`κ = (1 + ϵ)/(1 − ϵ)` (p. 6, l. 221).

`𝒫` is the law of `Mitaka.sample` with perfect integer samplers (a world `implE` answering with
`answer P id`, p. 6, l. 214-215), on its output type `Fin 2 → Fin n → ℤ`; `𝒬_e` is
`Key.gaussianQe`. The proof:
* `evalDist_sampleCoords_singleton`: the law of the coordinates as a sum over the perturbation
  `x ∈ ℤ^{2n}` of products of integer Gaussians (p. 19, l. 595-596);
* `tsum_rho_mul_rho_eq`: completing the square in `x` (l. 598-601), with
  `C = (I + Âᵗ(B̂B̂ᵗ)⁻¹Â)⁻¹` (`convCov`) and `m_y = −L C Âᵗ(B̂B̂ᵗ)⁻¹ y` (`convCentre`); here
  `B̂B̂ᵗ + ÂÂᵗ = s²I − Σ_e`;
* `Key.geSmoothing_convCov`: `L r √C ≥ η_ϵ(ℤ^{2n})` from condition 3 and the sampling-scale
  estimate (l. 602-603; `Key.one_add_sq_norm2_le`);
* Lemma 1 (`rhoSum_one_mem_Icc`) for the two online normalisers (`r ≥ η_ϵ(ℤⁿ)`, l. 597) and for
  `ρ_{Lr√C, m}(ℤ^{2n})` (l. 604), so `a_z ∈ [κ⁻¹, κ²]` (l. 606);
* `BoundedRatio.renyiDiv_withDensity_le` (Popoviciu's step, l. 610-612).

Hypotheses: those of Lemma 3 (`n = 2^ℓ`, `0 < q`, condition 1, NTRU, the Gram–Schmidt coefficient
`u`, `‖u − û‖∞ ≤ 1/(2p_u)`, a lower-triangular root `A` of `Σ_p` with `|A − Â| ≤ 1/(2p_A)`
coefficientwise), condition 2 (`β(p_u) < s`), condition 3, and `0 < ϵ < 1`. Theorem 1's
`ϵ ≤ 1/2`, `a > 1` and condition 4 are not used. -/

@[expose] public section

open Real MeasureTheory InformationTheory OracleSpec OracleComp LatticeCrypto
  Mitaka.LatticeGaussian
open scoped Matrix MatrixOrder ENNReal

namespace Mitaka

/-- `κ = (1 + ϵ)/(1 − ϵ)` [ZKLY26, p. 6, l. 221]. -/
noncomputable def kappa (ϵ : ℝ) : ℝ := (1 + ϵ) / (1 - ϵ)

namespace LatticeGaussian

variable {m : ℕ}

/-- `C = (I + Âᵗ(B̂B̂ᵗ)⁻¹Â)⁻¹` [ZKLY26, p. 19, l. 599]. -/
noncomputable def convCov (Bh Ah : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  (1 + Ahᵀ * (Bh * Bhᵀ)⁻¹ * Ah)⁻¹

/-- `m_y = −L C Âᵗ(B̂B̂ᵗ)⁻¹ y` [ZKLY26, p. 19, l. 599], at `y = z − c`. -/
noncomputable def convCentre (Bh Ah : Matrix (Fin m) (Fin m) ℝ) (L : ℝ) (y : Fin m → ℝ) :
    Fin m → ℝ :=
  -(L • ((convCov Bh Ah * Ahᵀ * (Bh * Bhᵀ)⁻¹) *ᵥ y))

/-- `√S (√S)ᵗ = S` for positive semidefinite `S`. -/
theorem sqrt_mul_transpose_sqrt {S : Matrix (Fin m) (Fin m) ℝ} (hS : S.PosSemidef) :
    CFC.sqrt S * (CFC.sqrt S)ᵀ = S := by
  have h1 : (CFC.sqrt S)ᵀ = CFC.sqrt S := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial, ← Matrix.star_eq_conjTranspose]
    exact (CFC.sqrt_nonneg S).isSelfAdjoint.star_eq
  rw [h1, CFC.sqrt_mul_sqrt_self S hS.nonneg]

/-- `(aM)(aM)ᵗ = a² MMᵗ`. -/
theorem smul_mul_transpose_smul (a : ℝ) (M : Matrix (Fin m) (Fin m) ℝ) :
    (a • M) * (a • M)ᵀ = a ^ 2 • (M * Mᵀ) := by
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, sq]

/-- `ρ_{M,c}(x) = exp(−π (x − c)ᵗ V⁻¹ (x − c))` when `MMᵗ = V`. -/
theorem rho_eq_of_mul_transpose {M V : Matrix (Fin m) (Fin m) ℝ} (h : M * Mᵀ = V)
    (c x : Fin m → ℝ) : rho M c x = Real.exp (-π * quadForm V⁻¹ (x - c)) := by
  rw [rho_eq_exp_quadForm, h]

/-- An invertible `V = MMᵗ` has an invertible factor `M`. -/
theorem det_ne_zero_of_mul_transpose {M V : Matrix (Fin m) (Fin m) ℝ} (h : M * Mᵀ = V)
    (hV : V.det ≠ 0) : M.det ≠ 0 := fun hM => hV (by
  rw [← h, Matrix.det_mul, Matrix.det_transpose, hM, zero_mul])

/-- `(a A)⁻¹ = a⁻¹ A⁻¹`. -/
theorem inv_smul_of_ne {a : ℝ} (ha : a ≠ 0) {A : Matrix (Fin m) (Fin m) ℝ} (h : IsUnit A.det) :
    (a • A)⁻¹ = a⁻¹ • A⁻¹ := by
  have h' := Matrix.inv_smul' (A := A) (Units.mk0 a ha) h
  simp only [Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0] at h'
  exact h'

/-- `quadForm (aP) v = a · quadForm P v`. -/
theorem quadForm_smul (a : ℝ) (P : Matrix (Fin m) (Fin m) ℝ) (v : Fin m → ℝ) :
    quadForm (a • P) v = a * quadForm P v := by
  simp [quadForm, Matrix.smul_mulVec]

/-- `⟨u, Aᵗw⟩ = ⟨Au, w⟩` (Mathlib's `Matrix.dotProduct_transpose_mulVec`, other side). -/
theorem dotProduct_transpose_mulVec_left (A : Matrix (Fin m) (Fin m) ℝ) (u w : Fin m → ℝ) :
    u ⬝ᵥ (Aᵀ *ᵥ w) = (A *ᵥ u) ⬝ᵥ w := by
  rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

/-- **Completing the square** [ZKLY26, p. 19, l. 600-601]: for invertible `B̂`,
`Σ_{x∈ℤ^m} ρ_{Lr}(x) ρ_{rB̂}(y + Âx/L) = ρ_{r√(B̂B̂ᵗ + ÂÂᵗ)}(y) ρ_{Lr√C, m_y}(ℤ^m)`. -/
theorem tsum_rho_mul_rho_eq {Bh Ah : Matrix (Fin m) (Fin m) ℝ} (hB : Bh.det ≠ 0) {L r : ℝ}
    (hL : 0 < L) (hr : 0 < r) (y : Fin m → ℝ) :
    ∑' x : Fin m → ℤ, rho ((L * r) • (1 : Matrix (Fin m) (Fin m) ℝ)) 0 (ofInt x) *
        rho (r • Bh) 0 (y + L⁻¹ • (Ah *ᵥ ofInt x)) =
      rho (r • CFC.sqrt (Bh * Bhᵀ + Ah * Ahᵀ)) 0 y *
        rhoSum 1 ((L * r) • CFC.sqrt (convCov Bh Ah)) (convCentre Bh Ah L y) := by
  set W := (Bh * Bhᵀ)⁻¹ with hWdef
  set D : Matrix (Fin m) (Fin m) ℝ := 1 + Ahᵀ * W * Ah with hDdef
  set C := convCov Bh Ah
  set S := Bh * Bhᵀ + Ah * Ahᵀ
  have hBu : IsUnit (Bh * Bhᵀ).det := by
    rw [Matrix.det_mul, Matrix.det_transpose]
    exact isUnit_iff_ne_zero.2 (mul_ne_zero hB hB)
  have hBPD : (Bh * Bhᵀ).PosDef := by
    have h := Matrix.PosDef.mul_conjTranspose_self Bh (Matrix.vecMul_injective_iff_isUnit.2
      ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hB)))
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hWs : Wᵀ = W := by
    rw [hWdef, Matrix.transpose_nonsing_inv, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hDPD : D.PosDef := Matrix.PosDef.one.add_posSemidef (by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hBPD.inv.posSemidef.conjTranspose_mul_mul_same Ah)
  have hDu : IsUnit D.det := isUnit_iff_ne_zero.2 hDPD.det_pos.ne'
  have hDC : D * C = 1 := Matrix.mul_nonsing_inv _ hDu
  have hDs : Dᵀ = D := by
    rw [hDdef, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul,
      Matrix.transpose_mul, hWs, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hCPD : C.PosDef := hDPD.inv
  have hSPD : S.PosDef := hBPD.add_posSemidef (by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose Ah)
  have hSinv : S⁻¹ = W - W * Ah * C * Ahᵀ * W := by
    have h := Matrix.add_mul_mul_inv_eq_sub (Bh * Bhᵀ) Ah 1 Ahᵀ
      ((Matrix.isUnit_iff_isUnit_det _).2 hBu) isUnit_one
      (by rw [inv_one]; exact (Matrix.isUnit_iff_isUnit_det _).2 hDu)
    rw [Matrix.mul_one, inv_one] at h
    exact h
  have hr0 : r ≠ 0 := hr.ne'
  have hLr : L * r ≠ 0 := (mul_pos hL hr).ne'
  have hCinv : C⁻¹ = D := Matrix.nonsing_inv_nonsing_inv _ hDu
  have hm : convCentre Bh Ah L y = -(L • (C *ᵥ (Ahᵀ *ᵥ (W *ᵥ y)))) := by
    rw [convCentre, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [rhoSum, ← tsum_mul_left]
  refine tsum_congr fun x => ?_
  rw [rho_eq_of_mul_transpose (smul_mul_transpose_smul _ _),
    rho_eq_of_mul_transpose (smul_mul_transpose_smul _ _),
    rho_eq_of_mul_transpose (smul_mul_transpose_smul _ _),
    rho_eq_of_mul_transpose (smul_mul_transpose_smul _ _), ← Real.exp_add, ← Real.exp_add,
    sqrt_mul_transpose_sqrt hSPD.posSemidef, sqrt_mul_transpose_sqrt hCPD.posSemidef,
    Matrix.transpose_one, Matrix.mul_one, inv_smul_of_ne (pow_ne_zero 2 hLr) (by simp),
    inv_smul_of_ne (pow_ne_zero 2 hr0) hBu,
    inv_smul_of_ne (pow_ne_zero 2 hr0) (isUnit_iff_ne_zero.2 hSPD.det_pos.ne'),
    inv_smul_of_ne (pow_ne_zero 2 hLr) (isUnit_iff_ne_zero.2 hCPD.det_pos.ne'),
    hCinv, hSinv, quadForm_smul,
    quadForm_smul, quadForm_smul, quadForm_smul, Matrix.one_mulVec, hm]
  congr 1
  set X := ofInt x
  set a := Ah *ᵥ X
  set wy := W *ᵥ y
  set u := Ahᵀ *ᵥ wy
  set cu := C *ᵥ u
  have F1 : quadForm W (y + L⁻¹ • a - 0) =
      y ⬝ᵥ wy + 2 * L⁻¹ * (a ⬝ᵥ wy) + L⁻¹ ^ 2 * (a ⬝ᵥ (W *ᵥ a)) := by
    have hs := Matrix.IsSymm.dotProduct_mulVec_comm (x := y) (y := a) hWs
    simp only [quadForm, sub_zero, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
      add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul, hs]
    ring
  have F3 : D *ᵥ cu = u := by rw [Matrix.mulVec_mulVec, hDC, Matrix.one_mulVec]
  have F4 : X ⬝ᵥ (D *ᵥ X) = X ⬝ᵥ X + a ⬝ᵥ (W *ᵥ a) := by
    rw [hDdef, Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, dotProduct_transpose_mulVec_left]
  have F5 : X ⬝ᵥ u = a ⬝ᵥ wy := dotProduct_transpose_mulVec_left _ _ _
  have F2 : quadForm D (X - -(L • cu)) =
      X ⬝ᵥ X + a ⬝ᵥ (W *ᵥ a) + 2 * L * (a ⬝ᵥ wy) + L ^ 2 * (cu ⬝ᵥ u) := by
    have hs := Matrix.IsSymm.dotProduct_mulVec_comm (x := cu) (y := X) hDs
    simp only [quadForm, sub_neg_eq_add, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
      add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul, F3, hs, F4, F5]
    ring
  have F6 : quadForm (W - W * Ah * C * Ahᵀ * W) (y - 0) = y ⬝ᵥ wy - cu ⬝ᵥ u := by
    have h1 : (W * Ah * C * Ahᵀ * W) *ᵥ y = W *ᵥ (Ah *ᵥ cu) := by
      simp only [← Matrix.mulVec_mulVec, cu, u, wy]
    have h2 : y ⬝ᵥ (W *ᵥ (Ah *ᵥ cu)) = cu ⬝ᵥ u := by
      rw [Matrix.IsSymm.dotProduct_mulVec_comm (x := y) hWs, ← dotProduct_transpose_mulVec_left]
    rw [quadForm, sub_zero, Matrix.sub_mulVec, dotProduct_sub, h1, h2]
  have F0 : quadForm (1 : Matrix (Fin m) (Fin m) ℝ)⁻¹ (X - 0) = X ⬝ᵥ X := by simp [quadForm]
  rw [F0, F1, F2, F6]
  field_simp
  ring

/-- `‖a − c w‖² = ‖a‖² − 2c⟨a, w⟩ + c²‖w‖²`. -/
theorem sqNorm_sub_smul (a w : Fin m → ℝ) (c : ℝ) :
    sqNorm (a - c • w) = sqNorm a - 2 * c * (a ⬝ᵥ w) + c ^ 2 * sqNorm w := by
  simp only [sqNorm, sub_dotProduct, dotProduct_sub, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, dotProduct_comm w a]
  ring

/-- A bound `‖Xz‖² ≤ μ‖z‖²` transfers to `Xᵗ`. -/
theorem sqNorm_transpose_mulVec_le {X : Matrix (Fin m) (Fin m) ℝ} {μ : ℝ} (hμ : 0 ≤ μ)
    (hX : ∀ z, sqNorm (X *ᵥ z) ≤ μ * sqNorm z) (w : Fin m → ℝ) :
    sqNorm (Xᵀ *ᵥ w) ≤ μ * sqNorm w := by
  set a := X *ᵥ (Xᵀ *ᵥ w)
  have hT : sqNorm (Xᵀ *ᵥ w) = a ⬝ᵥ w := dotProduct_transpose_mulVec_left X _ _
  have ha := hX (Xᵀ *ᵥ w)
  have h0 := sqNorm_nonneg (a - μ • w)
  rw [sqNorm_sub_smul] at h0
  rcases hμ.eq_or_lt with h | h
  · subst h
    have ha0 : a = 0 := by
      by_contra hne
      have := sqNorm_pos hne
      linarith
    rw [hT, ha0, zero_dotProduct, zero_mul]
  · have hw := sqNorm_nonneg w
    have h1 : μ * sqNorm (Xᵀ *ᵥ w) ≤ μ * (μ * sqNorm w) := by nlinarith [ha, h0, hT]
    exact le_of_mul_le_mul_left h1 h

/-- `Âᵗ(B̂B̂ᵗ)⁻¹Â = XᵗX` with `X = B̂⁻¹Â`. -/
theorem transpose_mul_inv_mul (Bh Ah : Matrix (Fin m) (Fin m) ℝ) :
    Ahᵀ * (Bh * Bhᵀ)⁻¹ * Ah = (Bh⁻¹ * Ah)ᵀ * (Bh⁻¹ * Ah) := by
  rw [Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv, Matrix.transpose_mul, Matrix.mul_assoc,
    Matrix.mul_assoc, Matrix.mul_assoc]

/-- `C ⪰ (1 + μ)⁻¹ I` when `‖B̂⁻¹Âz‖² ≤ μ‖z‖²` [ZKLY26, p. 19, l. 602]. -/
theorem posSemidef_convCov_sub {Bh Ah : Matrix (Fin m) (Fin m) ℝ} {μ : ℝ} (hμ : 0 ≤ μ)
    (hX : ∀ z, sqNorm ((Bh⁻¹ * Ah) *ᵥ z) ≤ μ * sqNorm z) :
    (convCov Bh Ah - (1 + μ)⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef := by
  set X := Bh⁻¹ * Ah
  set D : Matrix (Fin m) (Fin m) ℝ := 1 + Xᵀ * X with hDdef
  have hDPD : D.PosDef := Matrix.PosDef.one.add_posSemidef (by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self X)
  have hDu : IsUnit D.det := isUnit_iff_ne_zero.2 hDPD.det_pos.ne'
  have hC : convCov Bh Ah = D⁻¹ := by rw [convCov, transpose_mul_inv_mul]
  have hDs : Dᵀ = D := by
    rw [hDdef, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul,
      Matrix.transpose_transpose]
  rw [hC, Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun y => ?_⟩
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_sub,
      Matrix.transpose_smul, Matrix.transpose_one, Matrix.transpose_nonsing_inv, hDs]
  set z := D⁻¹ *ᵥ y
  have hy : y = D *ᵥ z := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hDu, Matrix.one_mulVec]
  have hg := hX z
  have hh := sqNorm_transpose_mulVec_le hμ hX (X *ᵥ z)
  have hXX : z ⬝ᵥ (Xᵀ *ᵥ (X *ᵥ z)) = sqNorm (X *ᵥ z) := dotProduct_transpose_mulVec_left X _ _
  have hDz : D *ᵥ z = z + Xᵀ *ᵥ (X *ᵥ z) := by
    rw [hDdef, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
  have e1 : star y ⬝ᵥ ((D⁻¹ - (1 + μ)⁻¹ • 1) *ᵥ y) =
      (sqNorm z + sqNorm (X *ᵥ z)) - (1 + μ)⁻¹ *
        (sqNorm z + 2 * sqNorm (X *ᵥ z) + sqNorm (Xᵀ *ᵥ (X *ᵥ z))) := by
    have h1 : y ⬝ᵥ z = sqNorm z + sqNorm (X *ᵥ z) := by
      rw [hy, hDz, add_dotProduct, dotProduct_comm (Xᵀ *ᵥ (X *ᵥ z)) z, hXX]
      rfl
    have h2 : y ⬝ᵥ y = sqNorm z + 2 * sqNorm (X *ᵥ z) + sqNorm (Xᵀ *ᵥ (X *ᵥ z)) := by
      rw [hy, hDz, add_dotProduct, dotProduct_add, dotProduct_add,
        dotProduct_comm (Xᵀ *ᵥ (X *ᵥ z)) z, hXX]
      simp only [sqNorm]
      ring
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul, star_trivial, ← h1, ← h2]
  rw [e1, sub_nonneg, inv_mul_le_iff₀ (by linarith)]
  nlinarith [hg, hh, sqNorm_nonneg (X *ᵥ z)]

/-- `C = (I + Âᵗ(B̂B̂ᵗ)⁻¹Â)⁻¹` is positive definite. -/
theorem posDef_convCov (Bh Ah : Matrix (Fin m) (Fin m) ℝ) : (convCov Bh Ah).PosDef := by
  have hD : (1 + (Bh⁻¹ * Ah)ᵀ * (Bh⁻¹ * Ah)).PosDef := Matrix.PosDef.one.add_posSemidef (by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self (Bh⁻¹ * Ah))
  rw [convCov, transpose_mul_inv_mul]
  exact hD.inv

/-- `D_{L(B),M,c}(Bz) ≥ 0`. -/
theorem gaussianPMF_nonneg (B M : Matrix (Fin m) (Fin m) ℝ) (c : Fin m → ℝ) (z : Fin m → ℤ) :
    0 ≤ gaussianPMF B M c z :=
  div_nonneg (Real.exp_pos _).le (tsum_nonneg fun _ => (Real.exp_pos _).le)

/-- `D_{L(B),M,c}(Bz) > 0`. -/
theorem gaussianPMF_pos {B M : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0) (hM : M.det ≠ 0)
    (c : Fin m → ℝ) (z : Fin m → ℤ) : 0 < gaussianPMF B M c z :=
  div_pos (Real.exp_pos _) (rhoSum_pos hB hM c)

/-- `‖(a, b)‖² = ‖a‖² + ‖b‖²`. -/
theorem sqNorm_append {k : ℕ} (a b : Fin k → ℝ) :
    sqNorm (Fin.append a b) = sqNorm a + sqNorm b := by
  simp only [sqNorm, dotProduct, Fin.sum_univ_add, Fin.append_left, Fin.append_right]

/-- `D_{L(B),M,c}(Bz) ≤ 1`. -/
theorem gaussianPMF_le_one {B M : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0) (hM : M.det ≠ 0)
    (c : Fin m → ℝ) (z : Fin m → ℤ) : gaussianPMF B M c z ≤ 1 :=
  div_le_one_of_le₀ ((summable_rho hB hM c).le_tsum z fun _ _ => (Real.exp_pos _).le)
    (rhoSum_pos hB hM c).le

/-- `D_{ℤ^m,w,c}` is the product of the one-dimensional discrete Gaussians of standard deviation
`w/√(2π)`, as measures of singletons. -/
theorem ofReal_gaussianPMF_one_smul {w : ℝ} (hw : 0 < w) (c : Fin m → ℝ) (z : Fin m → ℤ) :
    ENNReal.ofReal (gaussianPMF 1 (w • (1 : Matrix (Fin m) (Fin m) ℝ)) c z) =
      ∏ i, discreteGaussianMeasure (Lemma5.stdDev w) (c i) {z i} := by
  rw [gaussianPMF_one_smul hw]
  change ENNReal.ofReal (∏ i, discreteGaussianPMF (Lemma5.stdDev w) (c i) (z i)) = _
  rw [ENNReal.ofReal_prod_of_nonneg fun i _ =>
    discreteGaussianPMF_nonneg _ _ (Lemma5.stdDev_pos hw) _]
  simp only [discreteGaussianMeasure_singleton]

/-- A law with `P{y} = K₀ w(y) Q{y}` for a bounded `w ≥ 0` is `Q` tilted by `w/E_Q[w]`. -/
theorem eq_withDensity_of_singleton {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable α] (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {w : α → ℝ} {K₀ b : ℝ} (hK₀ : 0 < K₀) (hw0 : ∀ y, 0 ≤ w y) (hwb : ∀ y, w y ≤ b)
    (h : ∀ y, P {y} = ENNReal.ofReal (K₀ * w y * (Q {y}).toReal)) :
    P = Q.withDensity fun y => ENNReal.ofReal (w y / ∫ y', w y' ∂Q) := by
  have hint : Integrable w Q := Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable b
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hw0 y)]
      exact hwb y)
  have hsum1 : ∑' y, (P {y}).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq fun y => measure_ne_top P _]
    have h1 := lintegral_countable' (μ := P) fun _ => (1 : ENNReal)
    simp only [lintegral_const, measure_univ, one_mul] at h1
    rw [← h1, ENNReal.toReal_one]
  have hval : ∀ y, (P {y}).toReal = K₀ * w y * (Q {y}).toReal := fun y => by
    rw [h y, ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg hK₀.le (hw0 y)) ENNReal.toReal_nonneg)]
  have hI : ∫ y, w y ∂Q = K₀⁻¹ := by
    rw [integral_countable hint]
    have e : ∀ y, Q.real {y} • w y = K₀⁻¹ * (P {y}).toReal := fun y => by
      rw [hval, measureReal_def, smul_eq_mul]
      field_simp
    rw [tsum_congr e, tsum_mul_left, hsum1, mul_one]
  refine Measure.ext_of_singleton fun y => ?_
  rw [withDensity_apply _ (measurableSet_singleton y), lintegral_singleton, hI, div_inv_eq_mul, h y,
    ← ENNReal.ofReal_toReal (measure_ne_top Q {y}), ← ENNReal.ofReal_mul (by
      exact mul_nonneg (hw0 y) hK₀.le), ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
  ring_nf

end LatticeGaussian

/-- `csc(π/(2n)) ≥ 0`. -/
theorem cscN_nonneg (n : ℕ) : 0 ≤ cscN n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [cscN]
  have h1 : (1 : ℝ) ≤ 2 * n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  exact one_div_nonneg.2 (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
    (div_le_self Real.pi_pos.le h1))

/-- `τ̄ ≥ 0` for `s ≥ 0`. -/
theorem tauBar_nonneg (P : Params) (n : ℕ) (hs : 0 ≤ P.s) : 0 ≤ tauBar P n := by
  have hc := cscN_nonneg n
  unfold tauBar
  exact add_nonneg (mul_nonneg (div_nonneg (mul_nonneg (by positivity) hc) (by positivity))
    (Real.sqrt_nonneg _)) (div_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (by positivity))

/-- `1 ≤ κ` for `0 ≤ ϵ < 1`. -/
theorem one_le_kappa {ϵ : ℝ} (hϵ₀ : 0 ≤ ϵ) (hϵ₁ : ϵ < 1) : 1 ≤ kappa ϵ := by
  rw [kappa, le_div_iff₀ (by linarith)]
  linarith

/-- `κ⁻¹ = (1 − ϵ)/(1 + ϵ)`. -/
theorem inv_kappa (ϵ : ℝ) : (kappa ϵ)⁻¹ = (1 - ϵ) / (1 + ϵ) := by
  rw [kappa, inv_div]

variable {n : ℕ}

namespace Key

/-- `L r √C ≥ η_ϵ(ℤ^{2n})` [ZKLY26, p. 19, l. 602-603]: the smallest eigenvalue of `C` is
`(1 + ‖B̂⁻¹Â‖₂²)⁻¹ ≥ q²/(β(p_u)² s² (1 + τ̄))` (sampling-scale estimate), and condition 3 asks
`L ≥ (β(p_u) s √(1 + τ̄)/(q r)) η_ϵ(ℤ^{2n})`. Assumed, not proved: `Key.GSCoeff u` and the
key-expansion facts `Key.UClose`, `Key.CholeskyRoot`, `Key.AClose` (`hu`, `hr`, `hC`, `hAc`). -/
theorem geSmoothing_convCov {ℓ : ℕ} (hn : n = 2 ^ ℓ) (P : Params) (K : Key n) (u : Fin n → ℝ)
    (A : Fin 2 → Fin 2 → Fin n → ℝ) (hq : 0 < P.q) (hK : K.Annular P) (hN : K.NTRU P)
    (hu : K.GSCoeff u) (hr : K.UClose P u) (hC : K.CholeskyRoot P A) (hAc : K.AClose P A)
    (hs : beta P n < P.s) {ϵ : ℝ} (hϵ : 0 < ϵ) (hr0 : 0 < P.r)
    (h3L : beta P n * P.s * √(1 + tauBar P n) / (P.q * P.r) *
      smoothingParam ϵ (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ) ≤ P.L) :
    GeSmoothing ϵ ((P.L * P.r) • CFC.sqrt (convCov (K.bHatMat P) (K.aHatCoefMat P)))
      (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ) := by
  have hn0 : 0 < n := by
    rw [hn]
    positivity
  have hβ := beta_pos P n hK.one_le_alpha hq
  have hs0 : 0 < P.s := hβ.trans hs
  have hq0 : (0 : ℝ) < P.q := by exact_mod_cast hq
  set μ := KMat.norm2 (K.bHatInv P * K.aHatMat P) ^ 2
  have hμ : 0 ≤ μ := sq_nonneg _
  have hU := one_add_sq_norm2_le hn P K u A hq hK hN hu hr hC hAc hs
  have hτ1 : 0 < 1 + tauBar P n := by
    have h1 : 0 < beta P n ^ 2 * P.s ^ 2 * (1 + tauBar P n) / (P.q : ℝ) ^ 2 := by linarith
    have h2 : 0 < beta P n ^ 2 * P.s ^ 2 / (P.q : ℝ) ^ 2 := by positivity
    rw [mul_div_right_comm] at h1
    exact pos_of_mul_pos_right h1 h2.le
  have hsq := Real.sqrt_pos.2 hτ1
  have hη0 : 0 < smoothingParam ϵ (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ) :=
    smoothingParam_pos (by omega) (by simp) hϵ
  have hco : 0 < beta P n * P.s * √(1 + tauBar P n) / (P.q * P.r) := by positivity
  have hL : (0 : ℝ) < P.L := lt_of_lt_of_le (mul_pos hco hη0) h3L
  set s' := P.L * P.r * P.q / (beta P n * P.s * √(1 + tauBar P n))
  have hs' : 0 < s' := by positivity
  have hη : smoothingParam ϵ (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ) ≤ s' := by
    rw [le_div_iff₀ (by positivity)]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at h3L
    linarith
  have hX := Key.sqNorm_inv_bHatMat_mul_le hn0 P K hq hN
  have hCs := LatticeGaussian.posSemidef_convCov_sub hμ hX
  have hCPD := LatticeGaussian.posDef_convCov (K.bHatMat P) (K.aHatCoefMat P)
  have hMM : ((P.L * P.r) • CFC.sqrt (convCov (K.bHatMat P) (K.aHatCoefMat P))) *
      ((P.L * P.r) • CFC.sqrt (convCov (K.bHatMat P) (K.aHatCoefMat P)))ᵀ =
        (P.L * P.r) ^ 2 • convCov (K.bHatMat P) (K.aHatCoefMat P) := by
    rw [smul_mul_transpose_smul, sqrt_mul_transpose_sqrt hCPD.posSemidef]
  refine geSmoothing_of_posSemidef (by simp)
    (det_ne_zero_of_mul_transpose hMM (by
      rw [Matrix.det_smul]
      exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ (by positivity))) hCPD.det_pos.ne'))
    hϵ hs' ?_ hη
  have hlam : s' ^ 2 ≤ (P.L * P.r) ^ 2 * (1 + μ)⁻¹ := by
    have e : s' ^ 2 =
        (P.L * P.r) ^ 2 * (beta P n ^ 2 * P.s ^ 2 * (1 + tauBar P n) / (P.q : ℝ) ^ 2)⁻¹ := by
      rw [div_pow, mul_pow (beta P n * P.s) (√(1 + tauBar P n)), Real.sq_sqrt hτ1.le]
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ (by linarith) hU) (sq_nonneg _)
  have e2 : (P.L * P.r) ^ 2 • convCov (K.bHatMat P) (K.aHatCoefMat P) -
      s' ^ 2 • (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ) =
        (P.L * P.r) ^ 2 • (convCov (K.bHatMat P) (K.aHatCoefMat P) - (1 + μ)⁻¹ • 1) +
          ((P.L * P.r) ^ 2 * (1 + μ)⁻¹ - s' ^ 2) • 1 := by
    rw [smul_sub, smul_smul, sub_smul]
    abel
  rw [hMM, e2]
  exact (hCs.smul (sq_nonneg _)).add (Matrix.PosSemidef.one.smul (by linarith))

private theorem negacyclicConvCoeff_neg_left (a b : Fin n → ℝ) :
    negacyclicConvCoeff (-a) b = -negacyclicConvCoeff a b := by
  funext k
  simp only [negacyclicConvCoeff, Pi.neg_apply, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun ij _ => by split_ifs <;> ring

private theorem append_sub {k : ℕ} (a b c d : Fin k → ℝ) :
    Fin.append (a - b) (c - d) = Fin.append a c - Fin.append b d := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [Fin.append_left, Fin.append_right, Pi.sub_apply]

/-- `B̂ (z₁ + ûz₂, z₂) = B (z₁, z₂)`. -/
private theorem bHatMat_mulVec_append (P : Params) (K : Key n) (z₁ z₂ : Fin n → ℤ) :
    K.bHatMat P *ᵥ Fin.append (ofInt z₁ + negacyclicConvCoeff (K.uHat P) (toReal z₂)) (ofInt z₂) =
      K.basisMat *ᵥ ofInt (Fin.append z₁ z₂) := by
  rw [bHatMat, ← Matrix.mulVec_mulVec]
  congr 1
  rw [← append_splitVec (uCoefMat (-K.uHat P) *ᵥ _), uCoefMat, splitVec_blocks_mulVec,
    splitVec_append]
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.append_left, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.one_mulVec,
      negacyclicMat_mulVec, negacyclicConvCoeff_neg_left, Pi.add_apply, Pi.neg_apply, ofInt]
    rw [show ofInt z₂ = toReal z₂ from rfl]
    ring
  · simp only [Fin.append_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.one_mulVec,
      Matrix.zero_mulVec, zero_add, ofInt]

/-- The two online Gaussians combine into `ρ_{rB̂}(z − c + Âx/L)` [ZKLY26, p. 19, l. 594-596]. -/
private theorem rho_mul_rho_eq (P : Params) (K : Key n) (hq : 0 < P.q) (hN : K.NTRU P)
    (hr : 0 < P.r) (c : Fin 2 → Fin n → ℝ) (z₁ z₂ : Fin n → ℤ) (x : Fin 2 → Fin n → ℤ) :
    rho (P.r • (1 : Matrix (Fin n) (Fin n) ℝ)) (centre P K (c - perturbation P K x) 1)
        (ofInt z₂) *
      rho (P.r • (1 : Matrix (Fin n) (Fin n) ℝ))
        (centre P K (c - perturbation P K x) 0 - negacyclicConvCoeff (K.uHat P) (toReal z₂))
        (ofInt z₁) =
      rho (P.r • K.bHatMat P) 0 (K.basisMat *ᵥ ofInt (Fin.append z₁ z₂) -
        Fin.append (c 0) (c 1) + (P.L : ℝ)⁻¹ • (K.aHatCoefMat P *ᵥ ofInt (Fin.append (x 0) (x 1))))
    := by
  set ch := centre P K (c - perturbation P K x)
  set v := Fin.append (ofInt z₁ - (ch 0 - negacyclicConvCoeff (K.uHat P) (toReal z₂)))
    (ofInt z₂ - ch 1) with hvdef
  have hBh := det_bHatMat_ne_zero P K hq hN
  have hv : K.bHatMat P *ᵥ v = K.basisMat *ᵥ ofInt (Fin.append z₁ z₂) - Fin.append (c 0) (c 1) +
      (P.L : ℝ)⁻¹ • (K.aHatCoefMat P *ᵥ ofInt (Fin.append (x 0) (x 1))) := by
    have e1 : v = Fin.append (ofInt z₁ + negacyclicConvCoeff (K.uHat P) (toReal z₂)) (ofInt z₂) -
        Fin.append (ch 0) (ch 1) := by
      rw [hvdef, ← append_sub]
      congr 1
      abel
    have e2 := bHatMat_mulVec_centre P K hq hN (c - perturbation P K x)
    rw [Pi.sub_apply, Pi.sub_apply, append_sub, perturbation_eq] at e2
    rw [e1, Matrix.mulVec_sub, bHatMat_mulVec_append, e2]
    abel
  have hinv : (K.bHatMat P)⁻¹ *ᵥ (K.basisMat *ᵥ ofInt (Fin.append z₁ z₂) -
      Fin.append (c 0) (c 1) + (P.L : ℝ)⁻¹ • (K.aHatCoefMat P *ᵥ ofInt (Fin.append (x 0) (x 1)))) =
        v := by
    rw [← hv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hBh),
      Matrix.one_mulVec]
  simp only [rho, ← Real.exp_add]
  congr 1
  rw [LatticeGaussian.inv_smul_of_ne hr.ne' (by simp),
    LatticeGaussian.inv_smul_of_ne hr.ne' (isUnit_iff_ne_zero.2 hBh), Matrix.smul_mulVec,
    Matrix.smul_mulVec, Matrix.smul_mulVec, sub_zero, hinv, inv_one, Matrix.one_mulVec,
    Matrix.one_mulVec, sqNorm_smul, sqNorm_smul, sqNorm_smul, sqNorm_append]
  ring

/-- `s²I − Σ_e = B̂B̂ᵗ + ÂÂᵗ`. -/
theorem sub_sigmaEMat (P : Params) (K : Key n) :
    P.s ^ 2 • (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ) - K.sigmaEMat P =
      K.bHatMat P * (K.bHatMat P)ᵀ + K.aHatCoefMat P * (K.aHatCoefMat P)ᵀ := by
  rw [sigmaEMat]
  abel

/-- `s²I − Σ_e` is positive definite under the NTRU equation. -/
theorem posDef_sub_sigmaEMat (P : Params) (K : Key n) (hq : 0 < P.q) (hN : K.NTRU P) :
    (P.s ^ 2 • (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ) - K.sigmaEMat P).PosDef := by
  rw [sub_sigmaEMat]
  have h := Matrix.PosDef.mul_conjTranspose_self (K.bHatMat P)
    (Matrix.vecMul_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2
      (isUnit_iff_ne_zero.2 (det_bHatMat_ne_zero P K hq hN))))
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h.add_posSemidef (by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose (K.aHatCoefMat P))

/-- Conditions 2-3 give `r > 0` and `L > 0`. -/
theorem r_pos_and_L_pos {ℓ : ℕ} (hn : n = 2 ^ ℓ) (P : Params) (K : Key n) (hq : 0 < P.q)
    (hK : K.Annular P) (hs : beta P n < P.s) {ϵ : ℝ} (hϵ₀ : 0 < ϵ)
    (h3r : smoothingParam ϵ (1 : Matrix (Fin n) (Fin n) ℝ) ≤ P.r)
    (h3L : beta P n * P.s * √(1 + tauBar P n) / (P.q * P.r) *
      smoothingParam ϵ (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ) ≤ P.L) :
    0 < P.r ∧ 0 < P.L := by
  have hn0 : 0 < n := by
    rw [hn]
    positivity
  have hr : 0 < P.r := (smoothingParam_pos hn0 (by simp) hϵ₀).trans_le h3r
  have hβ := beta_pos P n hK.one_le_alpha hq
  have hs0 : 0 < P.s := hβ.trans hs
  have hτ := tauBar_nonneg P n hs0.le
  have hq0 : (0 : ℝ) < P.q := by exact_mod_cast hq
  have hη0 : 0 < smoothingParam ϵ (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ) :=
    smoothingParam_pos (by omega) (by simp) hϵ₀
  have hco : 0 < beta P n * P.s * √(1 + tauBar P n) / (P.q * P.r) := by positivity
  exact ⟨hr, by exact_mod_cast (mul_pos hco hη0).trans_le h3L⟩

/-- The summand of the law of Algorithm 3 at the coordinates `(z₁, z₂)`: perturbation `x`. -/
private noncomputable def coordTerm (P : Params) (K : Key n) (c : Fin 2 → Fin n → ℝ)
    (z₁ z₂ : Fin n → ℤ) (x : Fin 2 → Fin n → ℤ) : ℝ :=
  gaussianPMF 1 (((P.L : ℝ) * P.r) • (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ)) 0
      (Fin.append (x 0) (x 1)) *
    gaussianPMF 1 (P.r • (1 : Matrix (Fin n) (Fin n) ℝ))
      (centre P K (c - perturbation P K x) 1) z₂ *
    gaussianPMF 1 (P.r • (1 : Matrix (Fin n) (Fin n) ℝ))
      (centre P K (c - perturbation P K x) 0 - negacyclicConvCoeff (K.uHat P) (toReal z₂)) z₁

private theorem coordTerm_nonneg (P : Params) (K : Key n) (c : Fin 2 → Fin n → ℝ)
    (z₁ z₂ : Fin n → ℤ) (x : Fin 2 → Fin n → ℤ) : 0 ≤ coordTerm P K c z₁ z₂ x :=
  mul_nonneg (mul_nonneg (gaussianPMF_nonneg _ _ _ _) (gaussianPMF_nonneg _ _ _ _))
    (gaussianPMF_nonneg _ _ _ _)

private theorem det_smul_one_ne_zero {k : ℕ} {w : ℝ} (hw : 0 < w) :
    (w • (1 : Matrix (Fin k) (Fin k) ℝ)).det ≠ 0 := by
  rw [Matrix.det_smul, Matrix.det_one, mul_one]
  exact pow_ne_zero _ hw.ne'

private theorem injective_append : Function.Injective
    fun x : Fin 2 → Fin n → ℤ => Fin.append (x 0) (x 1) := by
  intro x y h
  have h0 : x 0 = y 0 := funext fun k => by
    have := congrFun h (Fin.castAdd n k)
    simpa only [Fin.append_left] using this
  have h1 : x 1 = y 1 := funext fun k => by
    have := congrFun h (Fin.natAdd n k)
    simpa only [Fin.append_right] using this
  funext i
  fin_cases i
  · exact h0
  · exact h1

private theorem summable_coordTerm (P : Params) (K : Key n) (c : Fin 2 → Fin n → ℝ)
    (hr : 0 < P.r) (hL : 0 < P.L) (z₁ z₂ : Fin n → ℤ) :
    Summable (coordTerm P K c z₁ z₂) := by
  have hr' : (0 : ℝ) < P.L * P.r := mul_pos (by exact_mod_cast hL) hr
  refine Summable.of_nonneg_of_le (coordTerm_nonneg P K c z₁ z₂) (fun x => ?_)
    ((((summable_rho (B := 1) (by simp) (det_smul_one_ne_zero hr') 0).div_const
      (rhoSum 1 (((P.L : ℝ) * P.r) • (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ)) 0))).comp_injective
        injective_append)
  have h1 := gaussianPMF_le_one (B := 1) (by simp) (det_smul_one_ne_zero hr)
    (centre P K (c - perturbation P K x) 1) z₂
  have h2 := gaussianPMF_le_one (B := 1) (by simp) (det_smul_one_ne_zero hr)
    (centre P K (c - perturbation P K x) 0 - negacyclicConvCoeff (K.uHat P) (toReal z₂)) z₁
  have h3 := gaussianPMF_nonneg 1 (((P.L : ℝ) * P.r) • (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ))
    0 (Fin.append (x 0) (x 1))
  calc coordTerm P K c z₁ z₂ x ≤ gaussianPMF 1
        (((P.L : ℝ) * P.r) • (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ)) 0
        (Fin.append (x 0) (x 1)) * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 h3) h2 (gaussianPMF_nonneg _ _ _ _)
          (by rw [mul_one]; exact h3)
    _ = _ := by rw [mul_one, mul_one]; rfl

private theorem coordTerm_pos (P : Params) (K : Key n) (c : Fin 2 → Fin n → ℝ)
    (hr : 0 < P.r) (hL : 0 < P.L) (z₁ z₂ : Fin n → ℤ) (x : Fin 2 → Fin n → ℤ) :
    0 < coordTerm P K c z₁ z₂ x := by
  have hr' : (0 : ℝ) < P.L * P.r := mul_pos (by exact_mod_cast hL) hr
  exact mul_pos (mul_pos (gaussianPMF_pos (by simp) (det_smul_one_ne_zero hr') _ _)
    (gaussianPMF_pos (by simp) (det_smul_one_ne_zero hr) _ _))
    (gaussianPMF_pos (by simp) (det_smul_one_ne_zero hr) _ _)

private theorem surjective_append : Function.Surjective
    fun x : Fin 2 → Fin n → ℤ => Fin.append (x 0) (x 1) := fun X =>
  ⟨![fun k => X (Fin.castAdd n k), fun k => X (Fin.natAdd n k)], Fin.append_castAdd_natAdd⟩

/-- The constant `C₀ = ρ_{Lr√C}(ℤ^{2n}) / (ρ_{Lr}(ℤ^{2n}) ρ_r(ℤⁿ)²)`. -/
private noncomputable def lawConst (P : Params) (K : Key n) : ℝ :=
  rhoSum 1 (((P.L : ℝ) * P.r) • CFC.sqrt (convCov (K.bHatMat P) (K.aHatCoefMat P))) 0 /
    (rhoSum 1 (((P.L : ℝ) * P.r) • (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ)) 0 *
      rhoSum 1 (P.r • (1 : Matrix (Fin n) (Fin n) ℝ)) 0 ^ 2)

/-- Normalisers `N₁, N₂ ∈ [κ⁻¹R, R]` [ZKLY26, p. 19, l. 597] put `T/(R_L N₁N₂)` in
`[T/(R_L R²), κ² T/(R_L R²)]`. -/
private theorem div_mem_of_normalisers {T RL R N1 N2 κ : ℝ} (hT : 0 ≤ T) (hRL : 0 < RL)
    (hκ : 0 < κ) (hR : 0 < R) (h1 : N1 ∈ Set.Icc (κ⁻¹ * R) R) (h2 : N2 ∈ Set.Icc (κ⁻¹ * R) R) :
    T / (RL * R ^ 2) ≤ T / (RL * (N1 * N2)) ∧
      T / (RL * (N1 * N2)) ≤ κ ^ 2 * (T / (RL * R ^ 2)) := by
  obtain ⟨h1l, h1u⟩ := h1
  obtain ⟨h2l, h2u⟩ := h2
  have hp : 0 < κ⁻¹ * R := mul_pos (inv_pos.2 hκ) hR
  constructor
  · refine div_le_div_of_nonneg_left hT
      (mul_pos hRL (mul_pos (hp.trans_le h1l) (hp.trans_le h2l))) ?_
    rw [sq]
    exact mul_le_mul_of_nonneg_left (mul_le_mul h1u h2u (hp.le.trans h2l) hR.le) hRL.le
  · have e : κ ^ 2 * (T / (RL * R ^ 2)) = T / (RL * ((κ⁻¹ * R) * (κ⁻¹ * R))) := by
      field_simp
    rw [e]
    refine div_le_div_of_nonneg_left hT (by positivity) ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul h1l h2l hp.le (hp.le.trans h1l)) hRL.le

/-- **The bounds of Lemma 4** [ZKLY26, p. 19, l. 595-606]: the mass of `(z₁, z₂)` lies in
`[κ⁻¹, κ²] · C₀ ρ_{r√(B̂B̂ᵗ + ÂÂᵗ), c}(Bz)`. -/
private theorem tsum_coordTerm_mem {ℓ : ℕ} (hn : n = 2 ^ ℓ) (P : Params) (K : Key n)
    (u : Fin n → ℝ) (A : Fin 2 → Fin 2 → Fin n → ℝ) (hq : 0 < P.q) (hK : K.Annular P)
    (hN : K.NTRU P) (hu : K.GSCoeff u) (hr : K.UClose P u) (hC : K.CholeskyRoot P A)
    (hAc : K.AClose P A) (hs : beta P n < P.s) {ϵ : ℝ} (hϵ₀ : 0 < ϵ) (hϵ₁ : ϵ < 1)
    (h3r : smoothingParam ϵ (1 : Matrix (Fin n) (Fin n) ℝ) ≤ P.r)
    (h3L : beta P n * P.s * √(1 + tauBar P n) / (P.q * P.r) *
      smoothingParam ϵ (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ) ≤ P.L)
    (c : Fin 2 → Fin n → ℝ) (z₁ z₂ : Fin n → ℤ) :
    ∑' x, coordTerm P K c z₁ z₂ x ∈ Set.Icc
      ((kappa ϵ)⁻¹ * (lawConst P K * rho (P.r • CFC.sqrt (K.bHatMat P * (K.bHatMat P)ᵀ +
        K.aHatCoefMat P * (K.aHatCoefMat P)ᵀ)) (Fin.append (c 0) (c 1))
          (K.basisMat *ᵥ ofInt (Fin.append z₁ z₂))))
      (kappa ϵ ^ 2 * (lawConst P K * rho (P.r • CFC.sqrt (K.bHatMat P * (K.bHatMat P)ᵀ +
        K.aHatCoefMat P * (K.aHatCoefMat P)ᵀ)) (Fin.append (c 0) (c 1))
          (K.basisMat *ᵥ ofInt (Fin.append z₁ z₂)))) := by
  obtain ⟨hr0, hL0⟩ := r_pos_and_L_pos hn P K hq hK hs hϵ₀ h3r h3L
  have hLr : (0 : ℝ) < P.L * P.r := mul_pos (by exact_mod_cast hL0) hr0
  set Bh := K.bHatMat P
  set Ah := K.aHatCoefMat P
  set Y := K.basisMat *ᵥ ofInt (Fin.append z₁ z₂) - Fin.append (c 0) (c 1)
  set Rr := rhoSum 1 (P.r • (1 : Matrix (Fin n) (Fin n) ℝ)) 0
  set RL := rhoSum 1 (((P.L : ℝ) * P.r) • (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ)) 0
  set MC := ((P.L : ℝ) * P.r) • CFC.sqrt (convCov Bh Ah)
  set κ := kappa ϵ
  have hκ1 := one_le_kappa hϵ₀.le hϵ₁
  have hκ0 : 0 < κ := zero_lt_one.trans_le hκ1
  have hRr : 0 < Rr := rhoSum_pos (by simp) (det_smul_one_ne_zero hr0) 0
  have hRL : 0 < RL := rhoSum_pos (by simp) (det_smul_one_ne_zero hLr) 0
  have hCPD := LatticeGaussian.posDef_convCov Bh Ah
  have hMC : MC * MCᵀ = ((P.L : ℝ) * P.r) ^ 2 • convCov Bh Ah := by
    rw [smul_mul_transpose_smul, sqrt_mul_transpose_sqrt hCPD.posSemidef]
  have hMCd : MC.det ≠ 0 := det_ne_zero_of_mul_transpose hMC (by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hLr.ne')) hCPD.det_pos.ne')
  have hgs : GeSmoothing ϵ (P.r • (1 : Matrix (Fin n) (Fin n) ℝ)) 1 :=
    (geSmoothing_smul_one_iff (by simp) hϵ₀ hr0).2 h3r
  have hN1 : ∀ c' : Fin n → ℝ, rhoSum 1 (P.r • (1 : Matrix (Fin n) (Fin n) ℝ)) c' ∈
      Set.Icc (κ⁻¹ * Rr) Rr := fun c' => by
    have h := rhoSum_one_mem_Icc (det_smul_one_ne_zero hr0) hϵ₀ hϵ₁ hgs c'
    rwa [← inv_kappa] at h
  set T : (Fin 2 → Fin n → ℤ) → ℝ := fun x =>
    rho (((P.L : ℝ) * P.r) • (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ)) 0
        (ofInt (Fin.append (x 0) (x 1))) *
      rho (P.r • Bh) 0 (Y + (P.L : ℝ)⁻¹ • (Ah *ᵥ ofInt (Fin.append (x 0) (x 1)))) with hTdef
  have hT0 : ∀ x, 0 ≤ T x := fun x => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hterm : ∀ x, coordTerm P K c z₁ z₂ x = T x /
      (RL * (rhoSum 1 (P.r • (1 : Matrix (Fin n) (Fin n) ℝ))
          (centre P K (c - perturbation P K x) 1) *
        rhoSum 1 (P.r • (1 : Matrix (Fin n) (Fin n) ℝ))
          (centre P K (c - perturbation P K x) 0 -
            negacyclicConvCoeff (K.uHat P) (toReal z₂)))) := fun x => by
    have h := rho_mul_rho_eq P K hq hN hr0 c z₁ z₂ x
    simp only [coordTerm, gaussianPMF, Matrix.one_mulVec, hTdef]
    rw [show Y = K.basisMat *ᵥ ofInt (Fin.append z₁ z₂) - Fin.append (c 0) (c 1) from rfl, ← h]
    ring
  have hlow : ∀ x, T x / (RL * Rr ^ 2) ≤ coordTerm P K c z₁ z₂ x := fun x => by
    rw [hterm]
    exact (div_mem_of_normalisers (hT0 x) hRL hκ0 hRr (hN1 _) (hN1 _)).1
  have hup : ∀ x, coordTerm P K c z₁ z₂ x ≤ κ ^ 2 * (T x / (RL * Rr ^ 2)) := fun x => by
    rw [hterm]
    exact (div_mem_of_normalisers (hT0 x) hRL hκ0 hRr (hN1 _) (hN1 _)).2
  have hsumC := summable_coordTerm P K c hr0 hL0 z₁ z₂
  have hsumT : Summable T := by
    refine Summable.of_nonneg_of_le hT0 (fun x => ?_) (hsumC.mul_left (RL * Rr ^ 2))
    have h := hlow x
    rw [div_le_iff₀ (by positivity)] at h
    linarith
  have hsumT' : ∑' x, T x = rho (P.r • CFC.sqrt (Bh * Bhᵀ + Ah * Ahᵀ)) 0 Y *
      rhoSum 1 MC (convCentre Bh Ah P.L Y) := by
    rw [← tsum_rho_mul_rho_eq (det_bHatMat_ne_zero P K hq hN) (by exact_mod_cast hL0) hr0 Y]
    exact (Equiv.ofBijective _ ⟨injective_append, surjective_append⟩).tsum_eq
      (fun X : Fin (n + n) → ℤ =>
        rho (((P.L : ℝ) * P.r) • (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ)) 0 (ofInt X) *
          rho (P.r • Bh) 0 (Y + (P.L : ℝ)⁻¹ • (Ah *ᵥ ofInt X)))
  have hρ : rho (P.r • CFC.sqrt (Bh * Bhᵀ + Ah * Ahᵀ)) (Fin.append (c 0) (c 1))
      (K.basisMat *ᵥ ofInt (Fin.append z₁ z₂)) =
        rho (P.r • CFC.sqrt (Bh * Bhᵀ + Ah * Ahᵀ)) 0 Y := by
    simp only [rho, sub_zero, Y]
  have hRC := rhoSum_one_mem_Icc hMCd hϵ₀ hϵ₁
    (geSmoothing_convCov hn P K u A hq hK hN hu hr hC hAc hs hϵ₀ hr0 h3L) (convCentre Bh Ah P.L Y)
  rw [← inv_kappa] at hRC
  have hρ0 : 0 ≤ rho (P.r • CFC.sqrt (Bh * Bhᵀ + Ah * Ahᵀ)) 0 Y := (Real.exp_pos _).le
  rw [hρ, lawConst]
  constructor
  · calc κ⁻¹ * (rhoSum 1 MC 0 / (RL * Rr ^ 2) * rho (P.r • CFC.sqrt (Bh * Bhᵀ + Ah * Ahᵀ)) 0 Y)
        = rho (P.r • CFC.sqrt (Bh * Bhᵀ + Ah * Ahᵀ)) 0 Y * (κ⁻¹ * rhoSum 1 MC 0) /
            (RL * Rr ^ 2) := by
          ring
      _ ≤ rho (P.r • CFC.sqrt (Bh * Bhᵀ + Ah * Ahᵀ)) 0 Y * rhoSum 1 MC (convCentre Bh Ah P.L Y) /
            (RL * Rr ^ 2) := by
          gcongr
          exact hRC.1
      _ = ∑' x, T x / (RL * Rr ^ 2) := by rw [tsum_div_const, hsumT']
      _ ≤ ∑' x, coordTerm P K c z₁ z₂ x :=
          Summable.tsum_le_tsum hlow (hsumT.div_const _) hsumC
  · calc ∑' x, coordTerm P K c z₁ z₂ x ≤ ∑' x, κ ^ 2 * (T x / (RL * Rr ^ 2)) :=
          Summable.tsum_le_tsum hup hsumC ((hsumT.div_const _).mul_left _)
      _ = κ ^ 2 * (rho (P.r • CFC.sqrt (Bh * Bhᵀ + Ah * Ahᵀ)) 0 Y *
            rhoSum 1 MC (convCentre Bh Ah P.L Y) / (RL * Rr ^ 2)) := by
          rw [tsum_mul_left, tsum_div_const, hsumT']
      _ ≤ κ ^ 2 * (rhoSum 1 MC 0 / (RL * Rr ^ 2) *
            rho (P.r • CFC.sqrt (Bh * Bhᵀ + Ah * Ahᵀ)) 0 Y) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_mul_eq_mul_div, mul_comm (rhoSum 1 MC 0)]
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hRC.2 hρ0) (by positivity)

variable {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m]

omit [LawfulMonad m] in
/-- The mass of a bind at a point, over a countable source. -/
private theorem evalDist_bind_singleton {α β : Type} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α] [MeasurableSpace β] [MeasurableSingletonClass β]
    (mx : m α) (f : α → m β) (b : β) :
    𝒟[mx >>= f] {b} = ∑' a, 𝒟[mx] {a} * 𝒟[f a] {b} := by
  rw [evalDist_bind_of_discrete, Measure.bind_apply (measurableSet_singleton b)
    Measurable.of_discrete.aemeasurable, lintegral_countable']
  exact tsum_congr fun a => mul_comm _ _

private theorem preimage_cons_singleton {k : ℕ} (a : ℤ) (z : Fin (k + 1) → ℤ) :
    (fun w : Fin k → ℤ => (Fin.cons a w : Fin (k + 1) → ℤ)) ⁻¹' {z} =
      if a = z 0 then {Fin.tail z} else ∅ := by
  ext w
  split_ifs with h
  · subst h
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      rw [← h, Fin.tail_cons]
    · rintro rfl
      exact Fin.cons_self_tail z
  · simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    intro hc
    exact h (by rw [← hc, Fin.cons_zero])

private theorem preimage_pair_singleton {α β : Type} [DecidableEq β] (w₂ z₂ : β) (z₁ : α) :
    (fun w₁ : α => (w₁, w₂)) ⁻¹' {(z₁, z₂)} = if w₂ = z₂ then {z₁} else ∅ := by
  ext w
  split_ifs with h <;> simp [h]

/-- The law of `queryVec t` is the product of the answer laws. -/
private theorem evalDist_queryVec_singleton (P : Params) (implE : QueryImpl samplerSpec m)
    (hE : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implE t) = answer P id t) {k : ℕ}
    (t : Fin k → Query) (z : Fin k → ℤ) :
    𝒟[simulateQ implE (queryVec t)] {z} = ∏ i, answer P id (t i) {z i} := by
  induction k with
  | zero =>
    simp only [queryVec, simulateQ_pure, evalDist_pure, Finset.univ_eq_empty, Finset.prod_empty]
    exact Measure.dirac_apply_of_mem (Subsingleton.elim _ _)
  | succ k ih =>
    simp only [queryVec, simulateQ_bind, simulateQ_spec_query, bind_pure_comp, simulateQ_map]
    rw [evalDist_bind_singleton, tsum_eq_single (z 0) fun a ha => by
      rw [evalDist_map_of_discrete, Measure.map_apply Measurable.of_discrete
        (measurableSet_singleton _), preimage_cons_singleton, ite_eq_right ha, measure_empty,
        mul_zero]]
    rw [evalDist_map_of_discrete, Measure.map_apply Measurable.of_discrete
      (measurableSet_singleton _), preimage_cons_singleton, ite_eq_left rfl, ih, Fin.prod_univ_succ,
      hE]
    rfl

/-- The law of Algorithm 3 at the coordinates [ZKLY26, p. 19, l. 595-596]: `(z₁, z₂)` has mass
`Σ_x D_{ℤ^{2n},Lr}(x) D_{ℤⁿ,r,ĉ₂}(z₂) D_{ℤⁿ,r,c′₁}(z₁)` with `ĉ = B̂⁻¹(c − Âx/L)` and
`c′₁ = ĉ₁ − û z₂`, for perfect integer samplers. -/
theorem evalDist_sampleCoords_singleton (P : Params) (K : Key n) (c : Fin 2 → Fin n → ℝ)
    (hr : 0 < P.r) (hL : 0 < P.L) (implE : QueryImpl samplerSpec m)
    (hE : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implE t) = answer P id t)
    (z₁ z₂ : Fin n → ℤ) :
    𝒟[simulateQ implE (sampleCoords P K c)] {(z₁, z₂)} =
      ENNReal.ofReal (∑' x : Fin 2 → Fin n → ℤ,
        gaussianPMF 1 (((P.L : ℝ) * P.r) • (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ)) 0
            (Fin.append (x 0) (x 1)) *
          gaussianPMF 1 (P.r • (1 : Matrix (Fin n) (Fin n) ℝ))
            (centre P K (c - perturbation P K x) 1) z₂ *
          gaussianPMF 1 (P.r • (1 : Matrix (Fin n) (Fin n) ℝ))
            (centre P K (c - perturbation P K x) 0 -
              negacyclicConvCoeff (K.uHat P) (toReal z₂)) z₁) := by
  change _ = ENNReal.ofReal (∑' x, coordTerm P K c z₁ z₂ x)
  simp only [sampleCoords, simulateQ_bind, simulateQ_map, bind_pure_comp,
    evalDist_bind_singleton, evalDist_map_of_discrete,
    Measure.map_apply Measurable.of_discrete (measurableSet_singleton _),
    preimage_pair_singleton, apply_ite, measure_empty, mul_zero, tsum_ite_eq,
    evalDist_queryVec_singleton P implE hE]
  have hr' : (0 : ℝ) < P.L * P.r := mul_pos (by exact_mod_cast hL) hr
  set G := coordTerm P K c z₁ z₂ with hGdef
  have hG0 := coordTerm_nonneg P K c z₁ z₂
  have hsum := summable_coordTerm P K c hr hL z₁ z₂
  rw [ENNReal.ofReal_tsum_of_nonneg hG0 hsum, ← (piFinTwoEquiv fun _ => Fin n → ℤ).symm.tsum_eq,
    show (∑' p, ENNReal.ofReal (G ((piFinTwoEquiv fun _ => Fin n → ℤ).symm p))) =
      ∑' a, ∑' b, ENNReal.ofReal (G ((piFinTwoEquiv fun _ => Fin n → ℤ).symm (a, b))) from
      tsum_prod (f := fun a b =>
        ENNReal.ofReal (G ((piFinTwoEquiv fun _ => Fin n → ℤ).symm (a, b))))]
  refine tsum_congr fun a => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun b => ?_
  simp only [hGdef, coordTerm, ENNReal.ofReal_mul (mul_nonneg (gaussianPMF_nonneg _ _ _ _)
      (gaussianPMF_nonneg _ _ _ _)), ENNReal.ofReal_mul (gaussianPMF_nonneg _ _ _ _),
    ofReal_gaussianPMF_one_smul hr', ofReal_gaussianPMF_one_smul hr, Fin.prod_univ_add]
  have he : (piFinTwoEquiv fun _ => Fin n → ℤ).symm (a, b) = ![a, b] := rfl
  simp only [he, answer, id, Fin.append_left, Fin.append_right, Pi.zero_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private theorem evalDist_sample_eq_map (P : Params) (K : Key n) (c : Fin 2 → Fin n → ℝ)
    (implE : QueryImpl samplerSpec m) :
    𝒟[simulateQ implE (sample P K c)] =
      (𝒟[simulateQ implE (sampleCoords P K c)]).map fun p => latticePoint K p.1 p.2 := by
  simp only [sample, simulateQ_map]
  exact evalDist_map_of_discrete _ _

private theorem latticePoint_injective (P : Params) (K : Key n) (hq : 0 < P.q) (hN : K.NTRU P) :
    Function.Injective fun p : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint K p.1 p.2 := by
  intro p p' h
  have h3 : Fin.append p.1 p.2 = Fin.append p'.1 p'.2 := by
    apply injective_mulVec_ofInt (det_basisMat_ne_zero P K hq hN)
    simp only at h
    simp only [K.basisMat_mulVec_ofInt, h]
  exact Prod.ext
    (funext fun k => by simpa only [Fin.append_left] using congrFun h3 (Fin.castAdd n k))
    (funext fun k => by simpa only [Fin.append_right] using congrFun h3 (Fin.natAdd n k))

private theorem evalDist_sample_latticePoint (P : Params) (K : Key n) (c : Fin 2 → Fin n → ℝ)
    (hq : 0 < P.q) (hN : K.NTRU P) (hr : 0 < P.r) (hL : 0 < P.L)
    (implE : QueryImpl samplerSpec m)
    (hE : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implE t) = answer P id t)
    (z₁ z₂ : Fin n → ℤ) :
    𝒟[simulateQ implE (sample P K c)] {latticePoint K z₁ z₂} =
      ENNReal.ofReal (∑' x, coordTerm P K c z₁ z₂ x) := by
  have hpre : (fun p : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint K p.1 p.2) ⁻¹'
      {latticePoint K z₁ z₂} = {(z₁, z₂)} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact (latticePoint_injective P K hq hN).eq_iff (b := (z₁, z₂))
  rw [evalDist_sample_eq_map, Measure.map_apply Measurable.of_discrete (measurableSet_singleton _),
    hpre, evalDist_sampleCoords_singleton P K c hr hL implE hE]
  rfl

/-- **Lemma 4, support** [ZKLY26, p. 7, l. 237; p. 19, l. 609]: with perfect integer samplers of
positive widths, the output law of Algorithm 3 has support `L(B)`. Assumed: perfect integer
samplers (`hE`). -/
theorem evalDist_sample_pos_iff (P : Params) (K : Key n) (c : Fin 2 → Fin n → ℝ)
    (hr : 0 < P.r) (hL : 0 < P.L) (implE : QueryImpl samplerSpec m)
    (hE : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implE t) = answer P id t)
    (y : Fin 2 → Fin n → ℤ) :
    0 < 𝒟[simulateQ implE (sample P K c)] {y} ↔ ∃ z₁ z₂, latticePoint K z₁ z₂ = y := by
  rw [evalDist_sample_eq_map, Measure.map_apply Measurable.of_discrete (measurableSet_singleton y)]
  constructor
  · intro h
    by_contra hne
    have he : (fun p : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint K p.1 p.2) ⁻¹' {y} = ∅ := by
      ext p
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      exact fun hp => hne ⟨p.1, p.2, hp⟩
    rw [he, measure_empty] at h
    exact lt_irrefl _ h
  · rintro ⟨z₁, z₂, rfl⟩
    have hmem : ((z₁, z₂) : (Fin n → ℤ) × (Fin n → ℤ)) ∈
        (fun p : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint K p.1 p.2) ⁻¹'
          {latticePoint K z₁ z₂} := rfl
    refine lt_of_lt_of_le ?_ (measure_mono (Set.singleton_subset_iff.2 hmem))
    rw [evalDist_sampleCoords_singleton P K c hr hL implE hE, ENNReal.ofReal_pos]
    exact (summable_coordTerm P K c hr hL z₁ z₂).tsum_pos (coordTerm_nonneg P K c z₁ z₂) 0
      (coordTerm_pos P K c hr hL z₁ z₂ 0)

/-- `𝒬_e` is a probability measure: `s²I − Σ_e = B̂B̂ᵗ + ÂÂᵗ` is positive definite. -/
theorem isProbabilityMeasure_gaussianQe (P : Params) (K : Key n) (hq : 0 < P.q)
    (hN : K.NTRU P) (hr0 : 0 < P.r) (c : Fin 2 → Fin n → ℝ) :
    IsProbabilityMeasure (K.gaussianQe P c) := by
  have hPD := posDef_sub_sigmaEMat P K hq hN
  refine isProbabilityMeasure_latticeGaussian P K hq hN
    (det_ne_zero_of_mul_transpose (smul_mul_transpose_smul _ _) ?_) c
  rw [sqrt_mul_transpose_sqrt hPD.posSemidef, Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hr0.ne')) hPD.det_pos.ne'

/-- `D_{L(B),M,c}` has no mass off the lattice points `latticePoint K z₁ z₂`. -/
private theorem latticeGaussian_singleton_eq_zero (K : Key n)
    (M : Matrix (Fin (n + n)) (Fin (n + n)) ℝ) (c : Fin 2 → Fin n → ℝ) {y : Fin 2 → Fin n → ℤ}
    (hy : ¬∃ p : (Fin n → ℤ) × (Fin n → ℤ), latticePoint K p.1 p.2 = y) :
    K.latticeGaussian M c {y} = 0 := by
  rw [latticeGaussian, Measure.map_apply Measurable.of_discrete (measurableSet_singleton y)]
  convert measure_empty (μ := gaussianMeasure K.basisMat M (Fin.append (c 0) (c 1)))
  ext z
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
  exact fun hz => hy ⟨(fun k => z (Fin.castAdd n k), fun k => z (Fin.natAdd n k)), hz⟩

/-- **Lemma 4, density** [ZKLY26, p. 7, l. 237; p. 19, l. 606-608]: `𝒫 = 𝒬_e · a/E_{𝒬_e}[a]`
with `a_z ∈ [κ⁻¹, κ²]`. Assumed, not proved: `Key.GSCoeff u`, the key-expansion facts
`Key.UClose`, `Key.CholeskyRoot`, `Key.AClose` (`hu`, `hr`, `hC`, `hAc`) and perfect integer
samplers (`hE`). -/
theorem exists_evalDist_sample_eq_withDensity {ℓ : ℕ} (hn : n = 2 ^ ℓ) (P : Params) (K : Key n)
    (u : Fin n → ℝ) (A : Fin 2 → Fin 2 → Fin n → ℝ) (hq : 0 < P.q) (hK : K.Annular P)
    (hN : K.NTRU P) (hu : K.GSCoeff u) (hr : K.UClose P u) (hC : K.CholeskyRoot P A)
    (hAc : K.AClose P A) (hs : beta P n < P.s) {ϵ : ℝ} (hϵ₀ : 0 < ϵ) (hϵ₁ : ϵ < 1)
    (h3r : smoothingParam ϵ (1 : Matrix (Fin n) (Fin n) ℝ) ≤ P.r)
    (h3L : beta P n * P.s * √(1 + tauBar P n) / (P.q * P.r) *
      smoothingParam ϵ (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ) ≤ P.L)
    (c : Fin 2 → Fin n → ℝ) (implE : QueryImpl samplerSpec m)
    (hE : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implE t) = answer P id t) :
    ∃ w : (Fin 2 → Fin n → ℤ) → ℝ, (∀ y, w y ∈ Set.Icc (kappa ϵ)⁻¹ (kappa ϵ ^ 2)) ∧
      𝒟[simulateQ implE (sample P K c)] =
        (K.gaussianQe P c).withDensity
          fun y => ENNReal.ofReal (w y / ∫ y', w y' ∂(K.gaussianQe P c)) := by
  classical
  obtain ⟨hr0, hL0⟩ := r_pos_and_L_pos hn P K hq hK hs hϵ₀ h3r h3L
  have hLr : (0 : ℝ) < P.L * P.r := mul_pos (by exact_mod_cast hL0) hr0
  have := isProbabilityMeasure_gaussianQe P K hq hN hr0 c
  have := isProbabilityMeasure_evalDist_sample P K c id hr0 hL0 implE hE
  have hκ1 := one_le_kappa hϵ₀.le hϵ₁
  have hκ0 : 0 < kappa ϵ := zero_lt_one.trans_le hκ1
  set MS := P.r • CFC.sqrt (K.bHatMat P * (K.bHatMat P)ᵀ + K.aHatCoefMat P * (K.aHatCoefMat P)ᵀ)
  have hPD := posDef_sub_sigmaEMat P K hq hN
  rw [sub_sigmaEMat] at hPD
  have hMSd : MS.det ≠ 0 := det_ne_zero_of_mul_transpose (smul_mul_transpose_smul _ _) (by
    rw [sqrt_mul_transpose_sqrt hPD.posSemidef, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hr0.ne')) hPD.det_pos.ne')
  have hQe : K.gaussianQe P c = K.latticeGaussian MS c := by rw [gaussianQe, sub_sigmaEMat]
  have hB := det_basisMat_ne_zero P K hq hN
  set Z := rhoSum K.basisMat MS (Fin.append (c 0) (c 1))
  have hZ : 0 < Z := rhoSum_pos hB hMSd _
  have hCPD := LatticeGaussian.posDef_convCov (K.bHatMat P) (K.aHatCoefMat P)
  have hMCd : (((P.L : ℝ) * P.r) • CFC.sqrt (convCov (K.bHatMat P) (K.aHatCoefMat P))).det ≠ 0 :=
    det_ne_zero_of_mul_transpose (smul_mul_transpose_smul _ _) (by
      rw [sqrt_mul_transpose_sqrt hCPD.posSemidef, Matrix.det_smul]
      exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hLr.ne')) hCPD.det_pos.ne')
  have hC0 : 0 < lawConst P K := div_pos (rhoSum_pos (by simp) hMCd 0)
    (mul_pos (rhoSum_pos (by simp) (det_smul_one_ne_zero hLr) 0)
      (pow_pos (rhoSum_pos (by simp) (det_smul_one_ne_zero hr0) 0) 2))
  set K₀ := lawConst P K * Z with hK₀def
  have hQs : ∀ z₁ z₂, (K.gaussianQe P c {latticePoint K z₁ z₂}).toReal =
      rho MS (Fin.append (c 0) (c 1)) (K.basisMat *ᵥ ofInt (Fin.append z₁ z₂)) / Z := by
    intro z₁ z₂
    rw [hQe, latticeGaussian_singleton P K hq hN, ENNReal.toReal_ofReal]
    exact div_nonneg (Real.exp_pos _).le (rhoSum_pos hB hMSd _).le
  have hQ0 : ∀ y, (¬∃ p : (Fin n → ℤ) × (Fin n → ℤ), latticePoint K p.1 p.2 = y) →
      K.gaussianQe P c {y} = 0 := fun y hy => by
    rw [hQe]
    exact latticeGaussian_singleton_eq_zero K MS c hy
  have hP0 : ∀ y, (¬∃ p : (Fin n → ℤ) × (Fin n → ℤ), latticePoint K p.1 p.2 = y) →
      𝒟[simulateQ implE (sample P K c)] {y} = 0 := by
    intro y hy
    refine le_antisymm (not_lt.1 fun hpos => hy ?_) zero_le
    obtain ⟨z₁, z₂, h⟩ := (evalDist_sample_pos_iff P K c hr0 hL0 implE hE y).1 hpos
    exact ⟨(z₁, z₂), h⟩
  have hinj := latticePoint_injective P K hq hN
  set w : (Fin 2 → Fin n → ℤ) → ℝ := fun y =>
    if y ∈ Set.range (fun p : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint K p.1 p.2) then
      (∑' x, coordTerm P K c
          (Function.invFun (fun p : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint K p.1 p.2) y).1
          (Function.invFun (fun p : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint K p.1 p.2) y).2 x) /
        (K₀ * (K.gaussianQe P c {y}).toReal)
    else 1 with hwdef
  have hρ : ∀ z₁ z₂ : Fin n → ℤ, 0 < rho MS (Fin.append (c 0) (c 1))
      (K.basisMat *ᵥ ofInt (Fin.append z₁ z₂)) := fun _ _ => Real.exp_pos _
  have hK₀Q : ∀ z₁ z₂, K₀ * (K.gaussianQe P c {latticePoint K z₁ z₂}).toReal =
      lawConst P K * rho MS (Fin.append (c 0) (c 1)) (K.basisMat *ᵥ ofInt (Fin.append z₁ z₂)) := by
    intro z₁ z₂
    rw [hQs, hK₀def]
    field_simp
  have hwp : ∀ p : (Fin n → ℤ) × (Fin n → ℤ), w (latticePoint K p.1 p.2) =
      (∑' x, coordTerm P K c p.1 p.2 x) /
        (lawConst P K *
          rho MS (Fin.append (c 0) (c 1)) (K.basisMat *ᵥ ofInt (Fin.append p.1 p.2))) := by
    intro p
    have hmem : latticePoint K p.1 p.2 ∈
        Set.range (fun p : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint K p.1 p.2) := ⟨p, rfl⟩
    simp only [hwdef, hmem, ↓reduceIte, Function.leftInverse_invFun hinj p, hK₀Q]
  have hw : ∀ y, w y ∈ Set.Icc (kappa ϵ)⁻¹ (kappa ϵ ^ 2) := by
    intro y
    by_cases h : y ∈ Set.range (fun p : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint K p.1 p.2)
    · obtain ⟨p, rfl⟩ := h
      rw [hwp]
      obtain ⟨h1, h2⟩ := tsum_coordTerm_mem hn P K u A hq hK hN hu hr hC hAc hs hϵ₀ hϵ₁ h3r h3L c
        p.1 p.2
      have hpos := mul_pos hC0 (hρ p.1 p.2)
      constructor
      · rw [le_div_iff₀ hpos]
        exact h1
      · rw [div_le_iff₀ hpos]
        exact h2
    · simp only [hwdef, h, ↓reduceIte]
      exact ⟨inv_le_one_of_one_le₀ hκ1, one_le_pow₀ hκ1⟩
  have hsing : ∀ y, 𝒟[simulateQ implE (sample P K c)] {y} =
      ENNReal.ofReal (K₀ * w y * (K.gaussianQe P c {y}).toReal) := by
    intro y
    by_cases h : y ∈ Set.range (fun p : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint K p.1 p.2)
    · obtain ⟨p, rfl⟩ := h
      rw [hwp, evalDist_sample_latticePoint P K c hq hN hr0 hL0 implE hE, mul_comm K₀,
        mul_assoc, hK₀Q]
      have hρne := (hρ p.1 p.2).ne'
      have hC0ne := hC0.ne'
      congr 1
      field_simp
    · have h' : ¬∃ p : (Fin n → ℤ) × (Fin n → ℤ), latticePoint K p.1 p.2 = y := h
      rw [hP0 y h', hQ0 y h', ENNReal.toReal_zero, mul_zero, ENNReal.ofReal_zero]
  exact ⟨w, hw, eq_withDensity_of_singleton _ _ (mul_pos hC0 hZ)
    (fun y => (inv_pos.2 hκ0).le.trans (hw y).1) (fun y => (hw y).2) hsing⟩

/-- **Lemma 4** [ZKLY26, p. 7, l. 237; p. 19, l. 610-612]: `log R_v(𝒫‖𝒬_e) ≤ (9v/8)(log κ)²` for
every `v > 1`. Assumed, not proved: `Key.GSCoeff u`, the key-expansion facts `Key.UClose`,
`Key.CholeskyRoot`, `Key.AClose` (`hu`, `hr`, `hC`, `hAc`) and perfect integer samplers (`hE`). -/
theorem renyiDiv_sample_gaussianQe_le {ℓ : ℕ} (hn : n = 2 ^ ℓ) (P : Params) (K : Key n)
    (u : Fin n → ℝ) (A : Fin 2 → Fin 2 → Fin n → ℝ) (hq : 0 < P.q) (hK : K.Annular P)
    (hN : K.NTRU P) (hu : K.GSCoeff u) (hr : K.UClose P u) (hC : K.CholeskyRoot P A)
    (hAc : K.AClose P A) (hs : beta P n < P.s) {ϵ : ℝ} (hϵ₀ : 0 < ϵ) (hϵ₁ : ϵ < 1)
    (h3r : smoothingParam ϵ (1 : Matrix (Fin n) (Fin n) ℝ) ≤ P.r)
    (h3L : beta P n * P.s * √(1 + tauBar P n) / (P.q * P.r) *
      smoothingParam ϵ (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ) ≤ P.L)
    (c : Fin 2 → Fin n → ℝ) (implE : QueryImpl samplerSpec m)
    (hE : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implE t) = answer P id t)
    {v : ℝ} (hv : 1 < v) :
    renyiDiv v 𝒟[simulateQ implE (sample P K c)] (K.gaussianQe P c) ≤
      ENNReal.ofReal (Real.exp (9 * v / 8 * Real.log (kappa ϵ) ^ 2)) := by
  obtain ⟨hr0, -⟩ := r_pos_and_L_pos hn P K hq hK hs hϵ₀ h3r h3L
  obtain ⟨w, hw, heq⟩ := exists_evalDist_sample_eq_withDensity hn P K u A hq hK hN hu hr hC hAc
    hs hϵ₀ hϵ₁ h3r h3L c implE hE
  have := isProbabilityMeasure_gaussianQe P K hq hN hr0 c
  rw [heq]
  exact BoundedRatio.renyiDiv_withDensity_le _ Measurable.of_discrete.aemeasurable
    (one_le_kappa hϵ₀.le hϵ₁) (Filter.Eventually.of_forall hw) hv

end Key

end Mitaka
