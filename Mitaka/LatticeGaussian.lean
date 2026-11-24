/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import LatticeCrypto.DiscreteGaussian
public import Mitaka.Poisson

/-! # Lattices `L(B) = Bℤ^m` and the lattice Gaussian `D_{L(B),M,c}`

[ZKLY26] (ePrint 2026/2521), §2.1 (p. 3, l. 96-102): "For a full-rank matrix `B ∈ ℝ^{n×n}`, the
lattice spanned by `B` is `L(B) = Bℤⁿ`. The dual of a lattice `L` is
`L* = {y ∈ ℝⁿ : ⟨x, y⟩ ∈ ℤ for all x ∈ L}`. Let `ρ_{M,c}(x) = exp(−π‖M⁻¹(x − c)‖₂²)` be the
Gaussian function with invertible factor `M ∈ ℝ^{n×n}` and center `c ∈ ℝⁿ`. Its scaled covariance
is `Σ = MMᵗ ≻ 0`, and `ρ_{M,c} = ρ_{√Σ,c}`. When `M = sI` for `s > 0`, we write the subscript `M`
as `s`, and call `s` the Gaussian width. […] Let `ρ_{M,c}(S) = Σ_{x∈S} ρ_{M,c}(x)` for any
countable set `S`. The discrete Gaussian over a lattice `L` is `D_{L,M,c}(x) =
ρ_{M,c}(x)/ρ_{M,c}(L)` for `x ∈ L`."

A lattice is given by an invertible basis `B` (hypothesis `B.det ≠ 0`) and its points are
`B z`, `z ∈ ℤ^m`; `points B` is the set `L(B)`, `dual` is the paper's dual of a set, and
`points_dualBasis` identifies `L(B)*` with `L((B⁻¹)ᵗ)`. Norms are Euclidean (`sqNorm`). The width
`s` of the paper is `σ√(2π)` for the standard deviation `σ` of VCVio's
`discreteGaussianMeasure` (`gaussianPMF_one_smul`).

* `rhoSum B M c = ρ_{M,c}(L(B))`, summed over the coordinates `z ∈ ℤ^m`; `rhoSum_eq_tsum_points`:
  it is the sum over the set `L(B)`.
* `gaussianMeasure B M c`: the law of the coordinates `z` of `x = Bz ∼ D_{L(B),M,c}`, a
  probability measure on `ℤ^m` (`isProbabilityMeasure_gaussianMeasure`), as VCVio's
  `discreteGaussianMeasure` on `ℤ`.
* `gaussian B M c`: `D_{L(B),M,c}` on `ℝ^m`; `gaussian_singleton` gives
  `D_{L(B),M,c}(x) = ρ_{M,c}(x)/ρ_{M,c}(L(B))` for `x ∈ L(B)`, `gaussian_compl_points` support
  in `L(B)`.
* `gaussianPMF_one_smul`: `D_{ℤ^m,s,c}` is the product of the one-dimensional
  `discreteGaussianPMF (s/√(2π)) (c i)`, the laws of the integer-sampler queries of
  `Mitaka.answer`. -/

@[expose] public section

open Real MeasureTheory LatticeCrypto
open scoped Matrix

namespace Mitaka.LatticeGaussian

variable {m : ℕ}

/-- The squared Euclidean norm `‖x‖² = Σᵢ xᵢ²`. -/
def sqNorm (x : Fin m → ℝ) : ℝ := x ⬝ᵥ x

/-- `‖x‖² ≥ 0`. -/
theorem sqNorm_nonneg (x : Fin m → ℝ) : 0 ≤ sqNorm x := by
  unfold sqNorm dotProduct
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

/-- `‖a x‖² = a² ‖x‖²`. -/
theorem sqNorm_smul (a : ℝ) (x : Fin m → ℝ) : sqNorm (a • x) = a ^ 2 * sqNorm x := by
  simp only [sqNorm, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/-- `‖N x‖² = xᵗ (NᵗN) x`. -/
theorem quadForm_transpose_mul_self (N : Matrix (Fin m) (Fin m) ℝ) (x : Fin m → ℝ) :
    quadForm (Nᵀ * N) x = sqNorm (N *ᵥ x) := by
  rw [quadForm, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, sqNorm]

/-- `ρ_{M,c}(x) = exp(−π‖M⁻¹(x − c)‖²)` [ZKLY26, p. 3, l. 98]. -/
noncomputable def rho (M : Matrix (Fin m) (Fin m) ℝ) (c x : Fin m → ℝ) : ℝ :=
  Real.exp (-π * sqNorm (M⁻¹ *ᵥ (x - c)))

/-- `ρ_{sI,c}(x) = exp(−π‖x − c‖²/s²)` [ZKLY26, p. 3, l. 100]. -/
theorem rho_smul_one {s : ℝ} (hs : s ≠ 0) (c x : Fin m → ℝ) :
    rho (s • (1 : Matrix (Fin m) (Fin m) ℝ)) c x = Real.exp (-π * sqNorm (x - c) / s ^ 2) := by
  have h := Matrix.inv_smul' (Units.mk0 s hs) (A := (1 : Matrix (Fin m) (Fin m) ℝ)) (by simp)
  simp only [Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, inv_one] at h
  rw [rho, h, Matrix.smul_mulVec, Matrix.one_mulVec, sqNorm_smul]
  congr 1
  field_simp

/-- `ρ_{M,c}(x) = exp(−π (x − c)ᵗ (MMᵗ)⁻¹ (x − c))`. -/
theorem rho_eq_exp_quadForm (M : Matrix (Fin m) (Fin m) ℝ) (c x : Fin m → ℝ) :
    rho M c x = Real.exp (-π * quadForm (M * Mᵀ)⁻¹ (x - c)) := by
  rw [rho, Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv, quadForm_transpose_mul_self]

/-- `ρ_{M,c} = ρ_{√Σ,c}`: `ρ_{M,c}` depends on `M` only through `Σ = MMᵗ`
[ZKLY26, p. 3, l. 99]. -/
theorem rho_congr {M N : Matrix (Fin m) (Fin m) ℝ} (h : M * Mᵀ = N * Nᵀ) (c : Fin m → ℝ) :
    rho M c = rho N c := by
  funext x
  rw [rho_eq_exp_quadForm, rho_eq_exp_quadForm, h]

/-- `ofInt 0 = 0`. -/
theorem ofInt_zero : ofInt (0 : Fin m → ℤ) = 0 := by
  ext i
  simp [ofInt]

/-- `‖x‖² > 0` for `x ≠ 0`. -/
theorem sqNorm_pos {x : Fin m → ℝ} (hx : x ≠ 0) : 0 < sqNorm x :=
  lt_of_le_of_ne (sqNorm_nonneg x) (Ne.symm fun h => hx (dotProduct_self_eq_zero.1 h))

/-- The lattice `L(B) = Bℤ^m` [ZKLY26, p. 3, l. 96]. -/
def points (B : Matrix (Fin m) (Fin m) ℝ) : Set (Fin m → ℝ) :=
  Set.range fun z : Fin m → ℤ => B *ᵥ ofInt z

/-- The dual `S* = {y : ⟨x, y⟩ ∈ ℤ for all x ∈ S}` [ZKLY26, p. 3, l. 96-97]. -/
def dual (S : Set (Fin m → ℝ)) : Set (Fin m → ℝ) := {y | ∀ x ∈ S, ∃ k : ℤ, x ⬝ᵥ y = k}

/-- The dual basis `(B⁻¹)ᵗ`. -/
noncomputable def dualBasis (B : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ := (B⁻¹)ᵀ

/-- `z ↦ Bz` is injective on `ℤ^m` for invertible `B`. -/
theorem injective_mulVec_ofInt {B : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0) :
    Function.Injective fun z : Fin m → ℤ => B *ᵥ ofInt z := by
  intro z z' h
  have h' := Matrix.mulVec_injective_iff_isUnit.2
    ((Matrix.isUnit_iff_isUnit_det B).2 (isUnit_iff_ne_zero.2 hB)) h
  funext i
  have hi := congrFun h' i
  simp only [ofInt] at hi
  exact_mod_cast hi

/-- `L(B)* = L((B⁻¹)ᵗ)`. -/
theorem points_dualBasis {B : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0) :
    points (dualBasis B) = dual (points B) := by
  have hu : IsUnit B.det := isUnit_iff_ne_zero.2 hB
  ext y
  constructor
  · rintro ⟨k, rfl⟩ _ ⟨z, rfl⟩
    refine ⟨∑ i, z i * k i, ?_⟩
    rw [dualBasis, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
    simp [ofInt, dotProduct]
  · intro hy
    have h := fun j : Fin m => hy _ ⟨Pi.single j 1, rfl⟩
    choose k hk using h
    refine ⟨k, ?_⟩
    have hk' : ofInt k = Bᵀ *ᵥ y := by
      funext j
      change (k j : ℝ) = _
      rw [← hk j]
      change (B *ᵥ ofInt (Pi.single j 1)) ⬝ᵥ y = _
      have : ofInt (Pi.single j 1 : Fin m → ℤ) = Pi.single j 1 := by
        ext i; simp [ofInt, Pi.single_apply]
      rw [this, Matrix.mulVec_single_one]
      rfl
    change dualBasis B *ᵥ ofInt k = y
    rw [hk', dualBasis, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hu,
      Matrix.transpose_one, Matrix.one_mulVec]

/-- `ρ_{M,c}(L(B)) = Σ_{z ∈ ℤ^m} ρ_{M,c}(Bz)` [ZKLY26, p. 3, l. 101]. -/
noncomputable def rhoSum (B M : Matrix (Fin m) (Fin m) ℝ) (c : Fin m → ℝ) : ℝ :=
  ∑' z : Fin m → ℤ, rho M c (B *ᵥ ofInt z)

/-- The weights of `ρ_{M,c}` on `L(B)` are summable. -/
theorem summable_rho {B M : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0) (hM : M.det ≠ 0)
    (c : Fin m → ℝ) : Summable fun z : Fin m → ℤ => rho M c (B *ᵥ ofInt z) := by
  have hN : (M⁻¹ * B).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact mul_ne_zero (inv_ne_zero hM) hB
  have hP : ((M⁻¹ * B)ᵀ * (M⁻¹ * B)).PosDef := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_iff_isUnit.2
      ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hN)))
  refine (summable_exp_neg_quadForm hP (B⁻¹ *ᵥ c)).congr fun z => ?_
  rw [rho, quadForm_transpose_mul_self, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
    Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hB), Matrix.mul_one,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_sub]

/-- `rhoSum B M c` is the sum of `ρ_{M,c}` over the set `L(B)`. -/
theorem rhoSum_eq_tsum_points {B M : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0)
    (c : Fin m → ℝ) : rhoSum B M c = ∑' x : points B, rho M c x :=
  (tsum_range (rho M c) (injective_mulVec_ofInt hB)).symm

/-- `ρ_{M,c}(L(B)) > 0`. -/
theorem rhoSum_pos {B M : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0) (hM : M.det ≠ 0)
    (c : Fin m → ℝ) : 0 < rhoSum B M c :=
  (summable_rho hB hM c).tsum_pos (fun _ => (Real.exp_pos _).le) 0 (Real.exp_pos _)

/-- The mass `D_{L(B),M,c}(Bz) = ρ_{M,c}(Bz)/ρ_{M,c}(L(B))` at the coordinates `z`
[ZKLY26, p. 3, l. 102]. -/
noncomputable def gaussianPMF (B M : Matrix (Fin m) (Fin m) ℝ) (c : Fin m → ℝ)
    (z : Fin m → ℤ) : ℝ :=
  rho M c (B *ᵥ ofInt z) / rhoSum B M c

/-- The law of the coordinates `z` of `Bz ∼ D_{L(B),M,c}`: the density `gaussianPMF` against the
counting measure on `ℤ^m`. -/
noncomputable def gaussianMeasure (B M : Matrix (Fin m) (Fin m) ℝ) (c : Fin m → ℝ) :
    Measure (Fin m → ℤ) :=
  Measure.count.withDensity fun z => ENNReal.ofReal (gaussianPMF B M c z)

/-- `D_{L(B),M,c}` as a measure on `ℝ^m`: the image of `gaussianMeasure B M c` under
`z ↦ Bz`. -/
noncomputable def gaussian (B M : Matrix (Fin m) (Fin m) ℝ) (c : Fin m → ℝ) :
    Measure (Fin m → ℝ) :=
  (gaussianMeasure B M c).map fun z => B *ᵥ ofInt z

/-- The mass of `gaussianMeasure` at `z` is `gaussianPMF`. -/
theorem gaussianMeasure_singleton (B M : Matrix (Fin m) (Fin m) ℝ) (c : Fin m → ℝ)
    (z : Fin m → ℤ) : gaussianMeasure B M c {z} = ENNReal.ofReal (gaussianPMF B M c z) := by
  rw [gaussianMeasure, withDensity_apply _ (measurableSet_singleton z), Measure.restrict_singleton,
    Measure.count_singleton, one_smul, lintegral_dirac]

/-- The coordinate law of `D_{L(B),M,c}` is a probability measure. -/
theorem isProbabilityMeasure_gaussianMeasure {B M : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0)
    (hM : M.det ≠ 0) (c : Fin m → ℝ) : IsProbabilityMeasure (gaussianMeasure B M c) := by
  have hpos := rhoSum_pos hB hM c
  have h1 : ∑' z, gaussianPMF B M c z = 1 := by
    change ∑' z, rho M c (B *ᵥ ofInt z) / rhoSum B M c = 1
    rw [tsum_div_const]
    exact div_self hpos.ne'
  have hs : Summable (gaussianPMF B M c) := (summable_rho hB hM c).div_const _
  constructor
  rw [gaussianMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_count, ← ENNReal.ofReal_tsum_of_nonneg (f := gaussianPMF B M c)
      (fun z => div_nonneg (Real.exp_pos _).le hpos.le) hs, h1, ENNReal.ofReal_one]

/-- `D_{L(B),M,c}` is a probability measure on `ℝ^m`. -/
theorem isProbabilityMeasure_gaussian {B M : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0)
    (hM : M.det ≠ 0) (c : Fin m → ℝ) : IsProbabilityMeasure (gaussian B M c) := by
  have := isProbabilityMeasure_gaussianMeasure hB hM c
  rw [gaussian]
  infer_instance

/-- `D_{L(B),M,c}(x) = ρ_{M,c}(x)/ρ_{M,c}(L(B))` for `x = Bz ∈ L(B)` [ZKLY26, p. 3, l. 102]. -/
theorem gaussian_singleton {B : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0)
    (M : Matrix (Fin m) (Fin m) ℝ) (c : Fin m → ℝ) (z : Fin m → ℤ) :
    gaussian B M c {B *ᵥ ofInt z} =
      ENNReal.ofReal (rho M c (B *ᵥ ofInt z) / rhoSum B M c) := by
  have hpre : (fun z : Fin m → ℤ => B *ᵥ ofInt z) ⁻¹' {B *ᵥ ofInt z} = {z} := by
    ext z'
    exact (injective_mulVec_ofInt hB).eq_iff
  rw [gaussian, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _), hpre,
    gaussianMeasure_singleton, gaussianPMF]

/-- `D_{L(B),M,c}` is supported on `L(B)`. -/
theorem gaussian_compl_points (B M : Matrix (Fin m) (Fin m) ℝ) (c : Fin m → ℝ) :
    gaussian B M c (points B)ᶜ = 0 := by
  rw [gaussian, points, Measure.map_apply (measurable_of_countable _)
    (Set.countable_range _).measurableSet.compl, Set.preimage_compl, Set.preimage_range,
    Set.compl_univ, measure_empty]

/-- A product of summable non-negative families over `ℤ` sums over `ℤ^m` to the product of the
sums. -/
theorem hasSum_prod_pi {f : Fin m → ℤ → ℝ} (h0 : ∀ i t, 0 ≤ f i t) (hs : ∀ i, Summable (f i)) :
    HasSum (fun z : Fin m → ℤ => ∏ i, f i (z i)) (∏ i, ∑' t, f i t) := by
  induction m with
  | zero =>
    simpa only [Finset.univ_eq_empty, Finset.prod_empty] using
      hasSum_single (f := fun _ : Fin 0 → ℤ => (1 : ℝ)) 0
      fun b hb => absurd (Subsingleton.elim b 0) hb
  | succ m ih =>
    have h := (hs 0).hasSum.mul (ih (fun i t => h0 i.succ t) fun i => hs i.succ)
      ((hs 0).mul_of_nonneg (ih (fun i t => h0 i.succ t) fun i => hs i.succ).summable
        (h0 0) fun _ => Finset.prod_nonneg fun i _ => h0 i.succ _)
    rw [Fin.prod_univ_succ]
    refine (Fin.consEquiv fun _ => ℤ).hasSum_iff.1 (h.congr_fun fun q => ?_)
    simp [Fin.prod_univ_succ]

/-- `D_{ℤ^m,s,c}` is the product of the one-dimensional discrete Gaussians of standard
deviation `s/√(2π)` (VCVio's `discreteGaussianPMF`) at the centres `cᵢ`. -/
theorem gaussianPMF_one_smul {s : ℝ} (hs : 0 < s) (c : Fin m → ℝ) (z : Fin m → ℤ) :
    gaussianPMF 1 (s • (1 : Matrix (Fin m) (Fin m) ℝ)) c z =
      ∏ i, discreteGaussianPMF (s / √(2 * π)) (c i) (z i) := by
  have hw : ∀ (i : Fin m) (t : ℤ), discreteGaussianWeight (s / √(2 * π)) (c i) t =
      Real.exp (-π * ((t : ℝ) - c i) ^ 2 / s ^ 2) := fun i t => by
    rw [discreteGaussianWeight, div_pow, Real.sq_sqrt (by positivity)]
    congr 1
    field_simp
  have hr : ∀ y : Fin m → ℤ, rho (s • (1 : Matrix (Fin m) (Fin m) ℝ)) c (1 *ᵥ ofInt y) =
      ∏ i, discreteGaussianWeight (s / √(2 * π)) (c i) (y i) := fun y => by
    rw [Matrix.one_mulVec, rho_smul_one hs.ne', sqNorm, dotProduct, Finset.mul_sum,
      Finset.sum_div, Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hw]
    simp [ofInt, sq]
  have hS : rhoSum 1 (s • (1 : Matrix (Fin m) (Fin m) ℝ)) c =
      ∏ i, discreteGaussianSum (s / √(2 * π)) (c i) := by
    rw [rhoSum, tsum_congr hr]
    exact (hasSum_prod_pi (f := fun i => discreteGaussianWeight (s / √(2 * π)) (c i))
      (fun i t => discreteGaussianWeight_nonneg _ _ _)
      fun i => discreteGaussianSum_summable _ _ (by positivity)).tsum_eq
  rw [gaussianPMF, hr, hS, ← Finset.prod_div_distrib]
  exact Finset.prod_congr rfl fun i _ => rfl

end Mitaka.LatticeGaussian
