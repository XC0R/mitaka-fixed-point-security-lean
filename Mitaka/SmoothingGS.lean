/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mitaka.Smoothing

/-! # The smoothing parameter from the Gram–Schmidt profile ([Jia+26, Theorem 3])

[Jia+26] (Jia, Zhang, Yu, Tang, ePrint 2026/096), Theorem 3 (p. 13): "Let `B ∈ ℤ^{m×m}` be a
basis of the lattice `Λ` and `α_i = ‖B‖_GS/‖b̃_i‖`. Let `s = ‖B‖_GS · √(ln(2m(1 + 1/ϵ))/π)`, then
`ρ_{1/s}(Λ* \ 0) ≤ Σ_{i} 2 (ϵ/(2m(1+ϵ)))^{α_i²} / (1 − Σ_{i} 2 (ϵ/(2m(1+ϵ)))^{α_i²})`. Defining the
right side of the inequality as `ϵ′`, then `η_{ϵ′}(Λ) ≤ ‖B‖_GS · √(ln(2m(1 + 1/ϵ))/π)`."

Here `B` is any invertible real matrix, `b̃_i = gs B i` are the Gram–Schmidt vectors of its
columns in the order `0, …, m − 1`, and `‖B‖_GS` is replaced by any `G ≥ max_i ‖b̃_i‖`
(`α_i = G/‖b̃_i‖`); at `G = max_i ‖b̃_i‖` this is the theorem as stated. The hypothesis
`profileSum B G ϵ < 1`, implicit in [Jia+26], makes `ϵ′` positive and finite.

The proof: for `0 ≠ w ∈ L(B)*` let `k` be the least index with `⟨w, b_k⟩ ≠ 0`; then
`⟨w, b̃_k⟩ = ⟨w, b_k⟩ ∈ ℤ \ 0` (`exists_one_le_abs_dotProduct_gs`), so
`|⟨w, b̃_k/‖b̃_k‖⟩| ≥ 1/‖b̃_k‖`; and the slab bound `tsum_slab_le` (the form of [Ban95, Lemma 2.4]
used on [Jia+26, p. 13]) gives `ρ_{1/s}(L(B)* \ 0) ≤ Σ_i 2 e^{−πs²/‖b̃_i‖²} ρ_{1/s}(L(B)*)`. The
printed proof (p. 13) uses the same two-sided slabs `|⟨x, b̃*_i/‖b̃*_i‖⟩| ≥ ‖b̃*_i‖` with the dual
Gram–Schmidt parallelepiped, which the least-index argument replaces; its one gap is that `S < 1`
is used but not stated. [Jia+26, Lemma 8] (p. 22) restates [Ban95, Lemma 2.4] with `‖x‖∞ ≥ t`
and is false as printed; no proof in [Jia+26] cites it by number (Lemma 9 and Theorem 3 use
[Ban95, Lemma 2.4] directly, in the slab form), and nothing here depends on it.

* `smoothingParam_le_profile`: [Jia+26, Theorem 3].
* `smoothingParam_le_of_norm_gs_le`: `η_ϵ(L(B)) ≤ G √(ln(2m(1 + 1/ϵ))/π)` when every
  `‖b̃_i‖ ≤ G` (all `α_i ≥ 1`; the bound `η_ϵ(L(B)) ≤ ‖B‖_GS η_ϵ(ℤ^m)` of [GPV08] with
  [Pei10, Lemma 2.5]). -/

@[expose] public section

open Real
open scoped Matrix

namespace Mitaka.LatticeGaussian

variable {m : ℕ}

/-- The column `b_j` of `B` as a vector of `EuclideanSpace ℝ (Fin m)`, i.e.
`WithLp.toLp 2 (Bᵀ j)`. -/
noncomputable abbrev col (B : Matrix (Fin m) (Fin m) ℝ) (j : Fin m) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun i => B i j

/-- The Gram–Schmidt vectors `b̃_j` of the columns of `B`. -/
noncomputable def gs (B : Matrix (Fin m) (Fin m) ℝ) : Fin m → EuclideanSpace ℝ (Fin m) :=
  InnerProductSpace.gramSchmidt ℝ (col B)

/-- `b̃_j ≠ 0` for invertible `B`. -/
theorem gs_ne_zero {B : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0) (j : Fin m) : gs B j ≠ 0 :=
  InnerProductSpace.gramSchmidt_ne_zero j ((Matrix.linearIndependent_cols_of_det_ne_zero hB).map'
    (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).symm.toLinearMap (LinearEquiv.ker _))

/-- `b_i − b̃_i` lies in the span of the earlier columns. -/
theorem col_sub_gs_mem_span (B : Matrix (Fin m) (Fin m) ℝ) (i : Fin m) :
    col B i - gs B i ∈ Submodule.span ℝ (col B '' Set.Iio i) := by
  rw [← InnerProductSpace.span_gramSchmidt_Iio ℝ (col B) i, gs,
    sub_eq_of_eq_add' (InnerProductSpace.gramSchmidt_def'' ℝ (col B) i)]
  exact Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨j, Finset.mem_Iio.1 hj, rfl⟩)

private theorem inner_eq_zero_of_mem_span {S : Set (EuclideanSpace ℝ (Fin m))}
    {w : EuclideanSpace ℝ (Fin m)} (h : ∀ v ∈ S, inner ℝ w v = 0) {v : EuclideanSpace ℝ (Fin m)}
    (hv : v ∈ Submodule.span ℝ S) : inner ℝ w v = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact inner_zero_right _
  | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
  | smul a x _ hx => rw [real_inner_smul_right, hx, mul_zero]

/-- `‖b̃_i‖ ≤ ‖b_i − v‖` for every `v` in the span of the earlier columns. -/
theorem norm_gs_le_norm_sub (B : Matrix (Fin m) (Fin m) ℝ) (i : Fin m)
    {v : EuclideanSpace ℝ (Fin m)} (hv : v ∈ Submodule.span ℝ (col B '' Set.Iio i)) :
    ‖gs B i‖ ≤ ‖col B i - v‖ := by
  have hr : col B i - gs B i - v ∈ Submodule.span ℝ (col B '' Set.Iio i) :=
    Submodule.sub_mem _ (col_sub_gs_mem_span B i) hv
  rw [← InnerProductSpace.span_gramSchmidt_Iio ℝ (col B) i] at hr
  have h0 : inner ℝ (gs B i) (col B i - gs B i - v) = 0 := by
    refine inner_eq_zero_of_mem_span (fun x hx => ?_) hr
    obtain ⟨j, hj, rfl⟩ := hx
    exact InnerProductSpace.gramSchmidt_orthogonal ℝ (col B) (ne_of_gt hj)
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_real h0
  rw [show gs B i + (col B i - gs B i - v) = col B i - v by abel] at h
  have h2 := mul_self_nonneg ‖col B i - gs B i - v‖
  exact le_of_sq_le_sq (by linarith) (norm_nonneg _)

/-- **Slab bound** ([Ban95, Lemma 2.4], in the form used on [Jia+26, p. 13], with `≤`): for a unit
vector `u`, `t ≥ 0`, `s > 0` and any shift `c`,
`Σ_{x ∈ L(D) + c, |⟨x, u⟩| ≥ t} ρ_{1/s}(x) ≤ 2 e^{−πs²t²} ρ_{1/s}(L(D))`. -/
theorem tsum_slab_le {D : Matrix (Fin m) (Fin m) ℝ} (hD : D.det ≠ 0) {u : Fin m → ℝ}
    (hu : sqNorm u = 1) {s t : ℝ} (hs : 0 < s) (ht : 0 ≤ t) (c : Fin m → ℝ) :
    ∑' y : {y : Fin m → ℤ // t ≤ |(D *ᵥ ofInt y + c) ⬝ᵥ u|},
        rho (s⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)) 0 (D *ᵥ ofInt y.1 + c) ≤
      2 * Real.exp (-π * s ^ 2 * t ^ 2) * rhoSum D (s⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)) 0 := by
  have hM := det_inv_smul_one_ne_zero (m := m) hs.ne'
  have hr : ∀ (a x : Fin m → ℝ), rho (s⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)) a x =
      Real.exp (-π * s ^ 2 * sqNorm (x - a)) := fun a x => by
    rw [rho_smul_one (inv_ne_zero hs.ne')]
    congr 1
    field_simp
  have hsq : ∀ (x : Fin m → ℝ) (a : ℝ), sqNorm (x - a • u) =
      sqNorm x - 2 * a * (x ⬝ᵥ u) + a ^ 2 := fun x a => by
    simp only [sqNorm, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, dotProduct_comm u x]
    rw [show u ⬝ᵥ u = 1 from hu]
    ring
  set e := Real.exp (-π * s ^ 2 * t ^ 2)
  set F : (Fin m → ℤ) → ℝ := fun y => Real.exp (-π * s ^ 2 * sqNorm (D *ᵥ ofInt y + c))
  set g : (Fin m → ℤ) → ℝ := fun y =>
    e * (rho (s⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)) (t • u - c) (D *ᵥ ofInt y) +
      rho (s⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)) (-(t • u) - c) (D *ᵥ ofInt y))
  have hgs : Summable g :=
    ((summable_rho hD hM _).add (summable_rho hD hM _)).mul_left e
  have hle : ∀ y, ({y | t ≤ |(D *ᵥ ofInt y + c) ⬝ᵥ u|} : Set (Fin m → ℤ)).indicator F y ≤ g y := by
    intro y
    have he : 0 ≤ e := (Real.exp_pos _).le
    have h1 := (Real.exp_pos (-π * s ^ 2 * sqNorm (D *ᵥ ofInt y - (t • u - c)))).le
    have h2 := (Real.exp_pos (-π * s ^ 2 * sqNorm (D *ᵥ ofInt y - (-(t • u) - c)))).le
    simp only [g, hr]
    by_cases hy : t ≤ |(D *ᵥ ofInt y + c) ⬝ᵥ u|
    · rw [Set.indicator_of_mem hy]
      set x := D *ᵥ ofInt y + c
      have hx1 : D *ᵥ ofInt y - (t • u - c) = x - t • u := by simp only [x]; abel
      have hx2 : D *ᵥ ofInt y - (-(t • u) - c) = x - (-t) • u := by simp only [x, neg_smul]; abel
      rw [hx1, hx2, hsq, hsq]
      have hpi := Real.pi_pos
      have hs2 := sq_nonneg s
      rcases le_abs'.1 hy with hneg | hpos
      · have hk : -π * s ^ 2 * sqNorm x ≤ -π * s ^ 2 * t ^ 2 +
            -π * s ^ 2 * (sqNorm x - 2 * -t * (x ⬝ᵥ u) + (-t) ^ 2) := by
          have := mul_nonneg (mul_nonneg (mul_nonneg hpi.le hs2) ht)
            (by linarith : 0 ≤ -(x ⬝ᵥ u) - t)
          linarith
        have := Real.exp_le_exp.2 hk
        rw [Real.exp_add] at this
        simp only [F]
        nlinarith [Real.exp_pos (-π * s ^ 2 * (sqNorm x - 2 * t * (x ⬝ᵥ u) + t ^ 2))]
      · have hk : -π * s ^ 2 * sqNorm x ≤ -π * s ^ 2 * t ^ 2 +
            -π * s ^ 2 * (sqNorm x - 2 * t * (x ⬝ᵥ u) + t ^ 2) := by
          have := mul_nonneg (mul_nonneg (mul_nonneg hpi.le hs2) ht)
            (by linarith : 0 ≤ x ⬝ᵥ u - t)
          linarith
        have := Real.exp_le_exp.2 hk
        rw [Real.exp_add] at this
        simp only [F]
        nlinarith [Real.exp_pos (-π * s ^ 2 * (sqNorm x - 2 * -t * (x ⬝ᵥ u) + (-t) ^ 2))]
    · rw [Set.indicator_of_notMem hy]
      positivity
  have hF : ∀ y : Fin m → ℤ, rho (s⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)) 0 (D *ᵥ ofInt y + c) =
      F y := fun y => by rw [hr, sub_zero]
  calc ∑' y : {y : Fin m → ℤ // t ≤ |(D *ᵥ ofInt y + c) ⬝ᵥ u|},
        rho (s⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)) 0 (D *ᵥ ofInt y.1 + c)
      = ∑' y, ({y | t ≤ |(D *ᵥ ofInt y + c) ⬝ᵥ u|} : Set (Fin m → ℤ)).indicator F y := by
        simp only [hF]
        exact tsum_subtype ({y | t ≤ |(D *ᵥ ofInt y + c) ⬝ᵥ u|} : Set (Fin m → ℤ)) F
    _ ≤ ∑' y, g y := Summable.tsum_le_tsum hle
        (Summable.of_nonneg_of_le (fun y => Set.indicator_nonneg
          (fun y _ => (Real.exp_pos _).le) y) hle hgs) hgs
    _ = e * (rhoSum D (s⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)) (t • u - c) +
          rhoSum D (s⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)) (-(t • u) - c)) := by
        rw [tsum_mul_left, Summable.tsum_add (summable_rho hD hM _) (summable_rho hD hM _)]
        rfl
    _ ≤ e * (rhoSum D (s⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)) 0 +
          rhoSum D (s⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)) 0) :=
        mul_le_mul_of_nonneg_left (add_le_add (rhoSum_le_rhoSum_zero hD hM _)
          (rhoSum_le_rhoSum_zero hD hM _)) (Real.exp_pos _).le
    _ = 2 * e * rhoSum D (s⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)) 0 := by ring

private theorem rhoSum_fin_zero (D M : Matrix (Fin 0) (Fin 0) ℝ) (c : Fin 0 → ℝ) :
    rhoSum D M c = 1 := by
  rw [rhoSum, tsum_eq_single 0 fun b hb => absurd (Subsingleton.elim b 0) hb]
  simp [rho, sqNorm]

private theorem smoothingParam_fin_zero {ϵ : ℝ} (hϵ : 0 ≤ ϵ) (B : Matrix (Fin 0) (Fin 0) ℝ) :
    smoothingParam ϵ B = 0 := by
  have h : {s : ℝ | 0 < s ∧
      rhoSum (dualBasis B) (s⁻¹ • (1 : Matrix (Fin 0) (Fin 0) ℝ)) 0 ≤ 1 + ϵ} = Set.Ioi 0 := by
    ext s
    simp [rhoSum_fin_zero, hϵ]
  rw [smoothingParam, h, csInf_Ioi]

/-- A non-zero vector of `L(B)*` has `|⟨w, b̃_k⟩| ≥ 1` for some `k` ([Jia+26, Theorem 3], proof). -/
theorem exists_one_le_abs_dotProduct_gs {B : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0)
    {y : Fin m → ℤ} (hy : y ≠ 0) :
    ∃ k, 1 ≤ |(dualBasis B *ᵥ ofInt y) ⬝ᵥ WithLp.ofLp (gs B k)| := by
  set w := dualBasis B *ᵥ ofInt y
  have hcol : ∀ j, w ⬝ᵥ WithLp.ofLp (col B j) = y j := by
    intro j
    have h1 : Bᵀ *ᵥ w = ofInt y := by
      rw [Matrix.mulVec_mulVec, dualBasis, ← Matrix.transpose_mul,
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hB), Matrix.transpose_one,
        Matrix.one_mulVec]
    have h2 := congrFun h1 j
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, ofInt] at h2
    simp only [dotProduct]
    rw [← h2]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hinner : ∀ v : EuclideanSpace ℝ (Fin m),
      inner ℝ (WithLp.toLp 2 w) v = w ⬝ᵥ WithLp.ofLp v := fun v => by
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]
  have hne : (Finset.univ.filter fun j => y j ≠ 0).Nonempty := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
    exact ⟨j, by simpa using hj⟩
  set k := (Finset.univ.filter fun j => y j ≠ 0).min' hne
  have hk : y k ≠ 0 := by simpa using Finset.min'_mem _ hne
  have hmin : ∀ j < k, y j = 0 := fun j hj => by
    by_contra h
    exact absurd (Finset.min'_le _ j (by simpa using h)) (not_le.2 hj)
  refine ⟨k, ?_⟩
  have hzero : inner ℝ (WithLp.toLp 2 w) (col B k - gs B k) = 0 :=
    inner_eq_zero_of_mem_span (fun v hv => by
      obtain ⟨j, hj, rfl⟩ := hv
      rw [hinner, hcol, hmin j hj, Int.cast_zero]) (col_sub_gs_mem_span B k)
  rw [hinner, WithLp.ofLp_sub, dotProduct_sub, hcol, sub_eq_zero] at hzero
  rw [← hzero, ← Int.cast_abs]
  exact_mod_cast Int.one_le_abs hk

/-- The profile sum `Σ_i 2 (ϵ/(2m(1 + ϵ)))^{α_i²}`, `α_i = G/‖b̃_i‖`, of [Jia+26, Theorem 3]. -/
noncomputable def profileSum (B : Matrix (Fin m) (Fin m) ℝ) (G ϵ : ℝ) : ℝ :=
  ∑ i, 2 * (ϵ / (2 * m * (1 + ϵ))) ^ ((G / ‖gs B i‖) ^ 2)

/-- [Jia+26, Theorem 3], first claim: `ρ_{1/s}(L(B)*) ≤ 1 + ϵ′` with `ϵ′ = S/(1 − S)`,
`S = profileSum B G ϵ`, `s = G √(ln(2m(1 + 1/ϵ))/π)`. -/
theorem rhoSum_dualBasis_le_profile {B : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0) {G ϵ : ℝ}
    (hϵ : 0 < ϵ) (hG : ∀ i, ‖gs B i‖ ≤ G) (hS : profileSum B G ϵ < 1) :
    rhoSum (dualBasis B)
        ((G * √(Real.log (2 * m * (1 + 1 / ϵ)) / π))⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)) 0 ≤
      1 + profileSum B G ϵ / (1 - profileSum B G ϵ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [rhoSum_fin_zero]
    simp [profileSum]
  have hD := det_dualBasis_ne_zero hB
  have hgpos : ∀ i, 0 < ‖gs B i‖ := fun i => norm_pos_iff.2 (gs_ne_zero hB i)
  have hG0 : 0 < G := (hgpos ⟨0, hm⟩).trans_le (hG _)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hA : 1 < 2 * (m : ℝ) * (1 + 1 / ϵ) := by
    have : 0 < 1 / ϵ := by positivity
    linarith [mul_pos (by linarith : (0 : ℝ) < m) this]
  have hL0 := Real.log_pos hA
  have hs0 : 0 < G * √(Real.log (2 * m * (1 + 1 / ϵ)) / π) :=
    mul_pos hG0 (Real.sqrt_pos.2 (div_pos hL0 Real.pi_pos))
  set s := G * √(Real.log (2 * m * (1 + 1 / ϵ)) / π) with hs
  have hs2 : s ^ 2 = G ^ 2 * Real.log (2 * m * (1 + 1 / ϵ)) / π := by
    rw [hs, mul_pow, Real.sq_sqrt (div_pos hL0 Real.pi_pos).le]
    ring
  have hx0 : 0 < ϵ / (2 * m * (1 + ϵ)) := by positivity
  have hterm : ∀ k, Real.exp (-π * s ^ 2 * ‖gs B k‖⁻¹ ^ 2) =
      (ϵ / (2 * m * (1 + ϵ))) ^ ((G / ‖gs B k‖) ^ 2) := fun k => by
    have hx : ϵ / (2 * m * (1 + ϵ)) = (2 * m * (1 + 1 / ϵ))⁻¹ := by
      field_simp
      ring
    rw [Real.rpow_def_of_pos hx0, hx, Real.log_inv, hs2]
    congr 1
    have := (hgpos k).ne'
    field_simp
  set u : Fin m → Fin m → ℝ := fun k => ‖gs B k‖⁻¹ • WithLp.ofLp (gs B k)
  have hu : ∀ k, sqNorm (u k) = 1 := fun k => by
    have h := real_inner_self_eq_norm_sq (gs B k)
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at h
    simp only [u, sqNorm, smul_dotProduct, dotProduct_smul, smul_eq_mul, h]
    have := (hgpos k).ne'
    field_simp
  set f : (Fin m → ℤ) → ℝ := fun y => Real.exp (-π * s ^ 2 * sqNorm (dualBasis B *ᵥ ofInt y))
  have hf0 : ∀ y, 0 ≤ f y := fun y => (Real.exp_pos _).le
  have hfS : Summable f := summable_exp_sqNorm hD hs0.ne'
  set T : Fin m → Set (Fin m → ℤ) := fun k =>
    {y | ‖gs B k‖⁻¹ ≤ |(dualBasis B *ᵥ ofInt y + 0) ⬝ᵥ u k|}
  have hind : ∀ k, Summable ((T k).indicator f) := fun k =>
    Summable.of_nonneg_of_le (fun y => Set.indicator_nonneg (fun y _ => hf0 y) y)
      (fun y => Set.indicator_le_self' (fun y _ => hf0 y) y) hfS
  have hslab : ∀ k, ∑' y, (T k).indicator f y ≤
      2 * (ϵ / (2 * m * (1 + ϵ))) ^ ((G / ‖gs B k‖) ^ 2) * ∑' y, f y := fun k => by
    rw [← tsum_subtype (T k) f, ← hterm, ← rhoSum_inv_smul_one hs0.ne']
    change ∑' y : {y : Fin m → ℤ // ‖gs B k‖⁻¹ ≤ |(dualBasis B *ᵥ ofInt y + 0) ⬝ᵥ u k|}, f y ≤ _
    refine le_of_eq_of_le (tsum_congr fun y => ?_)
      (tsum_slab_le hD (hu k) hs0 (inv_nonneg.2 (norm_nonneg _)) 0)
    rw [add_zero, rho_inv_smul_one hs0.ne']
  have hpt : ∀ y, (if y = 0 then 0 else f y) ≤ ∑ k, (T k).indicator f y := fun y => by
    by_cases hy : y = 0
    · simp only [hy, ↓reduceIte]
      exact Finset.sum_nonneg fun k _ => Set.indicator_nonneg (fun y _ => hf0 y) _
    · simp only [hy, ↓reduceIte]
      obtain ⟨k, hk⟩ := exists_one_le_abs_dotProduct_gs hB hy
      have hmem : y ∈ T k := by
        change ‖gs B k‖⁻¹ ≤ |(dualBasis B *ᵥ ofInt y + 0) ⬝ᵥ u k|
        rw [add_zero, dotProduct_smul, smul_eq_mul, abs_mul, abs_inv, abs_norm]
        exact le_mul_of_one_le_right (inv_nonneg.2 (norm_nonneg _)) hk
      rw [← Set.indicator_of_mem hmem f]
      exact Finset.single_le_sum (fun k _ => Set.indicator_nonneg (fun y _ => hf0 y) y)
        (Finset.mem_univ k)
  have hsumS : Summable fun y => ∑ k, (T k).indicator f y := summable_sum fun k _ => hind k
  have hite : Summable fun y => if y = 0 then 0 else f y :=
    Summable.of_nonneg_of_le (fun y => by split_ifs <;> simp [hf0]) hpt hsumS
  have hf0' : f 0 = 1 := by simp [f, ofInt_zero, sqNorm]
  have hR : ∑' y, (if y = 0 then 0 else f y) ≤ profileSum B G ϵ * ∑' y, f y := by
    refine (Summable.tsum_le_tsum hpt hite hsumS).trans ?_
    rw [Summable.tsum_finsetSum fun k _ => hind k, profileSum, Finset.sum_mul]
    exact Finset.sum_le_sum fun k _ => hslab k
  have hF : ∑' y, f y = 1 + ∑' y, (if y = 0 then 0 else f y) := by
    rw [hfS.tsum_eq_add_tsum_ite 0, hf0']
  have hmain : ∑' y, f y ≤ 1 + profileSum B G ϵ * ∑' y, f y := by linarith
  rw [rhoSum_inv_smul_one hs0.ne']
  have h1S : 0 < 1 - profileSum B G ϵ := by linarith
  rw [show 1 + profileSum B G ϵ / (1 - profileSum B G ϵ) = 1 / (1 - profileSum B G ϵ) by
    field_simp; ring, le_div_iff₀ h1S]
  linarith

/-- **[Jia+26, Theorem 3]**: `η_{ϵ′}(L(B)) ≤ G √(ln(2m(1 + 1/ϵ))/π)` with
`ϵ′ = S/(1 − S)`, `S = profileSum B G ϵ < 1`, for every `G ≥ max_i ‖b̃_i‖`. -/
theorem smoothingParam_le_profile {B : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0) {G ϵ : ℝ}
    (hϵ : 0 < ϵ) (hG : ∀ i, ‖gs B i‖ ≤ G) (hS : profileSum B G ϵ < 1) :
    smoothingParam (profileSum B G ϵ / (1 - profileSum B G ϵ)) B ≤
      G * √(Real.log (2 * m * (1 + 1 / ϵ)) / π) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [smoothingParam_fin_zero (by simp [profileSum])]
    simp
  have hgpos : ∀ i, 0 < ‖gs B i‖ := fun i => norm_pos_iff.2 (gs_ne_zero hB i)
  have hG0 : 0 < G := (hgpos ⟨0, hm⟩).trans_le (hG _)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hA : 1 < 2 * (m : ℝ) * (1 + 1 / ϵ) := by
    have : 0 < 1 / ϵ := by positivity
    linarith [mul_pos (by linarith : (0 : ℝ) < m) this]
  have hS0 : 0 < profileSum B G ϵ :=
    Finset.sum_pos (fun i _ => mul_pos two_pos (Real.rpow_pos_of_pos (by positivity) _))
      ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  exact (smoothingParam_le_iff hB (div_pos hS0 (sub_pos.2 hS))
    (mul_pos hG0 (Real.sqrt_pos.2 (div_pos (Real.log_pos hA) Real.pi_pos)))).2
    (rhoSum_dualBasis_le_profile hB hϵ hG hS)

/-- `η_ϵ(L(B)) ≤ G √(ln(2m(1 + 1/ϵ))/π)` when every Gram–Schmidt norm is at most `G`. -/
theorem smoothingParam_le_of_norm_gs_le {B : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0)
    {G ϵ : ℝ} (hϵ : 0 < ϵ) (hG : ∀ i, ‖gs B i‖ ≤ G) :
    smoothingParam ϵ B ≤ G * √(Real.log (2 * m * (1 + 1 / ϵ)) / π) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [smoothingParam_fin_zero hϵ.le]
    simp
  have hgpos : ∀ i, 0 < ‖gs B i‖ := fun i => norm_pos_iff.2 (gs_ne_zero hB i)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hx0 : 0 < ϵ / (2 * m * (1 + ϵ)) := by positivity
  have hx1 : ϵ / (2 * m * (1 + ϵ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [mul_le_mul_of_nonneg_right hm1 hϵ.le]
  have hSle : profileSum B G ϵ ≤ ϵ / (1 + ϵ) := by
    calc profileSum B G ϵ ≤ ∑ _i : Fin m, 2 * (ϵ / (2 * m * (1 + ϵ))) :=
          Finset.sum_le_sum fun i _ => by
            refine mul_le_mul_of_nonneg_left ?_ two_pos.le
            refine (Real.rpow_le_rpow_of_exponent_ge hx0 hx1 ?_).trans (Real.rpow_one _).le
            exact_mod_cast one_le_pow₀ ((one_le_div (hgpos i)).2 (hG i))
      _ = ϵ / (1 + ϵ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
  have h1 : ϵ / (1 + ϵ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hS : profileSum B G ϵ < 1 := hSle.trans_lt h1
  have hS0 : 0 < profileSum B G ϵ :=
    Finset.sum_pos (fun i _ => mul_pos two_pos (Real.rpow_pos_of_pos hx0 _))
      ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  have hle : profileSum B G ϵ / (1 - profileSum B G ϵ) ≤ ϵ := by
    rw [div_le_iff₀ (sub_pos.2 hS)]
    rw [le_div_iff₀ (by linarith)] at hSle
    linarith
  exact (smoothingParam_anti hB (div_pos hS0 (sub_pos.2 hS)) hle).trans
    (smoothingParam_le_profile hB hϵ hG hS)

end Mitaka.LatticeGaussian
