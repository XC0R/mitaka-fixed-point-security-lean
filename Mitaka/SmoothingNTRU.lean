/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import Mathlib.Data.Matrix.Block
public import Mitaka.Lemma2
public import Mitaka.SmoothingGS

/-! # The smoothing parameter of the Mitaka trapdoor lattice `L(B)`

Condition 4 of [ZKLY26, Theorem 1] (p. 7, l. 228) asks for
`rs √((1 − √(ϵ/2))(1 − τ̄)/(1 + (2a − 1)τ̄)) ≥ η_ϵ(L(B))`; the paper gives no bound on
`η_ϵ(L(B))`. This file gives one from condition 1 (p. 7, l. 225) and the NTRU equation, through
[Jia+26, Theorem 3] (`Mitaka.LatticeGaussian.smoothingParam_le_profile`).

`B = (g G; −f −F)` (p. 4, l. 137) acts on `(z₁, z₂) ∈ K²` in the coefficient embedding as the
real `2n × 2n` matrix `Key.basisMat` (columns `Xʲ b₁`, then `Xʲ b₂`, `b₁ = (g, −f)`,
`b₂ = (G, −F)`, `j < n`), indexed by `Fin (n + n)` through `Fin.append`; `Key.basisMat_mulVec` is
`Mitaka.basisApply` and `Key.basisMat_mulVec_ofInt` is `Mitaka.latticePoint`, so `L(B)` is the set
of outputs of `Mitaka.sample`.

The Gram–Schmidt vectors of `Key.basisMat` satisfy `‖b̃_i‖ ≤ α√q` (`Key.norm_gs_basisMat_le`): for
`i < n`, `‖b̃_i‖ ≤ ‖Xʲb₁‖ = ‖b₁‖` and `n‖b₁‖² = Σ_k (|f(ζ_k)|² + |g(ζ_k)|²) ≤ nα²q` (Parseval and
condition 1); for `i = n + j`, `‖b̃_i‖ ≤ ‖Xʲ(b₂ − u b₁)‖ = ‖b̃₂‖` with the Gram–Schmidt coefficient
`u` (p. 4, l. 139-141), and `|b̃₂(ζ_k)|² = q²/(|f(ζ_k)|² + |g(ζ_k)|²) ≤ α²q` (Lagrange's identity
with `fG − gF = q`).

* `Key.smoothingParam_basisMat_le_profile`: [Jia+26, Theorem 3] at `G = α√q`, `m = 2n`.
* `Key.smoothingParam_basisMat_le`: `η_ϵ(L(B)) ≤ α√q · √(ln(4n(1 + 1/ϵ))/π)`.

The three key theorems (`Key.norm_gs_basisMat_le`, `Key.smoothingParam_basisMat_le_profile`,
`Key.smoothingParam_basisMat_le`) take `0 < q`, condition 1 (`Key.Annular`), the NTRU equation
(`Key.NTRU`) and a Gram–Schmidt coefficient `u` (`Key.GSCoeff u`) as hypotheses; that such a `u`
exists is not proved here. -/

@[expose] public section

open Real LatticeCrypto Mitaka.LatticeGaussian
open scoped Matrix

namespace Mitaka

variable {n : ℕ}

/-- The matrix of `v ↦ a v` on coefficient vectors of `ℝ[X]/(Xⁿ + 1)`; column `j` is `a Xʲ`. -/
noncomputable def negacyclicMat (a : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun k j => negacyclicConvCoeff a (Pi.single j 1) k

/-- `negacyclicMat a` applies `negacyclicConvCoeff a`. -/
theorem negacyclicMat_mulVec (a v : Fin n → ℝ) :
    negacyclicMat a *ᵥ v = negacyclicConvCoeff a v := by
  funext k
  have hlin : ∀ g : Fin n → ℝ, negacyclicConvCoeff a g k = ∑ ij : Fin n × Fin n,
      (if (ij.1.val + ij.2.val) % n = k.val then
        (if ij.1.val + ij.2.val < n then (1 : ℝ) else -1) else 0) * a ij.1 * g ij.2 := fun g => by
    unfold negacyclicConvCoeff
    refine Finset.sum_congr rfl fun ij _ => ?_
    split_ifs <;> ring
  simp only [Matrix.mulVec, dotProduct, negacyclicMat, hlin, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ij _ => ?_
  simp [Pi.single_apply]

namespace Key

/-- `B = (g G; −f −F)` as a real `2n × 2n` matrix on `Fin.append z₁ z₂`. -/
noncomputable def basisMat (K : Key n) : Matrix (Fin (n + n)) (Fin (n + n)) ℝ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (negacyclicMat (toReal K.g)) (negacyclicMat (toReal K.G))
      (-negacyclicMat (toReal K.f)) (-negacyclicMat (toReal K.F)))

/-- `basisMat` is `basisApply`. -/
theorem basisMat_mulVec (K : Key n) (w : Fin 2 → Fin n → ℝ) :
    K.basisMat *ᵥ Fin.append (w 0) (w 1) = Fin.append (basisApply K w 0) (basisApply K w 1) := by
  funext i
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, basisMat, Matrix.reindex_apply,
      Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Fin.append_left, Fin.append_right, basisApply, Matrix.cons_val_zero, Pi.add_apply,
      ← negacyclicMat_mulVec]
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, basisMat, Matrix.reindex_apply,
      Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Fin.append_left, Fin.append_right, basisApply, Matrix.cons_val_one, Matrix.cons_val_zero,
      Pi.sub_apply, Pi.neg_apply, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib,
      ← negacyclicMat_mulVec]
    ring

/-- `basisMat` on integer coordinates is `latticePoint`. -/
theorem basisMat_mulVec_ofInt (K : Key n) (z₁ z₂ : Fin n → ℤ) :
    K.basisMat *ᵥ ofInt (Fin.append z₁ z₂) =
      ofInt (Fin.append (latticePoint K z₁ z₂ 0) (latticePoint K z₁ z₂ 1)) := by
  have h1 : ofInt (Fin.append z₁ z₂) = Fin.append (toReal z₁) (toReal z₂) := by
    funext i
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;>
      simp only [ofInt, toReal, Fin.append_left, Fin.append_right]
  have h2 := K.basisMat_mulVec ![toReal z₁, toReal z₂]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h2
  rw [h1, h2]
  funext i
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;>
    simp only [Fin.append_left, Fin.append_right, basisApply, latticePoint, Matrix.cons_val_zero,
      Matrix.cons_val_one, ← toReal_negacyclicConvCoeff, ofInt, toReal,
      Pi.add_apply, Pi.sub_apply, Pi.neg_apply] <;> push_cast <;> ring

/-- `B` is invertible under the NTRU equation. -/
theorem det_basisMat_ne_zero (P : Params) (K : Key n) (hq : 0 < P.q) (hN : K.NTRU P) :
    K.basisMat.det ≠ 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  set a : Fin n → ℝ := fun j => v (Fin.castAdd n j)
  set b : Fin n → ℝ := fun j => v (Fin.natAdd n j)
  have hvab : v = Fin.append a b := (Fin.append_castAdd_natAdd).symm
  have h := K.basisMat_mulVec ![a, b]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ← hvab, hv] at h
  have h0 : basisApply K ![a, b] 0 = 0 := by
    funext k
    have := congrFun h (Fin.castAdd n k)
    rw [Fin.append_left] at this
    exact this.symm
  have h1 : basisApply K ![a, b] 1 = 0 := by
    funext k
    have := congrFun h (Fin.natAdd n k)
    rw [Fin.append_right] at this
    exact this.symm
  have e1 : intK K.g * ofCoeffs a + intK K.G * ofCoeffs b = 0 := by
    have := congrArg ofCoeffs h0
    simpa [basisApply, intK, ofCoeffs_add, ofCoeffs_negacyclicConvCoeff hn, ofCoeffs_zero]
      using this
  have e2 : intK K.f * ofCoeffs a + intK K.F * ofCoeffs b = 0 := by
    have := congrArg ofCoeffs h1
    simp only [basisApply, Matrix.cons_val_one, Matrix.cons_val_zero, ofCoeffs_sub, ofCoeffs_neg,
      ofCoeffs_negacyclicConvCoeff hn, ofCoeffs_zero] at this
    simp only [intK]
    linear_combination -this
  have hq' : (P.q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hsmul : ∀ x : KR n, (P.q : ℝ) • x = (P.q : KR n) * x := fun x => by
    rw [(Algebra.smul_def (P.q : ℝ) x : (P.q : ℝ) • x = algebraMap ℝ (KR n) (P.q : ℝ) * x),
      map_natCast]
  have hqa : (P.q : ℝ) • ofCoeffs a = 0 := by
    rw [hsmul]
    linear_combination (-ofCoeffs a) * hN.eq + intK K.G * e2 - intK K.F * e1
  have hqb : (P.q : ℝ) • ofCoeffs b = 0 := by
    rw [hsmul]
    linear_combination (-ofCoeffs b) * hN.eq + intK K.f * e1 - intK K.g * e2
  have ha : a = 0 := ofCoeffs_injective hn
    (((smul_eq_zero.1 hqa).resolve_left hq').trans ofCoeffs_zero.symm)
  have hb : b = 0 := ofCoeffs_injective hn
    (((smul_eq_zero.1 hqb).resolve_left hq').trans ofCoeffs_zero.symm)
  refine hv0 ?_
  rw [hvab, ha, hb]
  funext i
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;>
    simp only [Fin.append_left, Fin.append_right, Pi.zero_apply]

private theorem norm_emb_single (k : Fin n) (l : Fin n) :
    ‖emb l (ofCoeffs (Pi.single k 1 : Fin n → ℝ))‖ = 1 := by
  rw [emb_ofCoeffs, Finset.sum_eq_single k (fun j _ hj => by simp [hj])
    (by simp), Pi.single_eq_same, Complex.ofReal_one, one_mul, norm_pow, root,
    Complex.norm_exp_ofReal_mul_I, one_pow]

private theorem lagrange_aux {f g F G U : ℂ} {q : ℝ}
    (hU : U * ((‖f‖ ^ 2 + ‖g‖ ^ 2 : ℝ) : ℂ) = starRingEnd ℂ g * G + starRingEnd ℂ f * F)
    (hq : f * G - g * F = q) :
    (‖G - U * g‖ ^ 2 + ‖F - U * f‖ ^ 2) * (‖f‖ ^ 2 + ‖g‖ ^ 2) = q ^ 2 := by
  have hγc : ((‖f‖ ^ 2 + ‖g‖ ^ 2 : ℝ) : ℂ) = f * starRingEnd ℂ f + g * starRingEnd ℂ g := by
    push_cast
    rw [Complex.mul_conj', Complex.mul_conj']
  rw [hγc] at hU
  have hqc : starRingEnd ℂ f * starRingEnd ℂ G - starRingEnd ℂ g * starRingEnd ℂ F = q := by
    have := congrArg (starRingEnd ℂ) hq
    simpa using this
  apply Complex.ofReal_injective
  push_cast
  simp only [← Complex.mul_conj', map_sub, map_mul]
  linear_combination (starRingEnd ℂ U * (f * starRingEnd ℂ f + g * starRingEnd ℂ g) -
    (g * starRingEnd ℂ G + f * starRingEnd ℂ F)) * hU +
    (starRingEnd ℂ f * starRingEnd ℂ G - starRingEnd ℂ g * starRingEnd ℂ F) * hq + (q : ℂ) * hqc

private theorem toLp_mulVec_mem_span {m : ℕ} (B : Matrix (Fin m) (Fin m) ℝ) (x : Fin m → ℝ)
    (i : Fin m) (hx : ∀ j, ¬ j < i → x j = 0) :
    WithLp.toLp 2 (B *ᵥ x) ∈ Submodule.span ℝ (col B '' Set.Iio i) := by
  have h : WithLp.toLp 2 (B *ᵥ x) = ∑ j, x j • col B j := by
    ext r
    simp [col, Matrix.mulVec, dotProduct, mul_comm]
  rw [h]
  refine Submodule.sum_mem _ fun j _ => ?_
  by_cases hj : j < i
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  · rw [hx j hj, zero_smul]
    exact Submodule.zero_mem _

private theorem col_eq {m : ℕ} (B : Matrix (Fin m) (Fin m) ℝ) (j : Fin m) :
    col B j = WithLp.toLp 2 (B *ᵥ Pi.single j 1) := by
  rw [Matrix.mulVec_single_one]
  rfl

private theorem norm_toLp_basisMat_le (P : Params) (K : Key n) (hn : 0 < n) (hα : 0 ≤ P.alpha)
    {a b : Fin n → ℝ}
    (h : ∀ l, ‖emb l (intK K.g * ofCoeffs a + intK K.G * ofCoeffs b)‖ ^ 2 +
      ‖emb l (intK K.f * ofCoeffs a + intK K.F * ofCoeffs b)‖ ^ 2 ≤ P.alpha ^ 2 * P.q) :
    ‖WithLp.toLp 2 (K.basisMat *ᵥ Fin.append a b)‖ ≤ P.alpha * √(P.q : ℝ) := by
  have hb := K.basisMat_mulVec ![a, b]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hb
  have hsq : (n : ℝ) * ‖WithLp.toLp 2 (K.basisMat *ᵥ Fin.append a b)‖ ^ 2 =
      ∑ l, (‖emb l (intK K.g * ofCoeffs a + intK K.G * ofCoeffs b)‖ ^ 2 +
        ‖emb l (intK K.f * ofCoeffs a + intK K.F * ofCoeffs b)‖ ^ 2) := by
    rw [hb, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_add, Finset.sum_add_distrib]
    simp only [Fin.append_left, Fin.append_right]
    rw [mul_add, ← sum_norm_sq_emb_ofCoeffs, ← sum_norm_sq_emb_ofCoeffs]
    simp only [basisApply, Matrix.cons_val_zero, Matrix.cons_val_one, ofCoeffs_add, ofCoeffs_sub,
      ofCoeffs_neg, ofCoeffs_negacyclicConvCoeff hn, intK]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← norm_neg, ← map_neg, neg_sub, sub_neg_eq_add, add_comm]
  have hle : (n : ℝ) * ‖WithLp.toLp 2 (K.basisMat *ᵥ Fin.append a b)‖ ^ 2 ≤
      n * (P.alpha ^ 2 * P.q) := by
    rw [hsq]
    calc _ ≤ ∑ _l : Fin n, P.alpha ^ 2 * (P.q : ℝ) := Finset.sum_le_sum fun l _ => h l
      _ = n * (P.alpha ^ 2 * P.q) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 := le_of_mul_le_mul_left hle hn'
  refine le_of_sq_le_sq ?_ (by positivity)
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  exact h2

/-- Every Gram–Schmidt norm of `B` is at most `α√q`, given `0 < q`, condition 1, the NTRU equation
and a Gram–Schmidt coefficient `u` (`Key.GSCoeff u`, assumed). -/
theorem norm_gs_basisMat_le (P : Params) (K : Key n) (u : Fin n → ℝ) (hq : 0 < P.q)
    (hK : K.Annular P) (hN : K.NTRU P) (hu : K.GSCoeff u) (i : Fin (n + n)) :
    ‖gs K.basisMat i‖ ≤ P.alpha * √(P.q : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact i.elim0
  have hα := hK.one_le_alpha
  have hq0 : (0 : ℝ) < P.q := by exact_mod_cast hq
  have hγ : ∀ l : Fin n, 0 < ‖emb l (intK K.f)‖ ^ 2 + ‖emb l (intK K.g)‖ ^ 2 := fun l =>
    lt_of_lt_of_le (div_pos hq0 (by positivity)) (hK.le_normSq l)
  have hlt : ∀ j k : Fin n, Fin.castAdd n j < Fin.natAdd n k := fun j k => by
    rw [Fin.lt_def]
    simp only [Fin.val_castAdd, Fin.val_natAdd]
    omega
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · have hcol : col K.basisMat (Fin.castAdd n k) =
        WithLp.toLp 2 (K.basisMat *ᵥ Fin.append (Pi.single k 1) 0) := by
      rw [col_eq]
      congr 2
      funext j
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [Fin.append_left, Pi.single_apply, Fin.castAdd_inj]
      · simp only [Fin.append_right, Pi.single_apply, Pi.zero_apply]
        simp only [(hlt k j).ne', ↓reduceIte]
    refine (norm_gs_le_norm_sub _ _ (Submodule.zero_mem _)).trans ?_
    rw [sub_zero, hcol]
    refine norm_toLp_basisMat_le P K hn (by linarith) fun l => ?_
    simp only [ofCoeffs_zero, mul_zero, add_zero, map_mul, norm_mul, norm_emb_single, mul_one]
    linarith [hK.normSq_le l]
  · set c := negacyclicConvCoeff u (Pi.single k 1)
    have hv : WithLp.toLp 2 (K.basisMat *ᵥ Fin.append c 0) ∈
        Submodule.span ℝ (col K.basisMat '' Set.Iio (Fin.natAdd n k)) := by
      refine toLp_mulVec_mem_span _ _ _ fun j hj => ?_
      refine Fin.addCases (fun j hj => ?_) (fun j _ => ?_) j hj
      · exact absurd (hlt j k) hj
      · simp only [Fin.append_right, Pi.zero_apply]
    have hcol : col K.basisMat (Fin.natAdd n k) - WithLp.toLp 2 (K.basisMat *ᵥ Fin.append c 0) =
        WithLp.toLp 2 (K.basisMat *ᵥ Fin.append (-c) (Pi.single k 1)) := by
      rw [col_eq, ← WithLp.toLp_sub, ← Matrix.mulVec_sub]
      congr 2
      funext j
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [Pi.sub_apply, Fin.append_left, Pi.single_apply, Pi.neg_apply]
        simp only [(hlt j k).ne, ↓reduceIte]
        ring
      · simp only [Pi.sub_apply, Fin.append_right, Pi.single_apply, Pi.zero_apply, sub_zero,
          Fin.natAdd_inj]
    refine (norm_gs_le_norm_sub _ _ hv).trans ?_
    rw [hcol]
    refine norm_toLp_basisMat_le P K hn (by linarith) fun l => ?_
    set ζ := emb l (ofCoeffs (Pi.single k 1 : Fin n → ℝ))
    set U := emb l (ofCoeffs u)
    have h1 : emb l (intK K.g * ofCoeffs (-c) + intK K.G * ofCoeffs (Pi.single k 1)) =
        ζ * (emb l (intK K.G) - U * emb l (intK K.g)) := by
      simp only [c, ofCoeffs_neg, ofCoeffs_negacyclicConvCoeff hn, map_add, map_mul, map_neg, ζ, U]
      ring
    have h2 : emb l (intK K.f * ofCoeffs (-c) + intK K.F * ofCoeffs (Pi.single k 1)) =
        ζ * (emb l (intK K.F) - U * emb l (intK K.f)) := by
      simp only [c, ofCoeffs_neg, ofCoeffs_negacyclicConvCoeff hn, map_add, map_mul, map_neg, ζ, U]
      ring
    have hζ : ‖ζ‖ = 1 := norm_emb_single k l
    rw [h1, h2, norm_mul, norm_mul, hζ, one_mul, one_mul]
    have hU : U * ((‖emb l (intK K.f)‖ ^ 2 + ‖emb l (intK K.g)‖ ^ 2 : ℝ) : ℂ) =
        starRingEnd ℂ (emb l (intK K.g)) * emb l (intK K.G) +
          starRingEnd ℂ (emb l (intK K.f)) * emb l (intK K.F) := by
      have := congrArg (emb l) hu.eq
      simp only [map_add, map_mul, emb_conjK] at this
      rw [← this]
      push_cast
      rw [Complex.conj_mul', Complex.conj_mul']
    have hqe : emb l (intK K.f) * emb l (intK K.G) - emb l (intK K.g) * emb l (intK K.F) =
        ((P.q : ℝ) : ℂ) := by
      have := congrArg (emb l) hN.eq
      simpa using this
    have hL := lagrange_aux hU hqe
    have hlow := hK.le_normSq l
    have hα2 : 0 < P.alpha ^ 2 := by positivity
    have h3 : P.q ≤ P.alpha ^ 2 * (‖emb l (intK K.f)‖ ^ 2 + ‖emb l (intK K.g)‖ ^ 2) := by
      rwa [div_le_iff₀' hα2] at hlow
    have h4 : (P.q : ℝ) ^ 2 ≤ P.alpha ^ 2 * P.q *
        (‖emb l (intK K.f)‖ ^ 2 + ‖emb l (intK K.g)‖ ^ 2) := by
      linarith [mul_le_mul_of_nonneg_left h3 hq0.le]
    exact le_of_mul_le_mul_right (by rw [hL]; linarith) (hγ l)

/-- [Jia+26, Theorem 3] for the Mitaka basis: `η_{ϵ′}(L(B)) ≤ α√q · √(ln(4n(1 + 1/ϵ))/π)` with
`ϵ′ = S/(1 − S)`, `S = profileSum (basisMat K) (α√q) ϵ < 1`, given `0 < q`, condition 1, the
NTRU equation and a Gram–Schmidt coefficient `u` (`Key.GSCoeff u`, assumed). -/
theorem smoothingParam_basisMat_le_profile (P : Params) (K : Key n) (u : Fin n → ℝ)
    (hq : 0 < P.q) (hK : K.Annular P) (hN : K.NTRU P) (hu : K.GSCoeff u) {ϵ : ℝ} (hϵ : 0 < ϵ)
    (hS : profileSum K.basisMat (P.alpha * √(P.q : ℝ)) ϵ < 1) :
    smoothingParam
        (profileSum K.basisMat (P.alpha * √(P.q : ℝ)) ϵ /
          (1 - profileSum K.basisMat (P.alpha * √(P.q : ℝ)) ϵ)) K.basisMat ≤
      P.alpha * √(P.q : ℝ) * √(Real.log (4 * n * (1 + 1 / ϵ)) / π) := by
  have h := smoothingParam_le_profile (det_basisMat_ne_zero P K hq hN) hϵ
    (norm_gs_basisMat_le P K u hq hK hN hu) hS
  rwa [show (2 : ℝ) * ((n + n : ℕ) : ℝ) * (1 + 1 / ϵ) = 4 * n * (1 + 1 / ϵ) by push_cast; ring]
    at h

/-- `η_ϵ(L(B)) ≤ α√q · √(ln(4n(1 + 1/ϵ))/π)` for `ϵ > 0`, given `0 < q`, condition 1, the NTRU
equation and a Gram–Schmidt coefficient `u` (`Key.GSCoeff u`, assumed). -/
theorem smoothingParam_basisMat_le (P : Params) (K : Key n) (u : Fin n → ℝ) (hq : 0 < P.q)
    (hK : K.Annular P) (hN : K.NTRU P) (hu : K.GSCoeff u) {ϵ : ℝ} (hϵ : 0 < ϵ) :
    smoothingParam ϵ K.basisMat ≤ P.alpha * √(P.q : ℝ) * √(Real.log (4 * n * (1 + 1 / ϵ)) / π) := by
  have h := smoothingParam_le_of_norm_gs_le (det_basisMat_ne_zero P K hq hN) hϵ
    (norm_gs_basisMat_le P K u hq hK hN hu)
  rwa [show (2 : ℝ) * ((n + n : ℕ) : ℝ) * (1 + 1 / ϵ) = 4 * n * (1 + 1 / ϵ) by push_cast; ring]
    at h

end Key

end Mitaka
