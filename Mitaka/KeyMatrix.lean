/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mitaka.Lemma3
public import Mitaka.SmoothingNTRU

/-! # The key matrices of Algorithm 3 as real `2n × 2n` matrices, and the laws `𝒬₀`, `𝒬_e`

[ZKLY26] (ePrint 2026/2521) states Theorem 1 (p. 7, l. 223-229) and Lemma 4 (p. 7, l. 237) with
the lattice Gaussians `𝒬₀ = D_{L(B),rs,c}` (p. 6, l. 221) and
`𝒬_e = D_{L(B), r√(s²I₂ₙ − Σ_e), c}` on `L(B) ⊂ ℝ^{2n}`. The matrices `B̂ = B U_{−û}`, `Â`
and `Σ_e = Σ_p − ÂÂ* = s²I − B̂B̂* − ÂÂ*` (p. 5, l. 170-194) are `2 × 2` matrices over `K`; Lemma 3
bounds `Σ_e` through the embeddings (`Key.norm2_sigmaE_le`, `Key.normF_sigmaE_le`). Here they act on
`ℝ^{2n} = ℝ^{n+n}` in the coefficient embedding, as `Key.basisMat` does (`Fin.append` of the two
coefficient vectors; the `(i, j)` block of a `K`-matrix entry `a` is `negacyclicMat a`).

* `coefMat X`: the real matrix of a `2 × 2` matrix `X` of coefficient vectors;
  `coefMat_mulVec`: it acts as `aMat X` on `K_ℝ²` (`toKVec`).
* `Key.bHatMat`, `Key.aHatCoefMat`, `Key.sigmaEMat`: `B̂`, `Â`, `Σ_e` as real matrices;
  `Key.bHatMat_mulVec`, `Key.sigmaEMat_mulVec`: they act as `Key.bHat`, `Key.sigmaE`.
* `Key.abs_dotProduct_sigmaEMat_le`, `Key.sum_sq_sigmaEMat`: `|xᵗΣ_e x| ≤ ‖Σ_e‖₂ ‖x‖²` and
  `Σᵢⱼ (Σ_e)ᵢⱼ² = ‖Σ_e‖_F²` (Parseval; `‖·‖₂`, `‖·‖_F` as on p. 3, l. 129-130).
* `Key.perturbation_eq`, `Key.bHatMat_mulVec_centre`: Algorithm 3's `p = (1/L)Âx` and
  `ĉ = B̂⁻¹(c − p)` in matrix form.
* `Key.latticeGaussian K M c`: `D_{L(B),M,c}` on the output type of `Mitaka.sample`, the image of
  `gaussianMeasure K.basisMat M c` under the coordinates `z ↦ Bz` (`Key.coordPoint`, which is
  `latticePoint`); `Key.gaussianQ0` (`M = rs I`) and `Key.gaussianQe`
  (`M = r √(s²I − Σ_e)`, with `CFC.sqrt` the positive square root). -/

@[expose] public section

open Real MeasureTheory LatticeCrypto Mitaka.LatticeGaussian
open scoped Matrix MatrixOrder

namespace Mitaka

variable {n : ℕ}

/-- The real `2n × 2n` matrix of a `2 × 2` matrix `X` of coefficient vectors: block `(i, j)` is
`negacyclicMat (X i j)`, indexed through `Fin.append`. -/
noncomputable def coefMat (X : Fin 2 → Fin 2 → Fin n → ℝ) :
    Matrix (Fin (n + n)) (Fin (n + n)) ℝ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (negacyclicMat (X 0 0)) (negacyclicMat (X 0 1))
      (negacyclicMat (X 1 0)) (negacyclicMat (X 1 1)))

/-- The two coefficient vectors of `x ∈ ℝ^{n+n}` (inverse of `Fin.append`). -/
def splitVec (x : Fin (n + n) → ℝ) : Fin 2 → Fin n → ℝ :=
  ![fun k => x (Fin.castAdd n k), fun k => x (Fin.natAdd n k)]

/-- `x ∈ ℝ^{n+n}` as a vector of `K_ℝ²`. -/
noncomputable def toKVec (x : Fin (n + n) → ℝ) : Fin 2 → KR n := fun i => ofCoeffs (splitVec x i)

/-- `splitVec` inverts `Fin.append`. -/
theorem splitVec_append (a b : Fin n → ℝ) : splitVec (Fin.append a b) = ![a, b] := by
  funext i
  fin_cases i <;> funext k <;>
    simp only [splitVec, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.append_left, Fin.append_right]

/-- `Fin.append` inverts `splitVec`. -/
theorem append_splitVec (x : Fin (n + n) → ℝ) : Fin.append (splitVec x 0) (splitVec x 1) = x := by
  funext i
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;>
    simp only [splitVec, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.append_left,
      Fin.append_right]

/-- A reindexed block matrix acts blockwise on the two coefficient vectors. -/
theorem splitVec_blocks_mulVec (A B C D : Matrix (Fin n) (Fin n) ℝ) (x : Fin (n + n) → ℝ) :
    splitVec (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A B C D) *ᵥ x) =
      ![A *ᵥ splitVec x 0 + B *ᵥ splitVec x 1, C *ᵥ splitVec x 0 + D *ᵥ splitVec x 1] := by
  funext i k
  fin_cases i <;>
    simp only [splitVec, Matrix.mulVec, dotProduct, Fin.sum_univ_add, Matrix.reindex_apply,
      Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, Pi.add_apply]

/-- `toKVec` is additive. -/
theorem toKVec_add (x y : Fin (n + n) → ℝ) : toKVec (x + y) = toKVec x + toKVec y := by
  funext i
  fin_cases i <;> simp [toKVec, splitVec, ← ofCoeffs_add] <;> rfl

/-- `ofCoeffs` is `ℝ`-linear. -/
theorem ofCoeffs_smul (c : ℝ) (x : Fin n → ℝ) : ofCoeffs (c • x) = c • ofCoeffs x := by
  rw [(Algebra.smul_def c (ofCoeffs x) : c • ofCoeffs x = algebraMap ℝ (KR n) c * ofCoeffs x)]
  simp only [ofCoeffs, Pi.smul_apply, smul_eq_mul, ← Polynomial.C_mul_monomial,
    ← Finset.mul_sum, map_mul]
  rfl

/-- `toKVec` commutes with scalars. -/
theorem toKVec_smul (c : ℝ) (x : Fin (n + n) → ℝ) : toKVec (c • x) = c • toKVec x := by
  funext i
  fin_cases i <;> simp [toKVec, splitVec, ← ofCoeffs_smul] <;> rfl

/-- `toKVec` is surjective for `n > 0`. -/
theorem toKVec_surjective (hn : 0 < n) : Function.Surjective (toKVec (n := n)) := by
  have hmonic : (negacyclicModulus ℝ n).Monic := by
    simpa [negacyclicModulus] using Polynomial.monic_X_pow_add_C (1 : ℝ) hn.ne'
  have hdeg : (negacyclicModulus ℝ n).natDegree = n := by
    simp [negacyclicModulus]
  have hne : negacyclicModulus ℝ n ≠ 1 := fun h => by
    rw [h, Polynomial.natDegree_one] at hdeg
    exact hn.ne hdeg
  have hsurj : ∀ f : KR n, ∃ x : Fin n → ℝ, ofCoeffs x = f := fun f => by
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective (g := negacyclicModulus ℝ n) f
    have hp := Polynomial.natDegree_modByMonic_lt p hmonic hne
    rw [hdeg] at hp
    refine ⟨fun k => (p %ₘ negacyclicModulus ℝ n).coeff k, ?_⟩
    have h1 := AdjoinRoot.mk_leftInverse hmonic (AdjoinRoot.mk _ p)
    rw [AdjoinRoot.modByMonicHom_mk, Polynomial.as_sum_range' _ n hp, Finset.sum_range] at h1
    exact h1
  intro v
  choose x hx using hsurj
  refine ⟨Fin.append (x (v 0)) (x (v 1)), funext fun i => ?_⟩
  fin_cases i <;> simp [toKVec, splitVec_append, hx]

/-- `‖a + b‖² = ‖a‖² + ‖b‖² + 2 Re(conj a · b)`. -/
private theorem norm_add_sq' (a b : ℂ) :
    ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 + 2 * (starRingEnd ℂ a * b).re := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_add]
  simp [Complex.mul_re]

/-- Parseval, polarised: `Re Σ_k conj φ_k(x) φ_k(y) = n ⟨x, y⟩`. -/
theorem re_sum_conj_emb_mul_emb (x y : Fin n → ℝ) :
    (∑ k : Fin n, starRingEnd ℂ (emb k (ofCoeffs x)) * emb k (ofCoeffs y)).re = n * (x ⬝ᵥ y) := by
  have h := sum_norm_sq_emb_ofCoeffs (x + y)
  have hx := sum_norm_sq_emb_ofCoeffs x
  have hy := sum_norm_sq_emb_ofCoeffs y
  simp only [ofCoeffs_add, map_add, norm_add_sq', Finset.sum_add_distrib, ← Finset.mul_sum] at h
  have hs : ∑ j, (x + y) j ^ 2 = ∑ j, x j ^ 2 + ∑ j, y j ^ 2 + 2 * (x ⬝ᵥ y) := by
    rw [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by simp only [Pi.add_apply]; ring
  rw [Complex.re_sum]
  linear_combination (h - hx - hy + (n : ℝ) * hs) / 2

/-- `φ_k` applied to the two entries of a vector of `K_ℝ²`. -/
noncomputable def embV (k : Fin n) (v : Fin 2 → KR n) : Fin 2 → ℂ := fun i => emb k (v i)

/-- `φ_k(Hv) = φ_k(H) φ_k(v)`. -/
theorem embV_mulVec (k : Fin n) (H : KMat n) (v : Fin 2 → KR n) :
    embV k (H *ᵥ v) = embM k H *ᵥ embV k v := by
  funext i
  simp [embV, Matrix.mulVec, dotProduct, embM_apply, Fin.sum_univ_two]

/-- Parseval on `K_ℝ²`: `Re Σ_k ⟨φ_k(x), φ_k(y)⟩ = n ⟨x, y⟩`. -/
theorem re_sum_star_dotProduct (x y : Fin (n + n) → ℝ) :
    (∑ k : Fin n, star (embV k (toKVec x)) ⬝ᵥ embV k (toKVec y)).re = n * (x ⬝ᵥ y) := by
  have hxy : x ⬝ᵥ y = splitVec x 0 ⬝ᵥ splitVec y 0 + splitVec x 1 ⬝ᵥ splitVec y 1 := by
    simp [dotProduct, Fin.sum_univ_add, splitVec]
  rw [hxy, mul_add, ← re_sum_conj_emb_mul_emb, ← re_sum_conj_emb_mul_emb, ← Complex.add_re,
    ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [dotProduct, Fin.sum_univ_two, embV, toKVec]

/-- `n ‖x‖² = Σ_k ‖φ_k(x)‖²` on `K_ℝ²`. -/
theorem sum_vecNormSq_embV (x : Fin (n + n) → ℝ) :
    ∑ k : Fin n, CMat.vecNormSq (embV k (toKVec x)) = n * sqNorm x := by
  have h := re_sum_star_dotProduct x x
  simp only [CMat.star_dotProduct_self, ← Complex.ofReal_sum, Complex.ofReal_re] at h
  rw [h, sqNorm]

/-- `coefMat X` acts on `K_ℝ²` as the `K_ℝ`-matrix `aMat X`. -/
theorem coefMat_mulVec (hn : 0 < n) (X : Fin 2 → Fin 2 → Fin n → ℝ) (x : Fin (n + n) → ℝ) :
    toKVec (coefMat X *ᵥ x) = aMat X *ᵥ toKVec x := by
  funext i
  rw [toKVec, coefMat, splitVec_blocks_mulVec]
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, aMat, toKVec, ofCoeffs_add,
      negacyclicMat_mulVec, ofCoeffs_negacyclicConvCoeff hn]

/-- `toKVec` commutes with subtraction. -/
theorem toKVec_sub (x y : Fin (n + n) → ℝ) : toKVec (x - y) = toKVec x - toKVec y := by
  rw [eq_sub_iff_add_eq, ← toKVec_add, sub_add_cancel]

/-- `toKVec` is injective for `n > 0`. -/
theorem toKVec_injective (hn : 0 < n) : Function.Injective (toKVec (n := n)) := fun x y h => by
  rw [← append_splitVec x, ← append_splitVec y]
  have h0 := ofCoeffs_injective hn (congrFun h 0)
  have h1 := ofCoeffs_injective hn (congrFun h 1)
  rw [h0, h1]

/-- `M` acts on `K_ℝ²` as `H`. -/
private def IsRealForm (M : Matrix (Fin (n + n)) (Fin (n + n)) ℝ) (H : KMat n) : Prop :=
  ∀ x, toKVec (M *ᵥ x) = H *ᵥ toKVec x

private theorem IsRealForm.mul {M M' : Matrix (Fin (n + n)) (Fin (n + n)) ℝ} {H H' : KMat n}
    (h : IsRealForm M H) (h' : IsRealForm M' H') : IsRealForm (M * M') (H * H') := fun x => by
  rw [← Matrix.mulVec_mulVec, h, h', Matrix.mulVec_mulVec]

private theorem IsRealForm.add {M M' : Matrix (Fin (n + n)) (Fin (n + n)) ℝ} {H H' : KMat n}
    (h : IsRealForm M H) (h' : IsRealForm M' H') : IsRealForm (M + M') (H + H') := fun x => by
  rw [Matrix.add_mulVec, toKVec_add, h, h', Matrix.add_mulVec]

private theorem IsRealForm.sub {M M' : Matrix (Fin (n + n)) (Fin (n + n)) ℝ} {H H' : KMat n}
    (h : IsRealForm M H) (h' : IsRealForm M' H') : IsRealForm (M - M') (H - H') := fun x => by
  rw [Matrix.sub_mulVec, toKVec_sub, h, h', Matrix.sub_mulVec]

private theorem IsRealForm.smul_one (c : ℝ) :
    IsRealForm (c • (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ)) (c • (1 : KMat n)) := fun x => by
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, toKVec_smul, Matrix.smul_mulVec,
    Matrix.one_mulVec]

/-- `⟨u, A w⟩ = ⟨Aᴴ u, w⟩`. -/
private theorem star_dotProduct_mulVec (A : CMat) (u w : Fin 2 → ℂ) :
    star u ⬝ᵥ (A *ᵥ w) = star (Aᴴ *ᵥ u) ⬝ᵥ w := by
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, Matrix.dotProduct_mulVec]

private theorem IsRealForm.transpose (hn : 0 < n) {M : Matrix (Fin (n + n)) (Fin (n + n)) ℝ}
    {H : KMat n} (h : IsRealForm M H) : IsRealForm Mᵀ (adjM H) := fun x => by
  obtain ⟨z, hz⟩ := toKVec_surjective hn (adjM H *ᵥ toKVec x)
  suffices hM : Mᵀ *ᵥ x = z by rw [hM, hz]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have key : ∀ y, (Mᵀ *ᵥ x - z) ⬝ᵥ y = 0 := fun y => by
    have h4 : ∑ k, star (embV k (toKVec x)) ⬝ᵥ embV k (toKVec (M *ᵥ y)) =
        ∑ k, star (embV k (toKVec z)) ⬝ᵥ embV k (toKVec y) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [h y, embV_mulVec, hz, embV_mulVec, embM_adjM, star_dotProduct_mulVec]
    have h5 := congrArg Complex.re h4
    rw [re_sum_star_dotProduct, re_sum_star_dotProduct] at h5
    rw [sub_dotProduct, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec,
      mul_left_cancel₀ hn' h5, sub_self]
  have h0 := key (Mᵀ *ᵥ x - z)
  rwa [dotProduct_self_eq_zero, sub_eq_zero] at h0

private theorem isRealForm_coefMat (hn : 0 < n) (X : Fin 2 → Fin 2 → Fin n → ℝ) :
    IsRealForm (coefMat X) (aMat X) :=
  coefMat_mulVec hn X

/-- `|⟨v, Av⟩| ≤ σ_max(A) ‖v‖²`. -/
private theorem norm_star_dotProduct_mulVec_le (A : CMat) (v : Fin 2 → ℂ) :
    ‖star v ⬝ᵥ (A *ᵥ v)‖ ≤ CMat.sigmaMax A * CMat.vecNormSq v := by
  have h1 : star v ⬝ᵥ (A *ᵥ v) = inner ℂ (WithLp.toLp 2 v) (WithLp.toLp 2 (A *ᵥ v)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  have hv := CMat.norm_sq_eq_vecNormSq (WithLp.toLp 2 v)
  have hw := CMat.norm_sq_eq_vecNormSq (WithLp.toLp 2 (A *ᵥ v))
  rw [WithLp.ofLp_toLp] at hv hw
  have hσ := CMat.sigmaMax_nonneg A
  have hy : ‖WithLp.toLp 2 (A *ᵥ v)‖ ≤ CMat.sigmaMax A * ‖WithLp.toLp 2 v‖ :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 (by
      rw [mul_pow, hw, hv]
      exact CMat.vecNormSq_mulVec_le A v)
  rw [h1, ← hv]
  calc ‖inner ℂ (WithLp.toLp 2 v) (WithLp.toLp 2 (A *ᵥ v))‖
      ≤ ‖WithLp.toLp 2 v‖ * ‖WithLp.toLp 2 (A *ᵥ v)‖ := norm_inner_le_norm _ _
    _ ≤ ‖WithLp.toLp 2 v‖ * (CMat.sigmaMax A * ‖WithLp.toLp 2 v‖) :=
        mul_le_mul_of_nonneg_left hy (norm_nonneg _)
    _ = CMat.sigmaMax A * ‖WithLp.toLp (2 : ENNReal) v‖ ^ 2 := by ring

/-- The quadratic form of a real form is bounded by `‖H‖₂`. -/
private theorem IsRealForm.abs_dotProduct_le (hn : 0 < n)
    {M : Matrix (Fin (n + n)) (Fin (n + n)) ℝ} {H : KMat n} (h : IsRealForm M H)
    (x : Fin (n + n) → ℝ) : |x ⬝ᵥ (M *ᵥ x)| ≤ KMat.norm2 H * sqNorm x := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have h1 := re_sum_star_dotProduct x (M *ᵥ x)
  simp only [h x, embV_mulVec] at h1
  have h2 : |(n : ℝ) * (x ⬝ᵥ (M *ᵥ x))| ≤ (n : ℝ) * (KMat.norm2 H * sqNorm x) := by
    rw [← h1, mul_left_comm, ← sum_vecNormSq_embV, Finset.mul_sum]
    refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans
      (Finset.sum_le_sum fun k _ => (norm_star_dotProduct_mulVec_le _ _).trans ?_))
    exact mul_le_mul_of_nonneg_right (KMat.sigmaMax_le_norm2 H k) (CMat.vecNormSq_nonneg _)
  rw [abs_mul, abs_of_pos hn'] at h2
  exact le_of_mul_le_mul_left h2 hn'

/-- The norm of a real form is bounded by `‖H‖₂`. -/
private theorem IsRealForm.sqNorm_mulVec_le (hn : 0 < n)
    {M : Matrix (Fin (n + n)) (Fin (n + n)) ℝ} {H : KMat n} (h : IsRealForm M H)
    (x : Fin (n + n) → ℝ) : sqNorm (M *ᵥ x) ≤ KMat.norm2 H ^ 2 * sqNorm x := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have h2 : (n : ℝ) * sqNorm (M *ᵥ x) ≤ (n : ℝ) * (KMat.norm2 H ^ 2 * sqNorm x) := by
    rw [← sum_vecNormSq_embV, mul_left_comm, ← sum_vecNormSq_embV, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [h x, embV_mulVec]
    refine (CMat.vecNormSq_mulVec_le _ _).trans
      (mul_le_mul_of_nonneg_right ?_ (CMat.vecNormSq_nonneg _))
    exact pow_le_pow_left₀ (CMat.sigmaMax_nonneg _) (KMat.sigmaMax_le_norm2 H k) 2
  exact le_of_mul_le_mul_left h2 hn'

private theorem splitVec_single_castAdd (l : Fin n) :
    splitVec (Pi.single (Fin.castAdd n l) (1 : ℝ)) = ![Pi.single l 1, 0] := by
  funext i k
  have := k.isLt
  have := l.isLt
  fin_cases i <;> simp [splitVec, Pi.single_apply, Fin.ext_iff]
  omega

private theorem splitVec_single_natAdd (l : Fin n) :
    splitVec (Pi.single (Fin.natAdd n l) (1 : ℝ)) = ![0, Pi.single l 1] := by
  funext i k
  have := k.isLt
  have := l.isLt
  fin_cases i <;> simp [splitVec, Pi.single_apply, Fin.ext_iff]
  omega

private theorem emb_ofCoeffs_single (k l : Fin n) :
    emb k (ofCoeffs (Pi.single l 1)) = root n k ^ (l : ℕ) := by
  rw [emb_ofCoeffs, Finset.sum_eq_single l (fun b _ hb => by simp [hb])
    (by simp)]
  simp

private theorem normSq_root_pow (k : Fin n) (l : ℕ) : Complex.normSq (root n k ^ l) = 1 := by
  rw [← Complex.sq_norm, norm_pow, root, Complex.norm_exp_ofReal_mul_I, one_pow, one_pow]

private theorem toKVec_single_castAdd (l : Fin n) :
    toKVec (Pi.single (Fin.castAdd n l) (1 : ℝ)) = ![ofCoeffs (Pi.single l 1), 0] := by
  funext i
  simp only [toKVec, splitVec_single_castAdd]
  fin_cases i <;> simp [ofCoeffs_zero]

private theorem toKVec_single_natAdd (l : Fin n) :
    toKVec (Pi.single (Fin.natAdd n l) (1 : ℝ)) = ![0, ofCoeffs (Pi.single l 1)] := by
  funext i
  simp only [toKVec, splitVec_single_natAdd]
  fin_cases i <;> simp [ofCoeffs_zero]

/-- The Frobenius norm of a real form is `‖H‖_F` [ZKLY26, p. 3, l. 130]. -/
private theorem IsRealForm.sum_sq (hn : 0 < n) {M : Matrix (Fin (n + n)) (Fin (n + n)) ℝ}
    {H : KMat n} (h : IsRealForm M H) : ∑ i, ∑ j, M i j ^ 2 = KMat.normF H ^ 2 := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hcol : ∀ j, ∑ i, M i j ^ 2 = sqNorm (M *ᵥ Pi.single j 1) := fun j => by
    simp [sqNorm, dotProduct, Matrix.mulVec_single, sq]
  have hk : ∀ k : Fin n, ∑ j, CMat.vecNormSq (embV k (toKVec (M *ᵥ Pi.single j 1))) =
      n * CMat.frob (embM k H) ^ 2 := fun k => by
    rw [Finset.sum_congr rfl fun j _ => by rw [h (Pi.single j 1), embV_mulVec]]
    simp only [Fin.sum_univ_add, toKVec_single_castAdd, toKVec_single_natAdd]
    simp [embV, Matrix.mulVec, dotProduct, Fin.sum_univ_two, CMat.vecNormSq,
      emb_ofCoeffs_single, Complex.normSq_mul, normSq_root_pow, CMat.frob_sq, Complex.sq_norm]
    ring
  have h2 : (n : ℝ) * ∑ i, ∑ j, M i j ^ 2 = (n : ℝ) * KMat.normF H ^ 2 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    simp only [hcol, ← sum_vecNormSq_embV]
    rw [Finset.sum_comm, Finset.sum_congr rfl fun k _ => hk k, ← Finset.mul_sum, KMat.normF_sq]
  exact mul_left_cancel₀ hn'.ne' h2

namespace Key

/-- `U_a = (1 a; 0 1)` [ZKLY26, p. 4, l. 138] as a real matrix. -/
noncomputable def uCoefMat (a : Fin n → ℝ) : Matrix (Fin (n + n)) (Fin (n + n)) ℝ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 (negacyclicMat a) 0 1)

/-- `B̂ = B U_{−û}` [ZKLY26, p. 5, l. 170] as a real matrix. -/
noncomputable def bHatMat (P : Params) (K : Key n) : Matrix (Fin (n + n)) (Fin (n + n)) ℝ :=
  K.basisMat * uCoefMat (-K.uHat P)

/-- `Â = Key.aInt / p_A` [ZKLY26, p. 5, l. 191] as a real matrix. -/
noncomputable def aHatCoefMat (P : Params) (K : Key n) : Matrix (Fin (n + n)) (Fin (n + n)) ℝ :=
  coefMat (K.aHat P)

/-- `Σ_e = s²I − B̂B̂* − ÂÂ*` [ZKLY26, p. 5, l. 175, 194] as a real matrix. -/
noncomputable def sigmaEMat (P : Params) (K : Key n) : Matrix (Fin (n + n)) (Fin (n + n)) ℝ :=
  P.s ^ 2 • (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ) - K.bHatMat P * (K.bHatMat P)ᵀ -
    K.aHatCoefMat P * (K.aHatCoefMat P)ᵀ

private theorem isRealForm_uCoefMat (hn : 0 < n) (a : Fin n → ℝ) :
    IsRealForm (uCoefMat a) (uMat (ofCoeffs a)) := fun x => by
  funext i
  rw [toKVec, uCoefMat, splitVec_blocks_mulVec]
  fin_cases i <;>
    simp [uMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, toKVec, ofCoeffs_add,
      negacyclicMat_mulVec, ofCoeffs_negacyclicConvCoeff hn]

private theorem isRealForm_basisMat (hn : 0 < n) (K : Key n) :
    IsRealForm K.basisMat K.bMat := fun x => by
  funext i
  rw [toKVec, Key.basisMat, splitVec_blocks_mulVec]
  fin_cases i <;>
    simp [Key.bMat, intK, Matrix.mulVec, dotProduct, Fin.sum_univ_two, toKVec, ofCoeffs_add,
      ofCoeffs_neg, Matrix.neg_mulVec, negacyclicMat_mulVec, ofCoeffs_negacyclicConvCoeff hn]
  ring

private theorem isRealForm_bHatMat (hn : 0 < n) (P : Params) (K : Key n) :
    IsRealForm (K.bHatMat P) (K.bHat P) := by
  have h := (isRealForm_basisMat hn K).mul (isRealForm_uCoefMat hn (-K.uHat P))
  rw [ofCoeffs_neg] at h
  exact h

private theorem isRealForm_sigmaEMat (hn : 0 < n) (P : Params) (K : Key n) :
    IsRealForm (K.sigmaEMat P) (K.sigmaE P) :=
  ((IsRealForm.smul_one _).sub ((isRealForm_bHatMat hn P K).mul
    ((isRealForm_bHatMat hn P K).transpose hn))).sub
    ((isRealForm_coefMat hn _).mul ((isRealForm_coefMat hn _).transpose hn))

/-- `bHatMat` acts on `K_ℝ²` as `B̂ = Key.bHat`. -/
theorem bHatMat_mulVec (hn : 0 < n) (P : Params) (K : Key n) (x : Fin (n + n) → ℝ) :
    toKVec (K.bHatMat P *ᵥ x) = K.bHat P *ᵥ toKVec x :=
  isRealForm_bHatMat hn P K x

/-- `sigmaEMat` acts on `K_ℝ²` as `Σ_e = Key.sigmaE`. -/
theorem sigmaEMat_mulVec (hn : 0 < n) (P : Params) (K : Key n) (x : Fin (n + n) → ℝ) :
    toKVec (K.sigmaEMat P *ᵥ x) = K.sigmaE P *ᵥ toKVec x :=
  isRealForm_sigmaEMat hn P K x

/-- `|xᵗ Σ_e x| ≤ ‖Σ_e‖₂ ‖x‖²` for the real form of `Σ_e` and `‖·‖₂` of [ZKLY26, p. 3, l. 129]. -/
theorem abs_dotProduct_sigmaEMat_le (hn : 0 < n) (P : Params) (K : Key n)
    (x : Fin (n + n) → ℝ) :
    |x ⬝ᵥ (K.sigmaEMat P *ᵥ x)| ≤ KMat.norm2 (K.sigmaE P) * sqNorm x :=
  (isRealForm_sigmaEMat hn P K).abs_dotProduct_le hn x

/-- `Σᵢⱼ (Σ_e)ᵢⱼ² = ‖Σ_e‖_F²`: the Frobenius norm of the real form of `Σ_e` is `‖Σ_e‖_F` of
[ZKLY26, p. 3, l. 130]. -/
theorem sum_sq_sigmaEMat (hn : 0 < n) (P : Params) (K : Key n) :
    ∑ i, ∑ j, K.sigmaEMat P i j ^ 2 = KMat.normF (K.sigmaE P) ^ 2 :=
  (isRealForm_sigmaEMat hn P K).sum_sq hn

/-- `B̂` is invertible under the NTRU equation. -/
theorem det_bHatMat_ne_zero (P : Params) (K : Key n) (hq : 0 < P.q) (hN : K.NTRU P) :
    (K.bHatMat P).det ≠ 0 := by
  rw [bHatMat, Matrix.det_mul, uCoefMat, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, mul_one, mul_one]
  exact det_basisMat_ne_zero P K hq hN

private theorem isRealForm_inv_bHatMat (hn : 0 < n) (P : Params) (K : Key n) (hq : 0 < P.q)
    (hN : K.NTRU P) : IsRealForm (K.bHatMat P)⁻¹ (K.bHatInv P) := fun x => by
  have hu : IsUnit (K.bHatMat P).det := isUnit_iff_ne_zero.2 (det_bHatMat_ne_zero P K hq hN)
  have hy : K.bHatMat P *ᵥ ((K.bHatMat P)⁻¹ *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  conv_rhs => rw [← hy]
  rw [isRealForm_bHatMat hn P K, Matrix.mulVec_mulVec, bHatInv_mul_bHat P K hq hN,
    Matrix.one_mulVec]

/-- `‖B̂⁻¹Âx‖² ≤ ‖B̂⁻¹Â‖₂² ‖x‖²` (with `B̂⁻¹ = Key.bHatInv`, `Â = Key.aHatMat`). -/
theorem sqNorm_inv_bHatMat_mul_le (hn : 0 < n) (P : Params) (K : Key n) (hq : 0 < P.q)
    (hN : K.NTRU P) (x : Fin (n + n) → ℝ) :
    sqNorm (((K.bHatMat P)⁻¹ * K.aHatCoefMat P) *ᵥ x) ≤
      KMat.norm2 (K.bHatInv P * K.aHatMat P) ^ 2 * sqNorm x :=
  ((isRealForm_inv_bHatMat hn P K hq hN).mul (isRealForm_coefMat hn _)).sqNorm_mulVec_le hn x

private theorem splitVec_smul (c : ℝ) (x : Fin (n + n) → ℝ) (i : Fin 2) :
    splitVec (c • x) i = c • splitVec x i := by
  fin_cases i <;> rfl

private theorem splitVec_ofInt_append (a b : Fin n → ℤ) :
    splitVec (ofInt (Fin.append a b)) = ![toReal a, toReal b] := by
  funext i
  fin_cases i <;> funext k <;>
    simp only [splitVec, ofInt, toReal, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.append_left, Fin.append_right]

/-- Algorithm 3, step 2: `p = (1/L) Â x` [ZKLY26, p. 6]. -/
theorem perturbation_eq (P : Params) (K : Key n) (x : Fin 2 → Fin n → ℤ) :
    Fin.append (perturbation P K x 0) (perturbation P K x 1) =
      (P.L : ℝ)⁻¹ • (K.aHatCoefMat P *ᵥ ofInt (Fin.append (x 0) (x 1))) := by
  have e : ∀ i, splitVec ((P.L : ℝ)⁻¹ • (K.aHatCoefMat P *ᵥ ofInt (Fin.append (x 0) (x 1)))) i =
      perturbation P K x i := fun i => by
    funext k
    rw [splitVec_smul, aHatCoefMat, coefMat, splitVec_blocks_mulVec, splitVec_ofInt_append]
    fin_cases i <;>
      simp [perturbation, negacyclicMat_mulVec, Fin.sum_univ_two, div_eq_inv_mul]
  rw [← append_splitVec ((P.L : ℝ)⁻¹ • (K.aHatCoefMat P *ᵥ ofInt (Fin.append (x 0) (x 1)))),
    e, e]

/-- Algorithm 3, step 3: `ĉ = B̂⁻¹ v`, i.e. `B̂ ĉ = v` for `ĉ = centre P K v`, under the NTRU
equation [ZKLY26, p. 6; p. 5, l. 170-171]. -/
theorem bHatMat_mulVec_centre (P : Params) (K : Key n) (hq : 0 < P.q) (hN : K.NTRU P)
    (v : Fin 2 → Fin n → ℝ) :
    K.bHatMat P *ᵥ Fin.append (centre P K v 0) (centre P K v 1) = Fin.append (v 0) (v 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · funext i
    exact absurd i.isLt (by simp)
  have hsm : ∀ (r : ℝ) (a : KR n), r • a = mkQ ℝ n (Polynomial.C r) * a :=
    fun r a => Algebra.smul_def r a
  have hc : toKVec (Fin.append (centre P K v 0) (centre P K v 1)) =
      K.bHatInv P *ᵥ toKVec (Fin.append (v 0) (v 1)) := by
    funext i
    fin_cases i <;>
      simp [toKVec, splitVec_append, centre, Key.bHatInv, uMat, intK, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, Matrix.mul_apply, hsm, ofCoeffs_fun_div, ofCoeffs_fun_add, ofCoeffs_add,
        ofCoeffs_negacyclicConvCoeff hn, ofCoeffs_fun_neg] <;> ring
  apply toKVec_injective hn
  rw [isRealForm_bHatMat hn P K, hc, Matrix.mulVec_mulVec, bHat_mul_bHatInv P K hq hN,
    Matrix.one_mulVec]

/-- The lattice point `B z` of the coordinates `z = Fin.append z₁ z₂`, in the output type of
`Mitaka.sample` (`basisMat_mulVec_ofInt`). -/
def coordPoint (K : Key n) (z : Fin (n + n) → ℤ) : Fin 2 → Fin n → ℤ :=
  latticePoint K (fun k => z (Fin.castAdd n k)) (fun k => z (Fin.natAdd n k))

/-- `D_{L(B),M,c}` on the output type of `Mitaka.sample`: the image of the coordinate law
`gaussianMeasure K.basisMat M c` under `z ↦ B z`, with `c ∈ K²` as `Fin.append (c 0) (c 1)`. -/
noncomputable def latticeGaussian (K : Key n) (M : Matrix (Fin (n + n)) (Fin (n + n)) ℝ)
    (c : Fin 2 → Fin n → ℝ) : Measure (Fin 2 → Fin n → ℤ) :=
  (gaussianMeasure K.basisMat M (Fin.append (c 0) (c 1))).map K.coordPoint

/-- `𝒬₀ = D_{L(B),rs,c}` [ZKLY26, p. 6, l. 221]. -/
noncomputable def gaussianQ0 (P : Params) (K : Key n) (c : Fin 2 → Fin n → ℝ) :
    Measure (Fin 2 → Fin n → ℤ) :=
  K.latticeGaussian ((P.r * P.s) • (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ)) c

/-- `𝒬_e = D_{L(B), r√(s²I₂ₙ − Σ_e), c}` [ZKLY26, p. 7, l. 237], with `√·` the positive square
root `CFC.sqrt`. -/
noncomputable def gaussianQe (P : Params) (K : Key n) (c : Fin 2 → Fin n → ℝ) :
    Measure (Fin 2 → Fin n → ℤ) :=
  K.latticeGaussian
    (P.r • CFC.sqrt (P.s ^ 2 • (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ) - K.sigmaEMat P)) c

/-- `D_{L(B),M,c}(Bz) = ρ_{M,c}(Bz)/ρ_{M,c}(L(B))` at `Bz = latticePoint K z₁ z₂`
[ZKLY26, p. 3, l. 102]. -/
theorem latticeGaussian_singleton (P : Params) (K : Key n) (hq : 0 < P.q) (hN : K.NTRU P)
    (M : Matrix (Fin (n + n)) (Fin (n + n)) ℝ) (c : Fin 2 → Fin n → ℝ) (z₁ z₂ : Fin n → ℤ) :
    K.latticeGaussian M c {latticePoint K z₁ z₂} =
      ENNReal.ofReal (rho M (Fin.append (c 0) (c 1)) (K.basisMat *ᵥ ofInt (Fin.append z₁ z₂)) /
        rhoSum K.basisMat M (Fin.append (c 0) (c 1))) := by
  have hB := det_basisMat_ne_zero P K hq hN
  have e : ∀ z, K.basisMat *ᵥ ofInt z = ofInt (Fin.append (K.coordPoint z 0) (K.coordPoint z 1)) :=
    fun z => by
      have h := K.basisMat_mulVec_ofInt (fun k => z (Fin.castAdd n k)) (fun k => z (Fin.natAdd n k))
      rwa [Fin.append_castAdd_natAdd] at h
  have hinj : Function.Injective K.coordPoint := fun z z' h =>
    injective_mulVec_ofInt hB (by simp only [e, h])
  have hz : K.coordPoint (Fin.append z₁ z₂) = latticePoint K z₁ z₂ := by
    simp only [coordPoint, Fin.append_left, Fin.append_right]
  have hpre : K.coordPoint ⁻¹' {latticePoint K z₁ z₂} = {Fin.append z₁ z₂} := by
    ext z
    rw [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_singleton_iff, ← hz, hinj.eq_iff]
  rw [latticeGaussian, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    hpre, gaussianMeasure_singleton, gaussianPMF]

/-- `D_{L(B),M,c}` is a probability measure. -/
theorem isProbabilityMeasure_latticeGaussian (P : Params) (K : Key n) (hq : 0 < P.q)
    (hN : K.NTRU P) {M : Matrix (Fin (n + n)) (Fin (n + n)) ℝ} (hM : M.det ≠ 0)
    (c : Fin 2 → Fin n → ℝ) : IsProbabilityMeasure (K.latticeGaussian M c) := by
  have := isProbabilityMeasure_gaussianMeasure (det_basisMat_ne_zero P K hq hN) hM
    (Fin.append (c 0) (c 1))
  rw [latticeGaussian]
  infer_instance

/-- `𝒬₀` is a probability measure. -/
theorem isProbabilityMeasure_gaussianQ0 (P : Params) (K : Key n) (hq : 0 < P.q) (hN : K.NTRU P)
    (hr0 : 0 < P.r) (hs0 : 0 < P.s) (c : Fin 2 → Fin n → ℝ) :
    IsProbabilityMeasure (K.gaussianQ0 P c) :=
  isProbabilityMeasure_latticeGaussian P K hq hN (by
    rw [Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ (mul_pos hr0 hs0).ne') c

end Key

end Mitaka
