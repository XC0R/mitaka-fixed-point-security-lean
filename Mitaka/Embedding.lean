/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import LatticeCrypto.Ring.SchoolbookCert
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-! # The canonical embedding of `ℝ[X]/(Xⁿ + 1)` and the coefficient-to-evaluation bound

[ZKLY26] (ePrint 2026/2521), §2.3 (p. 3, l. 116-130; p. 4, l. 131-132). For `n = 2^ℓ`,
`K = ℚ[X]/(Xⁿ + 1)` has the `n` complex embeddings `φ_k(f) = f(ζ^{2k+1})`, `0 ≤ k < n`, where
`ζ = exp(πi/n)` is a primitive `2n`-th root of unity, and `f* = f(X⁻¹)` has
`φ_k(f*) = conj φ_k(f)`. Elements are taken in `K_ℝ = ℝ[X]/(Xⁿ + 1)` (VCVio's
`NegacyclicQuotient ℝ n`), which also holds the Cholesky root `A` of Lemma 3. For a `2 × 2` matrix
`H` over `K_ℝ`, `φ_k(H)` applies `φ_k` entrywise, `‖H‖₂ = max_k σ_max(φ_k(H))`,
`σ_min(H) = min_k σ_min(φ_k(H))`, `‖H‖_F² = Σ_k ‖φ_k(H)‖_F²`, and `Σ ≻ 0` when `Σ = Σ*` and every
`φ_k(Σ)` is positive definite. For a complex matrix `M`, `σ_max(M)` is Mathlib's `ℓ²` operator
norm, `σ_min(M)` the minimum of `‖Mx‖` and `λ_max(M)` the maximum of `Re ⟪x, Mx⟫` over unit
vectors `x`.

* `sum_abs_cos_le`: `Σ_{j<n} |cos(φ + jπ/n)| ≤ csc(π/(2n))` for `n ≥ 1`.
* `sum_abs_cos_root_le`: for `n = 2^ℓ` and `θ = (2k+1)π/n` the angles `jθ` are, modulo `π`, a
  permutation of the `jπ/n`, so `Σ_{j<n} |cos(jθ - φ)| ≤ csc(π/(2n))` (p. 18, l. 569).
* `norm_sum_mul_root_pow_le`, `norm_emb_ofCoeffs_le`: the coefficient-to-evaluation bound
  `|f(ζ)| ≤ ‖f‖∞ csc(π/(2n))` at every root of `Xⁿ + 1`, for real `f` (p. 18, l. 567-569).
* `sum_norm_sq_emb_ofCoeffs`: Parseval, `Σ_k |φ_k(f)|² = n ‖f‖₂²` (p. 3, l. 130).

`2 × 2` complex matrices are handled through `CMat.vecNormSq` (`‖v‖²` on `ℂ²`). For `M` with
`‖M‖_F² ≤ T ≤ 2B` and `TB ≤ B² + |det M|²`, `CMat.vecNormSq_mulVec_le_of_frob` gives
`‖Mv‖² ≤ B‖v‖²` and `CMat.normSq_det_mul_le_of_frob` gives `|det M|² ‖v‖² ≤ B‖Mv‖²`: with
`v^⊥ = (-conj v₁, conj v₀)`, `‖Mv‖² + ‖Mv^⊥‖² = ‖M‖_F² ‖v‖²` and `‖Mv‖ ‖Mv^⊥‖ ≥ |det M| ‖v‖²`
(Lagrange's identity). This is the "quadratic formula" step of [ZKLY26, p. 18, l. 574].
`CMat.sigmaMax_le_of_lower`: a lower-triangular matrix with entries at most `ε` has
`σ_max ≤ ε (1 + √5)/2` (p. 18, l. 578-582). `CMat.lambdaMax_mul_conjTranspose_add_one`:
`λ_max(NN* + I) = 1 + σ_max(N)²` (p. 19, l. 589). -/

@[expose] public section

open Polynomial LatticeCrypto
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

namespace Mitaka

/-- `K_ℝ = ℝ[X]/(Xⁿ + 1)`. -/
abbrev KR (n : ℕ) := NegacyclicQuotient ℝ n

/-- `2 × 2` matrices over `K_ℝ`. -/
abbrev KMat (n : ℕ) := Matrix (Fin 2) (Fin 2) (KR n)

/-- `2 × 2` complex matrices. -/
abbrev CMat := Matrix (Fin 2) (Fin 2) ℂ

variable {n : ℕ}

/-! ### Coefficient vectors -/

/-- The element of `K_ℝ` with coefficient vector `x`. -/
noncomputable def ofCoeffs (x : Fin n → ℝ) : KR n :=
  mkQ ℝ n (∑ k : Fin n, Polynomial.monomial k.val (x k))

/-- `ofCoeffs 0 = 0`. -/
theorem ofCoeffs_zero : ofCoeffs (0 : Fin n → ℝ) = 0 := by
  simp [ofCoeffs]

/-- `ofCoeffs` is additive. -/
theorem ofCoeffs_add (x y : Fin n → ℝ) : ofCoeffs (x + y) = ofCoeffs x + ofCoeffs y := by
  simp only [ofCoeffs, Pi.add_apply, map_add, Finset.sum_add_distrib]

/-- `ofCoeffs` commutes with subtraction. -/
theorem ofCoeffs_sub (x y : Fin n → ℝ) : ofCoeffs (x - y) = ofCoeffs x - ofCoeffs y := by
  simp only [ofCoeffs, Pi.sub_apply, map_sub, Finset.sum_sub_distrib]

/-- `ofCoeffs` commutes with negation. -/
theorem ofCoeffs_neg (x : Fin n → ℝ) : ofCoeffs (-x) = -ofCoeffs x := by
  simp only [ofCoeffs, Pi.neg_apply, map_neg, Finset.sum_neg_distrib]

/-- `ofCoeffs` is additive (pointwise form). -/
theorem ofCoeffs_fun_add (x y : Fin n → ℝ) :
    ofCoeffs (fun k => x k + y k) = ofCoeffs x + ofCoeffs y :=
  ofCoeffs_add x y

/-- `ofCoeffs` commutes with negation (pointwise form). -/
theorem ofCoeffs_fun_neg (x : Fin n → ℝ) : ofCoeffs (fun k => -x k) = -ofCoeffs x :=
  ofCoeffs_neg x

/-- Dividing the coefficients by `r` multiplies by the constant `r⁻¹`. -/
theorem ofCoeffs_fun_div (x : Fin n → ℝ) (r : ℝ) :
    ofCoeffs (fun k => x k / r) = ofCoeffs x * mkQ ℝ n (Polynomial.C r⁻¹) := by
  simp only [ofCoeffs, ← map_mul, Finset.sum_mul, div_eq_mul_inv, Polynomial.monomial_mul_C]

/-- `ofCoeffs` turns the negacyclic convolution into the product of `K_ℝ`. -/
theorem ofCoeffs_negacyclicConvCoeff (hn : 0 < n) (x y : Fin n → ℝ) :
    ofCoeffs (negacyclicConvCoeff x y) = ofCoeffs x * ofCoeffs y := by
  unfold ofCoeffs
  rw [← mk_double_sum_eq_mk_negacyclicConv hn, ← map_mul, Finset.sum_mul_sum]
  simp only [Polynomial.monomial_mul_monomial]

/-- A coefficient vector is determined by its element of `K_ℝ`. -/
theorem ofCoeffs_injective (hn : 0 < n) : Function.Injective (ofCoeffs (n := n)) := by
  intro x y h
  have hmonic : (negacyclicModulus ℝ n).Monic := by
    simpa [negacyclicModulus] using Polynomial.monic_X_pow_add_C (1 : ℝ) hn.ne'
  have hdeg : (negacyclicModulus ℝ n).degree = n := by
    simpa [negacyclicModulus] using Polynomial.degree_X_pow_add_C hn (1 : ℝ)
  have key : ∀ x : Fin n → ℝ, AdjoinRoot.modByMonicHom hmonic (ofCoeffs x) =
      ∑ k : Fin n, Polynomial.monomial k.val (x k) := fun x => by
    change AdjoinRoot.modByMonicHom hmonic (AdjoinRoot.mk _ _) = _
    rw [AdjoinRoot.modByMonicHom_mk, (Polynomial.modByMonic_eq_self_iff hmonic).2]
    rw [hdeg, Polynomial.degree_lt_iff_coeff_zero]
    intro j hj
    rw [Polynomial.finsetSum_coeff]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Polynomial.coeff_monomial_apply]
    exact ite_eq_right (Nat.ne_of_lt (i.isLt.trans_le hj))
  have hp := congrArg (AdjoinRoot.modByMonicHom hmonic) h
  rw [key, key] at hp
  funext k
  have hk := congrArg (fun p : Polynomial ℝ => p.coeff k.val) hp
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial_apply, Fin.val_inj] at hk
  simpa using hk

/-! ### The embeddings -/

/-- `csc(π/(2n))`. -/
noncomputable def cscN (n : ℕ) : ℝ := 1 / Real.sin (Real.pi / (2 * n))

/-- The root `ζ^{2k+1} = exp((2k+1)πi/n)` of `Xⁿ + 1`, with `ζ = exp(πi/n)`. -/
noncomputable def root (n k : ℕ) : ℂ :=
  Complex.exp ((((2 * k + 1) * Real.pi / n : ℝ) : ℂ) * Complex.I)

/-- `(ζ^{2k+1})ⁿ = -1`. -/
theorem root_pow (hn : n ≠ 0) (k : ℕ) : root n k ^ n = -1 := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h : (n : ℂ) * ((((2 * k + 1) * Real.pi / n : ℝ) : ℂ) * Complex.I) =
      ((2 * k + 1 : ℕ) : ℂ) * (Real.pi * Complex.I) := by
    push_cast
    field_simp
  rw [root, ← Complex.exp_nat_mul, h, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
  exact Odd.neg_one_pow ⟨k, rfl⟩

/-- `ζ = exp(πi/n)`. -/
private noncomputable def rho (n : ℕ) : ℂ := Complex.exp (Real.pi * Complex.I / n)

private theorem isPrimitiveRoot_rho (hn : n ≠ 0) : IsPrimitiveRoot (rho n) (2 * n) := by
  have h := Complex.isPrimitiveRoot_exp (2 * n) (by omega)
  have e : 2 * (Real.pi : ℂ) * Complex.I / ((2 * n : ℕ) : ℂ) = Real.pi * Complex.I / n := by
    push_cast
    ring
  rwa [e] at h

private theorem root_eq_rho_pow (k : ℕ) : root n k = rho n ^ (2 * k + 1) := by
  rw [root, rho, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem conj_rho : starRingEnd ℂ (rho n) = (rho n)⁻¹ := by
  rw [rho, ← Complex.exp_conj, ← Complex.exp_neg, map_div₀, map_mul, Complex.conj_ofReal,
    Complex.conj_I, map_natCast]
  ring_nf

private theorem conj_root (k : ℕ) : starRingEnd ℂ (root n k) = (root n k)⁻¹ := by
  rw [root_eq_rho_pow, map_pow, conj_rho, inv_pow]

/-- For `n = 2^ℓ`, each `ζ^{2k+1}` is a primitive `2n`-th root of unity. -/
theorem isPrimitiveRoot_root {ℓ : ℕ} (hn : n = 2 ^ ℓ) (k : ℕ) :
    IsPrimitiveRoot (root n k) (2 * n) := by
  have hn0 : n ≠ 0 := by
    rw [hn]
    positivity
  rw [root_eq_rho_pow]
  refine (isPrimitiveRoot_rho hn0).pow_of_coprime _ ?_
  rw [hn, ← pow_succ']
  exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 (odd_two_mul_add_one k))

/-- The embedding `φ_k(f) = f(ζ^{2k+1})` of `K_ℝ` into `ℂ` [ZKLY26, p. 3, l. 120]. -/
noncomputable def emb (k : Fin n) : KR n →+* ℂ :=
  AdjoinRoot.lift (f := negacyclicModulus ℝ n) (algebraMap ℝ ℂ) (root n k) (by
    simp only [negacyclicModulus, Polynomial.eval₂_add, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_one, root_pow k.pos.ne', neg_add_cancel])

/-- `φ_k` on the class of a polynomial is evaluation at `ζ^{2k+1}`. -/
theorem emb_mkQ (k : Fin n) (p : Polynomial ℝ) :
    emb k (mkQ ℝ n p) = p.eval₂ (algebraMap ℝ ℂ) (root n k) :=
  AdjoinRoot.lift_mk _ p

/-- `φ_k(x) = Σ_j x_j ζ^{(2k+1)j}`. -/
theorem emb_ofCoeffs (k : Fin n) (x : Fin n → ℝ) :
    emb k (ofCoeffs x) = ∑ j : Fin n, (x j : ℂ) * root n k ^ (j : ℕ) := by
  rw [ofCoeffs, emb_mkQ, Polynomial.eval₂_finsetSum]
  simp [Polynomial.eval₂_monomial]

/-- `φ_k` fixes real constants. -/
theorem emb_algebraMap (k : Fin n) (r : ℝ) : emb k (algebraMap ℝ (KR n) r) = r := by
  change emb k (mkQ ℝ n (Polynomial.C r)) = r
  rw [emb_mkQ, Polynomial.eval₂_C]
  rfl

/-- `(Xⁿ + 1)(x) = xⁿ + 1`. -/
theorem eval₂_negacyclicModulus {T : Type*} [CommRing T] (i : ℝ →+* T) (x : T) :
    (negacyclicModulus ℝ n).eval₂ i x = x ^ n + 1 := by
  simp [negacyclicModulus]

/-- If `yⁿ = -1`, then `-y^{n-1}` is a root of `Xⁿ + 1`. -/
theorem neg_pow_pred_pow_add_one {T : Type*} [CommRing T] {y : T} {n : ℕ}
    (hy : y ^ n = -1) : (-y ^ (n - 1)) ^ n + 1 = 0 := by
  rcases n with _ | m
  · rw [pow_zero] at hy ⊢
    linear_combination hy
  · rw [neg_pow, Nat.add_sub_cancel, ← pow_mul, mul_comm m (m + 1), pow_mul, hy, ← pow_add,
      Odd.neg_one_pow ⟨m, by ring⟩, neg_add_cancel]

/-- The class of `X` in `K_ℝ`. -/
noncomputable def xK (n : ℕ) : KR n := mkQ ℝ n Polynomial.X

/-- `Xⁿ = -1` in `K_ℝ`. -/
theorem xK_pow (n : ℕ) : xK n ^ n = -1 := by
  rw [xK, ← map_pow]
  exact mk_X_pow_n

/-- `X⁻¹ = -X^{n-1}` is a root of `Xⁿ + 1` in `K_ℝ`. -/
theorem eval₂_neg_xK_pow (n : ℕ) :
    (negacyclicModulus ℝ n).eval₂ (Algebra.ofId ℝ (KR n) : ℝ →+* KR n) (-xK n ^ (n - 1)) = 0 := by
  rw [eval₂_negacyclicModulus]
  exact neg_pow_pred_pow_add_one (xK_pow n)

/-- The involution `f ↦ f* = f(X⁻¹)` of `K_ℝ`, with `X⁻¹ = -X^{n-1}` [ZKLY26, p. 3, l. 126]. -/
noncomputable def conjK (n : ℕ) : KR n →ₐ[ℝ] KR n :=
  AdjoinRoot.liftAlgHom (negacyclicModulus ℝ n) (Algebra.ofId ℝ (KR n)) (-xK n ^ (n - 1))
    (eval₂_neg_xK_pow n)

/-- `φ_k(X) = ζ^{2k+1}`. -/
theorem emb_xK (k : Fin n) : emb k (xK n) = root n k := by
  rw [xK, emb_mkQ, Polynomial.eval₂_X]

/-- `X* = -X^{n-1}`. -/
theorem conjK_xK : conjK n (xK n) = -xK n ^ (n - 1) := by
  change Polynomial.eval₂ _ _ Polynomial.X = _
  rw [Polynomial.eval₂_X]

private theorem mul_neg_pow_pred {T : Type*} [CommRing T] {y : T} (hn : n ≠ 0)
    (hy : y ^ n = -1) : y * -y ^ (n - 1) = 1 := by
  rw [mul_neg, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hn), hy, neg_neg]

/-- `X X* = 1`. -/
theorem xK_mul_conjK_xK (hn : n ≠ 0) : xK n * conjK n (xK n) = 1 := by
  rw [conjK_xK]
  exact mul_neg_pow_pred hn (xK_pow n)

/-- `f** = f`. -/
theorem conjK_conjK (hn : n ≠ 0) (f : KR n) : conjK n (conjK n f) = f := by
  have h : (conjK n).comp (conjK n) = AlgHom.id ℝ (KR n) := by
    apply AdjoinRoot.algHom_ext
    have h1 := xK_mul_conjK_xK hn
    have h2 : conjK n (xK n) * conjK n (conjK n (xK n)) = 1 := by
      rw [← map_mul, h1, map_one]
    change conjK n (conjK n (xK n)) = xK n
    linear_combination (-conjK n (conjK n (xK n))) * h1 + xK n * h2
  exact congrArg (fun φ : KR n →ₐ[ℝ] KR n => φ f) h

/-- `φ_k(f*) = conj φ_k(f)` [ZKLY26, p. 3, l. 126]. -/
theorem emb_conjK (k : Fin n) (f : KR n) : emb k (conjK n f) = starRingEnd ℂ (emb k f) := by
  have hn : n ≠ 0 := k.pos.ne'
  have h : (emb k).comp (conjK n : KR n →+* KR n) = (starRingEnd ℂ).comp (emb k) := by
    refine Ideal.Quotient.ringHom_ext (Polynomial.ringHom_ext (fun r => ?_) ?_)
    · change emb k (conjK n (algebraMap ℝ (KR n) r)) =
        starRingEnd ℂ (emb k (algebraMap ℝ (KR n) r))
      rw [AlgHom.commutes, emb_algebraMap, Complex.conj_ofReal]
    · change emb k (conjK n (xK n)) = starRingEnd ℂ (emb k (xK n))
      rw [conjK_xK, emb_xK, map_neg, map_pow, emb_xK, conj_root]
      refine eq_inv_of_mul_eq_one_left ?_
      rw [neg_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hn), root_pow hn,
        neg_neg]
  exact congrArg (fun φ : KR n →+* ℂ => φ f) h

/-- The conjugate transpose `H*` over `K_ℝ`, `(H*)ᵢⱼ = (Hⱼᵢ)*` [ZKLY26, p. 3, l. 127]. -/
noncomputable def adjM (H : KMat n) : KMat n := Matrix.of fun i j => conjK n (H j i)

/-- `φ_k` applied entrywise, `φ_k(HG) = φ_k(H) φ_k(G)` [ZKLY26, p. 3, l. 122-124]. -/
noncomputable def embM (k : Fin n) : KMat n →+* CMat := (emb k).mapMatrix

/-- `φ_k(H*) = φ_k(H)ᴴ`. -/
theorem embM_adjM (k : Fin n) (H : KMat n) : embM k (adjM H) = (embM k H)ᴴ := by
  ext i j
  simp [embM, adjM, emb_conjK]

/-- `φ_k(H)ᵢⱼ = φ_k(Hᵢⱼ)`. -/
theorem embM_apply (k : Fin n) (H : KMat n) (i j : Fin 2) : embM k H i j = emb k (H i j) := rfl

/-- `φ_k(r f) = r φ_k(f)` for real `r`. -/
theorem emb_smul (k : Fin n) (r : ℝ) (f : KR n) : emb k (r • f) = r * emb k f := by
  rw [show r • f = algebraMap ℝ (KR n) r * f from Algebra.smul_def r f, map_mul, emb_algebraMap]

/-- `φ_k(r I) = r I` for real `r`. -/
theorem embM_smul_one (k : Fin n) (r : ℝ) : embM k (r • (1 : KMat n)) = (r : ℂ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embM_apply, emb_smul]

/-- `(H + G)* = H* + G*`. -/
theorem adjM_add (H G : KMat n) : adjM (H + G) = adjM H + adjM G := by
  ext i j
  simp [adjM]

/-- `(H - G)* = H* - G*`. -/
theorem adjM_sub (H G : KMat n) : adjM (H - G) = adjM H - adjM G := by
  ext i j
  simp [adjM]

/-- `(HG)* = G* H*`. -/
theorem adjM_mul (H G : KMat n) : adjM (H * G) = adjM G * adjM H := by
  ext i j
  simp only [adjM, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul]
  ring

/-- `H** = H`. -/
theorem adjM_adjM (hn : n ≠ 0) (H : KMat n) : adjM (adjM H) = H := by
  ext i j
  simp [adjM, conjK_conjK hn]

/-- `I* = I`. -/
theorem adjM_one : adjM (1 : KMat n) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adjM]

/-- `(r I)* = r I` for real `r`. -/
theorem adjM_smul_one (r : ℝ) : adjM (r • (1 : KMat n)) = r • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adjM]

/-! ### Norms of `2 × 2` matrices -/

namespace CMat

/-- The largest singular value: the `ℓ²` operator norm. -/
noncomputable def sigmaMax (M : CMat) : ℝ := ‖M‖

/-- The smallest singular value: the minimum of `‖Mx‖` over unit vectors. -/
noncomputable def sigmaMin (M : CMat) : ℝ :=
  ⨅ x : Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1, ‖Matrix.toEuclideanLin M x‖

/-- The largest eigenvalue of a Hermitian matrix: the maximum of `Re ⟪x, Mx⟫` over unit vectors. -/
noncomputable def lambdaMax (M : CMat) : ℝ :=
  ⨆ x : Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1,
    (inner ℂ (x : EuclideanSpace ℂ (Fin 2)) (Matrix.toEuclideanLin M x)).re

/-- The Frobenius norm. -/
noncomputable def frob (M : CMat) : ℝ := √(∑ i, ∑ j, ‖M i j‖ ^ 2)

end CMat

namespace KMat

/-- `‖H‖₂ = max_k σ_max(φ_k(H))` [ZKLY26, p. 3, l. 129]. -/
noncomputable def norm2 (H : KMat n) : ℝ := ⨆ k : Fin n, CMat.sigmaMax (embM k H)

/-- `σ_min(H) = min_k σ_min(φ_k(H))` [ZKLY26, p. 3, l. 129]. -/
noncomputable def sigmaMin (H : KMat n) : ℝ := ⨅ k : Fin n, CMat.sigmaMin (embM k H)

/-- `λ_max(H) = max_k λ_max(φ_k(H))`. -/
noncomputable def lambdaMax (H : KMat n) : ℝ := ⨆ k : Fin n, CMat.lambdaMax (embM k H)

/-- `‖H‖_F = (Σ_k ‖φ_k(H)‖_F²)^{1/2}` [ZKLY26, p. 3, l. 130]. -/
noncomputable def normF (H : KMat n) : ℝ := √(∑ k : Fin n, CMat.frob (embM k H) ^ 2)

/-- `Σ ≻ 0`: `Σ = Σ*` and every `φ_k(Σ)` is positive definite [ZKLY26, p. 4, l. 131-132]. -/
structure PosDef (H : KMat n) : Prop where
  /-- `Σ = Σ*`. -/
  adjM_eq : adjM H = H
  /-- Every `φ_k(Σ)` is positive definite. -/
  posDef : ∀ k, (embM k H).PosDef

end KMat

/-! ### The coefficient-to-evaluation bound -/

/-- An `n`-periodic sequence summed along `j ↦ aj + b`, `a` coprime to `n`. -/
private theorem sum_fin_affine (g : ℕ → ℝ) (hg : ∀ t, g (t + n) = g t) {a : ℕ}
    (ha : a.Coprime n) (b : ℕ) : ∑ j : Fin n, g (a * j + b) = ∑ j : Fin n, g j := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hq : ∀ q t, g (t + n * q) = g t := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      intro t
      rw [Nat.mul_succ, ← add_assoc, hg, ih]
  have hmod : ∀ t, g t = g (t % n) := fun t => by
    have := hq (t / n) (t % n)
    rwa [Nat.mod_add_div] at this
  let e : Fin n → Fin n := fun j => ⟨(a * j + b) % n, Nat.mod_lt _ hn⟩
  have he : Function.Injective e := by
    intro i j hij
    have h1 : a * i + b ≡ a * j + b [MOD n] := congrArg Fin.val hij
    exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt
      (Nat.ModEq.cancel_left_of_coprime ha.symm (Nat.ModEq.add_right_cancel' b h1)) i.2 j.2)
  calc ∑ j : Fin n, g (a * j + b) = ∑ j : Fin n, g (e j) :=
        Finset.sum_congr rfl fun j _ => hmod _
    _ = ∑ j : Fin n, g j := (Finite.injective_iff_bijective.1 he).sum_comp (fun j : Fin n => g j)

/-- `Σ_{j<n} |cos(φ + jπ/n)| ≤ csc(π/(2n))`. -/
theorem sum_abs_cos_le (hn : n ≠ 0) (φ : ℝ) :
    ∑ j : Fin n, |Real.cos (φ + j * Real.pi / n)| ≤ cscN n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hp : 0 < Real.pi / n := div_pos Real.pi_pos hn'
  let F : ℝ → ℝ := fun ψ => ∑ j : Fin n, |Real.cos (ψ + j * Real.pi / n)|
  have hshift : ∀ (ψ : ℝ) (b : ℕ), F (ψ + b * (Real.pi / n)) = F ψ := by
    intro ψ b
    have h := sum_fin_affine (n := n) (fun t : ℕ => |Real.cos (ψ + t * Real.pi / n)|)
      (fun t => by
        rw [show ψ + ((t + n : ℕ) : ℝ) * Real.pi / n = ψ + t * Real.pi / n + Real.pi by
          push_cast
          field_simp
          ring, Real.cos_add_pi, abs_neg]) (Nat.coprime_one_left n) b
    refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h
    congr 2
    push_cast
    ring
  have hpi : ∀ (ψ : ℝ) (q : ℤ), F (ψ + q * Real.pi) = F ψ := by
    intro ψ q
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show ψ + q * Real.pi + j * Real.pi / n = ψ + j * Real.pi / n + q * Real.pi by ring,
      Real.cos_add_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul]
  set ψ := toIcoMod hp (-(Real.pi / 2)) φ with hψdef
  have hψ := toIcoMod_mem_Ico hp (-(Real.pi / 2)) φ
  rw [← hψdef] at hψ
  set m := toIcoDiv hp (-(Real.pi / 2)) φ
  have hφ : φ = ψ + (m % n).toNat * (Real.pi / n) + (m / n : ℤ) * Real.pi := by
    have h1 := toIcoMod_add_toIcoDiv_zsmul hp (-(Real.pi / 2)) φ
    rw [← hψdef, zsmul_eq_mul] at h1
    have h2 : ((m % n).toNat : ℝ) = ((m % n : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hn))
    have h3 : (m : ℝ) = (m % n : ℤ) + n * (m / n : ℤ) := by
      rw [Int.emod_def]
      push_cast
      ring
    rw [h2, ← h1, h3]
    field_simp
    ring
  have hF : F φ = F ψ := by
    rw [hφ, hpi, hshift]
  have hcos : ∀ j : Fin n, 0 ≤ Real.cos (ψ + j * Real.pi / n) := fun j => by
    refine Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩
    · have : 0 ≤ (j : ℝ) * Real.pi / n := by positivity
      linarith [hψ.1]
    · have hj : (j : ℝ) + 1 ≤ n := by exact_mod_cast j.2
      have : (j : ℝ) * Real.pi / n ≤ Real.pi - Real.pi / n := by
        rw [div_le_iff₀ hn', sub_mul, div_mul_cancel₀ _ hn'.ne']
        nlinarith [Real.pi_pos]
      linarith [hψ.2]
  have hh : 0 < Real.sin (Real.pi / (2 * n)) := by
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos, (by exact_mod_cast Nat.pos_of_ne_zero hn : (1 : ℝ) ≤ n)]
  have htel : Real.sin (Real.pi / (2 * n)) * ∑ j : Fin n, Real.cos (ψ + j * Real.pi / n) =
      -Real.sin (ψ - Real.pi / (2 * n)) := by
    let f : ℕ → ℝ := fun j => Real.sin (ψ - Real.pi / (2 * n) + j * Real.pi / n)
    have hstep : ∀ j : ℕ, f (j + 1) - f j =
        2 * (Real.sin (Real.pi / (2 * n)) * Real.cos (ψ + j * Real.pi / n)) := fun j => by
      simp only [f]
      rw [show ψ - Real.pi / (2 * n) + ((j + 1 : ℕ) : ℝ) * Real.pi / n =
          (ψ + j * Real.pi / n) + Real.pi / (2 * n) by push_cast; field_simp; ring,
        show ψ - Real.pi / (2 * n) + (j : ℝ) * Real.pi / n =
          (ψ + j * Real.pi / n) - Real.pi / (2 * n) by ring, Real.sin_add, Real.sin_sub]
      ring
    have hsum := Finset.sum_range_sub f n
    rw [Finset.sum_congr rfl fun j _ => hstep j, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
    have hfn : f n = -Real.sin (ψ - Real.pi / (2 * n)) := by
      simp only [f]
      rw [mul_div_cancel_left₀ _ hn'.ne', Real.sin_add_pi]
    rw [Fin.sum_univ_eq_sum_range (fun j => Real.cos (ψ + j * Real.pi / n)), Finset.mul_sum]
    rw [Finset.mul_sum] at hsum
    have hf0 : f 0 = Real.sin (ψ - Real.pi / (2 * n)) := by simp [f]
    linarith
  calc ∑ j : Fin n, |Real.cos (φ + j * Real.pi / n)| = F φ := rfl
    _ = ∑ j : Fin n, Real.cos (ψ + j * Real.pi / n) := by
        rw [hF]
        exact Finset.sum_congr rfl fun j _ => abs_of_nonneg (hcos j)
    _ ≤ cscN n := by
        rw [cscN, le_div_iff₀ hh, mul_comm, htel]
        linarith [Real.neg_one_le_sin (ψ - Real.pi / (2 * n))]

/-- For `n = 2^ℓ` and `θ = (2k+1)π/n`: `Σ_{j<n} |cos(jθ - φ)| ≤ csc(π/(2n))`
[ZKLY26, p. 18, l. 569]. -/
theorem sum_abs_cos_root_le {ℓ : ℕ} (hn : n = 2 ^ ℓ) (k : ℕ) (φ : ℝ) :
    ∑ j : Fin n, |Real.cos (j * ((2 * k + 1) * Real.pi / n) - φ)| ≤ cscN n := by
  have hn0 : n ≠ 0 := by
    rw [hn]
    positivity
  have hcop : (2 * k + 1).Coprime n := by
    rw [hn]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 (odd_two_mul_add_one k))
  have h := sum_fin_affine (n := n) (fun t : ℕ => |Real.cos (-φ + t * Real.pi / n)|)
    (fun t => by
      rw [show -φ + ((t + n : ℕ) : ℝ) * Real.pi / n = -φ + t * Real.pi / n + Real.pi by
        push_cast
        field_simp
        ring, Real.cos_add_pi, abs_neg]) hcop 0
  refine le_of_eq_of_le (Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h)
    (sum_abs_cos_le hn0 (-φ))
  congr 2
  push_cast
  ring

/-- **Coefficient-to-evaluation bound** [ZKLY26, p. 18, l. 567-569]: for `n = 2^ℓ` and real
coefficients `|x_j| ≤ M`, `|x(ζ^{2k+1})| ≤ M csc(π/(2n))`. -/
theorem norm_sum_mul_root_pow_le {ℓ : ℕ} (hn : n = 2 ^ ℓ) (k : ℕ) (x : Fin n → ℝ) {M : ℝ}
    (hx : ∀ j, |x j| ≤ M) :
    ‖∑ j : Fin n, (x j : ℂ) * root n k ^ (j : ℕ)‖ ≤ M * cscN n := by
  have hn0 : 0 < n := by
    rw [hn]
    positivity
  have hM : 0 ≤ M := (abs_nonneg _).trans (hx ⟨0, hn0⟩)
  set z := ∑ j : Fin n, (x j : ℂ) * root n k ^ (j : ℕ)
  set a := Complex.arg z
  have key : ‖z‖ = ∑ j : Fin n, x j * Real.cos (j * ((2 * k + 1) * Real.pi / n) - a) := by
    have h1 : (‖z‖ : ℂ) = Complex.exp (-(a : ℂ) * Complex.I) * z := by
      conv_rhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
      rw [mul_left_comm, ← Complex.exp_add, neg_mul, neg_add_cancel, Complex.exp_zero, mul_one]
    have h2 := congrArg Complex.re h1
    rw [Complex.ofReal_re] at h2
    rw [h2, Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [root, ← Complex.exp_nat_mul, mul_left_comm, ← Complex.exp_add,
      show -(a : ℂ) * Complex.I + (j : ℕ) * ((((2 * k + 1) * Real.pi / n : ℝ) : ℂ) * Complex.I) =
        (((j : ℕ) * ((2 * k + 1) * Real.pi / n) - a : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  rw [key]
  calc ∑ j : Fin n, x j * Real.cos (j * ((2 * k + 1) * Real.pi / n) - a)
      ≤ ∑ j : Fin n, M * |Real.cos (j * ((2 * k + 1) * Real.pi / n) - a)| :=
        Finset.sum_le_sum fun j _ => (le_abs_self _).trans (by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hx j) (abs_nonneg _))
    _ = M * ∑ j : Fin n, |Real.cos (j * ((2 * k + 1) * Real.pi / n) - a)| := by
        rw [Finset.mul_sum]
    _ ≤ M * cscN n := mul_le_mul_of_nonneg_left (sum_abs_cos_root_le hn k a) hM

/-- The coefficient-to-evaluation bound at the embeddings: `|φ_k(x)| ≤ ‖x‖∞ csc(π/(2n))`. -/
theorem norm_emb_ofCoeffs_le {ℓ : ℕ} (hn : n = 2 ^ ℓ) (k : Fin n) (x : Fin n → ℝ) {M : ℝ}
    (hx : ∀ j, |x j| ≤ M) : ‖emb k (ofCoeffs x)‖ ≤ M * cscN n := by
  rw [emb_ofCoeffs]
  exact norm_sum_mul_root_pow_le hn k x hx

/-- Parseval: `Σ_k |φ_k(x)|² = n Σ_j x_j²` [ZKLY26, p. 3, l. 130]. -/
theorem sum_norm_sq_emb_ofCoeffs (x : Fin n → ℝ) :
    ∑ k : Fin n, ‖emb k (ofCoeffs x)‖ ^ 2 = n * ∑ j : Fin n, x j ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hρ := isPrimitiveRoot_rho hn.ne'
  have hρ0 : rho n ≠ 0 := Complex.exp_ne_zero _
  have hρ2 : IsPrimitiveRoot (rho n ^ 2) n := hρ.pow (by omega) rfl
  have orth : ∀ i j : Fin n, ∑ k : Fin n,
      rho n ^ ((2 * (k : ℕ) + 1) * (i : ℕ)) * (rho n ^ ((2 * (k : ℕ) + 1) * (j : ℕ)))⁻¹ =
        if i = j then (n : ℂ) else 0 := by
    intro i j
    set u := (rho n ^ 2) ^ (i : ℕ) * ((rho n ^ 2) ^ (j : ℕ))⁻¹
    have hterm : ∀ k : ℕ, rho n ^ ((2 * k + 1) * (i : ℕ)) * (rho n ^ ((2 * k + 1) * (j : ℕ)))⁻¹ =
        rho n ^ (i : ℕ) * (rho n ^ (j : ℕ))⁻¹ * u ^ k := fun k => by
      simp only [u]
      ring
    rw [Fin.sum_univ_eq_sum_range (fun k => rho n ^ ((2 * k + 1) * (i : ℕ)) *
      (rho n ^ ((2 * k + 1) * (j : ℕ)))⁻¹) n, Finset.sum_congr rfl fun k _ => hterm k,
      ← Finset.mul_sum]
    split_ifs with hij
    · subst hij
      simp [u, hρ0]
    · have hu1 : u ≠ 1 := by
        intro h
        apply hij
        have h' : (rho n ^ 2) ^ (i : ℕ) = (rho n ^ 2) ^ (j : ℕ) := by
          simp only [u] at h
          exact (mul_inv_eq_one₀ (pow_ne_zero _ (pow_ne_zero _ hρ0))).1 h
        exact Fin.ext (hρ2.pow_inj i.2 j.2 h')
      have hun : u ^ n = 1 := by
        simp only [u]
        rw [mul_pow, inv_pow, pow_right_comm _ (i : ℕ) n, pow_right_comm _ (j : ℕ) n,
          hρ2.pow_eq_one, one_pow, one_pow, inv_one, mul_one]
      rw [geom_sum_eq hu1, hun, sub_self, zero_div, mul_zero]
  have hz : ∀ k : Fin n, emb k (ofCoeffs x) * starRingEnd ℂ (emb k (ofCoeffs x)) =
      ∑ i : Fin n, ∑ j : Fin n, (x i : ℂ) * x j *
        (rho n ^ ((2 * (k : ℕ) + 1) * (i : ℕ)) * (rho n ^ ((2 * (k : ℕ) + 1) * (j : ℕ)))⁻¹) := by
    intro k
    rw [emb_ofCoeffs, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, Complex.conj_ofReal, map_pow, conj_root, root_eq_rho_pow, inv_pow, ← pow_mul,
      ← pow_mul]
    ring
  have hsum : ∑ k : Fin n, emb k (ofCoeffs x) * starRingEnd ℂ (emb k (ofCoeffs x)) =
      ((n * ∑ j : Fin n, x j ^ 2 : ℝ) : ℂ) := by
    simp_rw [hz]
    calc ∑ k : Fin n, ∑ i : Fin n, ∑ j : Fin n, (x i : ℂ) * x j *
          (rho n ^ ((2 * (k : ℕ) + 1) * (i : ℕ)) * (rho n ^ ((2 * (k : ℕ) + 1) * (j : ℕ)))⁻¹)
        = ∑ i : Fin n, ∑ j : Fin n, (x i : ℂ) * x j * ∑ k : Fin n,
          (rho n ^ ((2 * (k : ℕ) + 1) * (i : ℕ)) * (rho n ^ ((2 * (k : ℕ) + 1) * (j : ℕ)))⁻¹) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm
      _ = ((n * ∑ j : Fin n, x j ^ 2 : ℝ) : ℂ) := by
          simp only [orth, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
          push_cast
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
  have h := congrArg Complex.re hsum
  rw [Complex.ofReal_re, Complex.re_sum] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]

/-! ### `2 × 2` complex matrices: norms through `ℂ²` vectors -/

/-- Lagrange's identity in `ℂ²`. -/
theorem normSq_lagrange (a b c d : ℂ) :
    (Complex.normSq a + Complex.normSq b) * (Complex.normSq c + Complex.normSq d) =
      Complex.normSq (starRingEnd ℂ a * c + starRingEnd ℂ b * d) +
        Complex.normSq (a * d - b * c) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  ring

namespace CMat

/-- `‖v‖² = |v₀|² + |v₁|²` for `v ∈ ℂ²`. -/
noncomputable def vecNormSq (v : Fin 2 → ℂ) : ℝ := Complex.normSq (v 0) + Complex.normSq (v 1)

/-- `(-conj v₁, conj v₀)`: orthogonal to `v`, with the same norm. -/
noncomputable def perp (v : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ![-starRingEnd ℂ (v 1), starRingEnd ℂ (v 0)]

/-- `‖v‖² ≥ 0`. -/
theorem vecNormSq_nonneg (v : Fin 2 → ℂ) : 0 ≤ vecNormSq v :=
  add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

/-- `‖v‖² > 0` for `v ≠ 0`. -/
theorem vecNormSq_pos {v : Fin 2 → ℂ} (hv : v ≠ 0) : 0 < vecNormSq v := by
  rcases (vecNormSq_nonneg v).eq_or_lt with h | h
  · refine absurd ?_ hv
    have h0 := Complex.normSq_nonneg (v 0)
    have h1 := Complex.normSq_nonneg (v 1)
    have e0 : Complex.normSq (v 0) = 0 := by unfold vecNormSq at h; linarith
    have e1 : Complex.normSq (v 1) = 0 := by unfold vecNormSq at h; linarith
    funext i
    fin_cases i
    · exact Complex.normSq_eq_zero.1 e0
    · exact Complex.normSq_eq_zero.1 e1
  · exact h

/-- `‖cv‖² = |c|² ‖v‖²`. -/
theorem vecNormSq_smul (c : ℂ) (v : Fin 2 → ℂ) :
    vecNormSq (c • v) = Complex.normSq c * vecNormSq v := by
  simp only [vecNormSq, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul]
  ring

/-- `‖v^⊥‖ = ‖v‖`. -/
theorem vecNormSq_perp (v : Fin 2 → ℂ) : vecNormSq (perp v) = vecNormSq v := by
  simp only [vecNormSq, perp, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.normSq_neg,
    Complex.normSq_conj]
  ring

/-- The Euclidean norm on `ℂ²` is `vecNormSq`. -/
theorem norm_sq_eq_vecNormSq (x : EuclideanSpace ℂ (Fin 2)) :
    ‖x‖ ^ 2 = vecNormSq (WithLp.ofLp x) := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Complex.sq_norm, Complex.sq_norm]
  rfl

/-- `‖Mx‖² = vecNormSq (M *ᵥ x)`. -/
theorem norm_toEuclideanLin_sq (M : CMat) (x : EuclideanSpace ℂ (Fin 2)) :
    ‖Matrix.toEuclideanLin M x‖ ^ 2 = vecNormSq (M *ᵥ WithLp.ofLp x) :=
  norm_sq_eq_vecNormSq _

/-- `‖M‖_F ≥ 0`. -/
theorem frob_nonneg (M : CMat) : 0 ≤ frob M := Real.sqrt_nonneg _

/-- `‖M‖_F² = Σᵢⱼ |Mᵢⱼ|²`. -/
theorem frob_sq (M : CMat) : frob M ^ 2 = ∑ i, ∑ j, ‖M i j‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- `‖Mv‖² + ‖M v^⊥‖² = ‖M‖_F² ‖v‖²`. -/
theorem vecNormSq_add_perp (M : CMat) (v : Fin 2 → ℂ) :
    vecNormSq (M *ᵥ v) + vecNormSq (M *ᵥ perp v) = frob M ^ 2 * vecNormSq v := by
  rw [frob_sq]
  simp only [vecNormSq, perp, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Complex.sq_norm, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.conj_re, Complex.conj_im]
  ring

/-- `|det M|² ‖v‖⁴ ≤ ‖Mv‖² ‖M v^⊥‖²`. -/
theorem normSq_det_mul_le (M : CMat) (v : Fin 2 → ℂ) :
    Complex.normSq M.det * vecNormSq v ^ 2 ≤ vecNormSq (M *ᵥ v) * vecNormSq (M *ᵥ perp v) := by
  have hdet : (M *ᵥ v) 0 * (M *ᵥ perp v) 1 - (M *ᵥ v) 1 * (M *ᵥ perp v) 0 =
      M.det * (vecNormSq v : ℂ) := by
    simp only [vecNormSq, Complex.ofReal_add, Complex.normSq_eq_conj_mul_self, perp,
      Matrix.det_fin_two, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    ring
  have h := normSq_lagrange ((M *ᵥ v) 0) ((M *ᵥ v) 1) ((M *ᵥ perp v) 0) ((M *ᵥ perp v) 1)
  rw [hdet, Complex.normSq_mul, Complex.normSq_ofReal] at h
  have h0 := Complex.normSq_nonneg (starRingEnd ℂ ((M *ᵥ v) 0) * (M *ᵥ perp v) 0 +
    starRingEnd ℂ ((M *ᵥ v) 1) * (M *ᵥ perp v) 1)
  simp only [vecNormSq] at h ⊢
  nlinarith [h, h0]

/-- **Upper bound from Frobenius norm and determinant.** If `‖M‖_F² ≤ T ≤ 2B` and
`TB ≤ B² + |det M|²`, then `‖Mv‖² ≤ B ‖v‖²`. -/
theorem vecNormSq_mulVec_le_of_frob (M : CMat) {T B : ℝ} (hF : frob M ^ 2 ≤ T) (hT : T ≤ 2 * B)
    (hB : T * B ≤ B ^ 2 + Complex.normSq M.det) (v : Fin 2 → ℂ) :
    vecNormSq (M *ᵥ v) ≤ B * vecNormSq v := by
  have h1 := vecNormSq_add_perp M v
  have h2 := normSq_det_mul_le M v
  have hS := vecNormSq_nonneg v
  have hF0 : 0 ≤ frob M ^ 2 := sq_nonneg _
  have hB0 : 0 ≤ B := by linarith
  by_contra hc
  replace hc := not_le.1 hc
  set m := vecNormSq (M *ᵥ v)
  set m' := vecNormSq (M *ᵥ perp v)
  set S := vecNormSq v
  set F := frob M ^ 2
  set D := Complex.normSq M.det
  have e1 : m * m' = B * S * (F * S - B * S) - (m - B * S) * (m + B * S - F * S) := by
    rw [show m' = F * S - m by linarith]
    ring
  have hFS : F * S ≤ T * S := mul_le_mul_of_nonneg_right hF hS
  have hTS : T * S ≤ 2 * B * S := mul_le_mul_of_nonneg_right hT hS
  have e2 : 0 < (m - B * S) * (m + B * S - F * S) := mul_pos (by linarith) (by linarith)
  have e3 : B * S * (F * S - B * S) ≤ S ^ 2 * D := by
    have h3 : F * B ≤ T * B := mul_le_mul_of_nonneg_right hF hB0
    nlinarith [mul_le_mul_of_nonneg_left h3 (sq_nonneg S),
      mul_le_mul_of_nonneg_left hB (sq_nonneg S)]
  linarith

/-- **Lower bound from Frobenius norm and determinant**: `|det M|² ‖v‖² ≤ B ‖Mv‖²` under the
hypotheses of `vecNormSq_mulVec_le_of_frob`. -/
theorem normSq_det_mul_le_of_frob (M : CMat) {T B : ℝ} (hF : frob M ^ 2 ≤ T) (hT : T ≤ 2 * B)
    (hB : T * B ≤ B ^ 2 + Complex.normSq M.det) (v : Fin 2 → ℂ) :
    Complex.normSq M.det * vecNormSq v ≤ B * vecNormSq (M *ᵥ v) := by
  have hup := vecNormSq_mulVec_le_of_frob M hF hT hB (perp v)
  rw [vecNormSq_perp] at hup
  have h2 := normSq_det_mul_le M v
  have hS := vecNormSq_nonneg v
  have hm := vecNormSq_nonneg (M *ᵥ v)
  have hB0 : 0 ≤ B := by nlinarith [sq_nonneg (frob M)]
  rcases hS.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    exact mul_nonneg hB0 hm
  · refine le_of_mul_le_mul_left ?_ hpos
    nlinarith [mul_le_mul_of_nonneg_left hup hm]

/-- `σ_max(M) ≥ 0`. -/
theorem sigmaMax_nonneg (M : CMat) : 0 ≤ sigmaMax M := norm_nonneg _

/-- `σ_max(M) ≤ c` if `‖Mv‖² ≤ c² ‖v‖²` for every `v`. -/
theorem sigmaMax_le_of {M : CMat} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ v, vecNormSq (M *ᵥ v) ≤ c ^ 2 * vecNormSq v) : sigmaMax M ≤ c := by
  rw [sigmaMax, Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow, norm_sq_eq_vecNormSq,
    norm_sq_eq_vecNormSq]
  exact h (WithLp.ofLp x)

/-- `‖Mv‖² ≤ σ_max(M)² ‖v‖²`. -/
theorem vecNormSq_mulVec_le (M : CMat) (v : Fin 2 → ℂ) :
    vecNormSq (M *ᵥ v) ≤ sigmaMax M ^ 2 * vecNormSq v := by
  have h := ((Matrix.toEuclideanLin (𝕜 := ℂ)).trans LinearMap.toContinuousLinearMap M).le_opNorm
    (WithLp.toLp 2 v)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, norm_sq_eq_vecNormSq, norm_sq_eq_vecNormSq] at h2
  exact h2

/-- `σ_max(Mᴴ) = σ_max(M)`. -/
theorem sigmaMax_conjTranspose (M : CMat) : sigmaMax Mᴴ = sigmaMax M :=
  Matrix.l2_opNorm_conjTranspose M

/-- `σ_max(MN) ≤ σ_max(M) σ_max(N)`. -/
theorem sigmaMax_mul_le (M N : CMat) : sigmaMax (M * N) ≤ sigmaMax M * sigmaMax N :=
  norm_mul_le M N

/-- `σ_max(M + N) ≤ σ_max(M) + σ_max(N)`. -/
theorem sigmaMax_add_le (M N : CMat) : sigmaMax (M + N) ≤ sigmaMax M + sigmaMax N :=
  norm_add_le M N

/-- `σ_max(M - N) ≤ σ_max(M) + σ_max(N)`. -/
theorem sigmaMax_sub_le (M N : CMat) : sigmaMax (M - N) ≤ sigmaMax M + sigmaMax N :=
  norm_sub_le M N

/-- `σ_max(r I) = |r|`. -/
theorem sigmaMax_smul_one (r : ℝ) : sigmaMax ((r : ℂ) • (1 : CMat)) = |r| := by
  rw [sigmaMax, norm_smul, CStarRing.norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs]

private theorem sphere_nonempty' : Nonempty (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :=
  (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype

private theorem exists_unit (v : Fin 2 → ℂ) (hv : vecNormSq v ≠ 0) :
    ∃ x : Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1, ∃ c : ℂ,
      WithLp.ofLp (x : EuclideanSpace ℂ (Fin 2)) = c • v ∧ Complex.normSq c * vecNormSq v = 1 := by
  set r := (√(vecNormSq v))⁻¹
  have hc : Complex.normSq (r : ℂ) * vecNormSq v = 1 := by
    rw [Complex.normSq_ofReal, ← sq, inv_pow, Real.sq_sqrt (vecNormSq_nonneg v)]
    exact inv_mul_cancel₀ hv
  have hx : ‖WithLp.toLp 2 ((r : ℂ) • v)‖ ^ 2 = 1 := by
    rw [norm_sq_eq_vecNormSq]
    exact (vecNormSq_smul _ _).trans hc
  exact ⟨⟨WithLp.toLp 2 ((r : ℂ) • v), mem_sphere_zero_iff_norm.2
    ((pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hx)⟩, r, rfl, hc⟩

/-- `σ_min(M) ≥ 0`. -/
theorem sigmaMin_nonneg (M : CMat) : 0 ≤ sigmaMin M := by
  have := sphere_nonempty'
  exact le_ciInf fun _ => norm_nonneg _

/-- `c ≤ σ_min(M)` if `c² ‖v‖² ≤ ‖Mv‖²` for every `v`. -/
theorem le_sigmaMin_of {M : CMat} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ v, c ^ 2 * vecNormSq v ≤ vecNormSq (M *ᵥ v)) : c ≤ sigmaMin M := by
  have := sphere_nonempty'
  refine le_ciInf fun x => ?_
  have hx : ‖(x : EuclideanSpace ℂ (Fin 2))‖ = 1 := mem_sphere_zero_iff_norm.1 x.2
  rw [← sq_le_sq₀ hc (norm_nonneg _), norm_toEuclideanLin_sq]
  have h1 := h (WithLp.ofLp (x : EuclideanSpace ℂ (Fin 2)))
  rwa [← norm_sq_eq_vecNormSq, hx, one_pow, mul_one] at h1

/-- `σ_min(M)² ‖v‖² ≤ ‖Mv‖²`. -/
theorem sigmaMin_sq_mul_le (M : CMat) (v : Fin 2 → ℂ) :
    sigmaMin M ^ 2 * vecNormSq v ≤ vecNormSq (M *ᵥ v) := by
  by_cases hv : vecNormSq v = 0
  · rw [hv, mul_zero]
    exact vecNormSq_nonneg _
  obtain ⟨x, c, hx, hc⟩ := exists_unit v hv
  have h1 : sigmaMin M ≤ ‖Matrix.toEuclideanLin M x‖ :=
    ciInf_le ⟨0, by rintro _ ⟨y, rfl⟩; exact norm_nonneg _⟩ x
  have h2 : sigmaMin M ^ 2 ≤ Complex.normSq c * vecNormSq (M *ᵥ v) := by
    rw [← vecNormSq_smul, ← Matrix.mulVec_smul, ← hx, ← norm_toEuclideanLin_sq]
    exact pow_le_pow_left₀ (sigmaMin_nonneg M) h1 2
  calc sigmaMin M ^ 2 * vecNormSq v
      ≤ Complex.normSq c * vecNormSq (M *ᵥ v) * vecNormSq v :=
        mul_le_mul_of_nonneg_right h2 (vecNormSq_nonneg v)
    _ = vecNormSq (M *ᵥ v) := by linear_combination vecNormSq (M *ᵥ v) * hc

/-- `v* v = ‖v‖²`. -/
theorem star_dotProduct_self (w : Fin 2 → ℂ) : star w ⬝ᵥ w = (vecNormSq w : ℂ) := by
  simp [dotProduct, Fin.sum_univ_two, vecNormSq, Complex.normSq_eq_conj_mul_self]

/-- `v* N Nᴴ v = ‖Nᴴ v‖²`. -/
theorem star_dotProduct_mul_conjTranspose (N : CMat) (v : Fin 2 → ℂ) :
    star v ⬝ᵥ ((N * Nᴴ) *ᵥ v) = (vecNormSq (Nᴴ *ᵥ v) : ℂ) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← star_dotProduct_self]
  congr 1
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]

private theorem re_inner_toEuclideanLin (M : CMat) (x : EuclideanSpace ℂ (Fin 2)) :
    (inner ℂ x (Matrix.toEuclideanLin M x)).re =
      (star (WithLp.ofLp x) ⬝ᵥ (M *ᵥ WithLp.ofLp x)).re := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rfl

/-- `λ_max(M) ≤ c` if `Re(v* M v) ≤ c ‖v‖²` for every `v`. -/
theorem lambdaMax_le_of {M : CMat} {c : ℝ}
    (h : ∀ v, (star v ⬝ᵥ (M *ᵥ v)).re ≤ c * vecNormSq v) : lambdaMax M ≤ c := by
  have := sphere_nonempty'
  refine ciSup_le fun x => ?_
  have hx : ‖(x : EuclideanSpace ℂ (Fin 2))‖ = 1 := mem_sphere_zero_iff_norm.1 x.2
  rw [re_inner_toEuclideanLin]
  have h1 := h (WithLp.ofLp (x : EuclideanSpace ℂ (Fin 2)))
  rwa [← norm_sq_eq_vecNormSq, hx, one_pow, mul_one] at h1

private theorem rayleigh_le (M : CMat) (y : Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :
    (inner ℂ (y : EuclideanSpace ℂ (Fin 2)) (Matrix.toEuclideanLin M y)).re ≤ sigmaMax M := by
  have hy : ‖(y : EuclideanSpace ℂ (Fin 2))‖ = 1 := mem_sphere_zero_iff_norm.1 y.2
  refine (re_inner_le_norm (𝕜 := ℂ) (y : EuclideanSpace ℂ (Fin 2))
    (Matrix.toEuclideanLin M y)).trans ?_
  rw [hy, one_mul]
  have h := ((Matrix.toEuclideanLin (𝕜 := ℂ)).trans LinearMap.toContinuousLinearMap M).le_opNorm
    (y : EuclideanSpace ℂ (Fin 2))
  rw [hy, mul_one] at h
  exact h

/-- `Re(v* M v) ≤ λ_max(M)` for a unit vector `v`. -/
theorem le_lambdaMax (M : CMat) (v : Fin 2 → ℂ) (hv : vecNormSq v = 1) :
    (star v ⬝ᵥ (M *ᵥ v)).re ≤ lambdaMax M := by
  have hx : ‖WithLp.toLp 2 v‖ = 1 := by
    refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 ?_
    rw [norm_sq_eq_vecNormSq]
    exact hv
  refine le_ciSup_of_le ⟨sigmaMax M, ?_⟩ ⟨WithLp.toLp 2 v, mem_sphere_zero_iff_norm.2 hx⟩
    (by rw [re_inner_toEuclideanLin])
  rintro _ ⟨y, rfl⟩
  exact rayleigh_le M y

/-- `λ_max(M) ≤ σ_max(M)`. -/
theorem lambdaMax_le_sigmaMax (M : CMat) : lambdaMax M ≤ sigmaMax M := by
  have := sphere_nonempty'
  exact ciSup_le fun y => rayleigh_le M y

/-- `λ_max(NN* + I) = 1 + σ_max(N)²`. -/
theorem lambdaMax_mul_conjTranspose_add_one (N : CMat) :
    lambdaMax (N * Nᴴ + 1) = 1 + sigmaMax N ^ 2 := by
  have hval : ∀ v, (star v ⬝ᵥ ((N * Nᴴ + 1) *ᵥ v)).re = vecNormSq (Nᴴ *ᵥ v) + vecNormSq v :=
    fun v => by
      rw [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, star_dotProduct_mul_conjTranspose,
        star_dotProduct_self, Complex.add_re, Complex.ofReal_re, Complex.ofReal_re]
  apply le_antisymm
  · refine lambdaMax_le_of fun v => ?_
    rw [hval]
    have h := vecNormSq_mulVec_le Nᴴ v
    rw [sigmaMax_conjTranspose] at h
    linarith
  · obtain ⟨x, hxs, hmax⟩ := (isCompact_sphere (0 : EuclideanSpace ℂ (Fin 2)) 1).exists_isMaxOn
      (NormedSpace.sphere_nonempty.2 zero_le_one)
      ((LinearMap.continuous_of_finiteDimensional (Matrix.toEuclideanLin Nᴴ)).norm.pow
        2).continuousOn
    set g := ‖Matrix.toEuclideanLin Nᴴ x‖ ^ 2 with hg
    have hσ : sigmaMax N ≤ √g := by
      rw [← sigmaMax_conjTranspose]
      refine sigmaMax_le_of (Real.sqrt_nonneg _) fun v => ?_
      rw [Real.sq_sqrt (sq_nonneg _)]
      by_cases hv : vecNormSq v = 0
      · have h := vecNormSq_mulVec_le Nᴴ v
        rw [hv, mul_zero] at h ⊢
        exact h
      · obtain ⟨y, c, hy, hc⟩ := exists_unit v hv
        have h := isMaxOn_iff.1 hmax _ y.2
        simp only [Pi.pow_apply] at h
        rw [norm_toEuclideanLin_sq, hy, Matrix.mulVec_smul, vecNormSq_smul] at h
        calc vecNormSq (Nᴴ *ᵥ v)
            = Complex.normSq c * vecNormSq (Nᴴ *ᵥ v) * vecNormSq v := by
              linear_combination -(vecNormSq (Nᴴ *ᵥ v)) * hc
          _ ≤ g * vecNormSq v := mul_le_mul_of_nonneg_right h (vecNormSq_nonneg v)
    have hx1 : vecNormSq (WithLp.ofLp x) = 1 := by
      rw [← norm_sq_eq_vecNormSq, mem_sphere_zero_iff_norm.1 hxs, one_pow]
    have h := le_lambdaMax (N * Nᴴ + 1) (WithLp.ofLp x) hx1
    rw [hval, hx1, ← norm_toEuclideanLin_sq, ← hg] at h
    have h2 := pow_le_pow_left₀ (sigmaMax_nonneg N) hσ 2
    rw [Real.sq_sqrt (sq_nonneg _)] at h2
    linarith

/-- A lower-triangular matrix with entries at most `ε` has `σ_max ≤ ε (1 + √5)/2`. -/
theorem sigmaMax_le_of_lower (N : CMat) (h01 : N 0 1 = 0) {ε : ℝ} (hε : ∀ i j, ‖N i j‖ ≤ ε) :
    sigmaMax N ≤ (1 + √5) / 2 * ε := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hε 0 0)
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h52 : 2 ≤ √5 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  refine sigmaMax_le_of (by positivity) fun v => ?_
  set a := ‖v 0‖
  set b := ‖v 1‖
  have h0 : ‖N 0 0 * v 0 + N 0 1 * v 1‖ ≤ ε * a := by
    rw [h01, zero_mul, add_zero, norm_mul]
    exact mul_le_mul_of_nonneg_right (hε 0 0) (norm_nonneg _)
  have h1 : ‖N 1 0 * v 0 + N 1 1 * v 1‖ ≤ ε * a + ε * b := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul] <;>
      exact mul_le_mul_of_nonneg_right (hε _ _) (norm_nonneg _)
  have hid : ((1 + √5) / 2) ^ 2 * (a ^ 2 + b ^ 2) - a ^ 2 - (a + b) ^ 2 =
      ((1 + √5) / 2 - 1) * (a - (1 + √5) / 2 * b) ^ 2 := by
    linear_combination (a ^ 2 + 2 * a * b - ((1 + √5) / 2 - 1) * b ^ 2) / 4 * h5
  have hpos : 0 ≤ ((1 + √5) / 2 - 1) * (a - (1 + √5) / 2 * b) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have hv : vecNormSq v = a ^ 2 + b ^ 2 := by
    simp only [vecNormSq, a, b, Complex.sq_norm]
  have hNv : vecNormSq (N *ᵥ v) = ‖N 0 0 * v 0 + N 0 1 * v 1‖ ^ 2 +
      ‖N 1 0 * v 0 + N 1 1 * v 1‖ ^ 2 := by
    simp only [vecNormSq, Complex.sq_norm, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hNv, hv]
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have e0 := pow_le_pow_left₀ (norm_nonneg _) h0 2
  have e1 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [mul_le_mul_of_nonneg_left hpos (sq_nonneg ε)]

/-- `‖XY‖_F ≤ σ_max(X) ‖Y‖_F`. -/
theorem frob_mul_le (X Y : CMat) : frob (X * Y) ≤ sigmaMax X * frob Y := by
  have hcol : ∀ M : CMat, frob M ^ 2 = vecNormSq (fun i => M i 0) + vecNormSq (fun i => M i 1) :=
    fun M => by
      rw [frob_sq]
      simp only [Fin.sum_univ_two, vecNormSq, Complex.sq_norm]
      ring
  have hXY : ∀ j, (fun i => (X * Y) i j) = X *ᵥ (fun i => Y i j) := fun j => by
    funext i
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [← sq_le_sq₀ (frob_nonneg _) (mul_nonneg (sigmaMax_nonneg _) (frob_nonneg _)), mul_pow,
    hcol, hcol, hXY, hXY, mul_add]
  exact add_le_add (vecNormSq_mulVec_le _ _) (vecNormSq_mulVec_le _ _)

/-- `‖Mᴴ‖_F = ‖M‖_F`. -/
theorem frob_conjTranspose (M : CMat) : frob Mᴴ = frob M := by
  simp only [frob, Matrix.conjTranspose_apply, norm_star]
  rw [Finset.sum_comm]

/-- `‖XY‖_F ≤ ‖X‖_F σ_max(Y)`. -/
theorem frob_mul_le' (X Y : CMat) : frob (X * Y) ≤ frob X * sigmaMax Y := by
  rw [← frob_conjTranspose, Matrix.conjTranspose_mul, mul_comm, ← frob_conjTranspose X,
    ← sigmaMax_conjTranspose Y]
  exact frob_mul_le _ _

/-- `‖M‖_F` is the Euclidean norm of the entries. -/
theorem frob_eq_norm (M : CMat) :
    frob M = ‖WithLp.toLp 2 (fun p : Fin 2 × Fin 2 => M p.1 p.2)‖ := by
  rw [EuclideanSpace.norm_eq, Fintype.sum_prod_type]
  rfl

/-- `‖M + N‖_F ≤ ‖M‖_F + ‖N‖_F`. -/
theorem frob_add_le (M N : CMat) : frob (M + N) ≤ frob M + frob N := by
  rw [frob_eq_norm, frob_eq_norm, frob_eq_norm]
  exact norm_add_le (WithLp.toLp 2 fun p : Fin 2 × Fin 2 => M p.1 p.2)
    (WithLp.toLp 2 fun p : Fin 2 × Fin 2 => N p.1 p.2)

/-- `‖M - N‖_F ≤ ‖M‖_F + ‖N‖_F`. -/
theorem frob_sub_le (M N : CMat) : frob (M - N) ≤ frob M + frob N := by
  rw [frob_eq_norm, frob_eq_norm, frob_eq_norm]
  exact norm_sub_le (WithLp.toLp 2 fun p : Fin 2 × Fin 2 => M p.1 p.2)
    (WithLp.toLp 2 fun p : Fin 2 × Fin 2 => N p.1 p.2)

end CMat

namespace KMat

/-- `σ_max(φ_k(H)) ≤ ‖H‖₂`. -/
theorem sigmaMax_le_norm2 (H : KMat n) (k : Fin n) : CMat.sigmaMax (embM k H) ≤ norm2 H :=
  le_ciSup (f := fun k => CMat.sigmaMax (embM k H)) (Set.finite_range _).bddAbove k

/-- `‖H‖₂ ≤ c` if `σ_max(φ_k(H)) ≤ c` for every `k`. -/
theorem norm2_le_of (hn : 0 < n) {H : KMat n} {c : ℝ} (h : ∀ k, CMat.sigmaMax (embM k H) ≤ c) :
    norm2 H ≤ c :=
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  ciSup_le h

/-- `σ_min(H) ≤ σ_min(φ_k(H))`. -/
theorem sigmaMin_le (H : KMat n) (k : Fin n) : sigmaMin H ≤ CMat.sigmaMin (embM k H) :=
  ciInf_le (f := fun k => CMat.sigmaMin (embM k H)) (Set.finite_range _).bddBelow k

/-- `c ≤ σ_min(H)` if `c ≤ σ_min(φ_k(H))` for every `k`. -/
theorem le_sigmaMin_of (hn : 0 < n) {H : KMat n} {c : ℝ} (h : ∀ k, c ≤ CMat.sigmaMin (embM k H)) :
    c ≤ sigmaMin H :=
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  le_ciInf h

/-- `λ_max(H) ≤ c` if `λ_max(φ_k(H)) ≤ c` for every `k`. -/
theorem lambdaMax_le_of (hn : 0 < n) {H : KMat n} {c : ℝ}
    (h : ∀ k, CMat.lambdaMax (embM k H) ≤ c) : lambdaMax H ≤ c :=
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  ciSup_le h

/-- `λ_max(φ_k(H)) ≤ λ_max(H)`. -/
theorem le_lambdaMax (H : KMat n) (k : Fin n) : CMat.lambdaMax (embM k H) ≤ lambdaMax H :=
  le_ciSup (f := fun k => CMat.lambdaMax (embM k H)) (Set.finite_range _).bddAbove k

/-- `‖H‖_F ≥ 0`. -/
theorem normF_nonneg (H : KMat n) : 0 ≤ normF H := Real.sqrt_nonneg _

/-- `‖H‖_F² = Σ_k ‖φ_k(H)‖_F²`. -/
theorem normF_sq (H : KMat n) : normF H ^ 2 = ∑ k : Fin n, CMat.frob (embM k H) ^ 2 :=
  Real.sq_sqrt (by positivity)

end KMat

end Mitaka
