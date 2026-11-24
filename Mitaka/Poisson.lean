/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import LatticeCrypto.DiscreteGaussian
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # Gaussian Poisson summation over `ℤ^m` for a positive definite quadratic form

For a positive definite `V ∈ ℝ^{m×m}` and a shift `c ∈ ℝ^m`,
`Σ_{x ∈ ℤ^m} exp(−π (x − c)ᵗ V⁻¹ (x − c)) = det(V)^{1/2} Σ_{y ∈ ℤ^m} exp(−π yᵗ V y) e^{2πi⟨y, c⟩}`.

[ZKLY26] (ePrint 2026/2521) applies Poisson summation to Gaussian masses on `L(B)` (p. 8,
l. 247-249) and on `L(B)*` (p. 20, l. 640); it is the proof of Lemma 1 ([Pei10, Lemma 2.4],
p. 3, l. 106-107), a corollary of [MR04, Lemma 4.4]. Mathlib has the one-dimensional case
(`Complex.tsum_exp_neg_quadratic`).

Proof: induction on `m` with a phase `e^{2πi⟨w, x⟩}`. For `P = (d pᵗ; p P′)` positive definite,
`(t, x′)ᵗ P (t, x′) = d (t + ⟨p, x′⟩/d)² + x′ᵗ S x′` with the Schur complement
`S = P′ − ppᵗ/d ≻ 0` and `det P = d det S`; the sum over `t` is the one-dimensional formula, the
sum over `x′` the induction hypothesis for `S` with a shifted phase, and
`vᵗ P⁻¹ v = v₀²/d + (v′ − v₀p/d)ᵗ S⁻¹ (v′ − v₀p/d)` reassembles the dual sum.

* `summable_exp_neg_quadForm`: the Gaussian weights of a positive definite form are summable
  over `ℤ^m`.
* `tsum_exp_neg_quadForm_eq`: the identity above, over `ℂ`.
* `tsum_exp_neg_quadForm_eq_real`: its real form, with `cos(2π⟨y, c⟩)` in place of the phase. -/

@[expose] public section

open Real Complex
open scoped Matrix

namespace Mitaka.LatticeGaussian

variable {m : ℕ}

/-- An integer vector as a real vector. -/
def ofInt (z : Fin m → ℤ) : Fin m → ℝ := fun i => z i

/-- The quadratic form `xᵗ P x`. -/
def quadForm (P : Matrix (Fin m) (Fin m) ℝ) (x : Fin m → ℝ) : ℝ := x ⬝ᵥ (P *ᵥ x)

/-- `xᵗ P x > 0` for positive definite `P` and `x ≠ 0`. -/
theorem quadForm_pos {P : Matrix (Fin m) (Fin m) ℝ} (hP : P.PosDef) {x : Fin m → ℝ}
    (hx : x ≠ 0) : 0 < quadForm P x := by
  simpa [quadForm] using (Matrix.posDef_iff_dotProduct_mulVec.1 hP).2 hx

/-- `(-x)ᵗ P (-x) = xᵗ P x`. -/
theorem quadForm_neg (P : Matrix (Fin m) (Fin m) ℝ) (x : Fin m → ℝ) :
    quadForm P (-x) = quadForm P x := by
  simp [quadForm, Matrix.mulVec_neg]

private theorem ofInt_cons (t : ℤ) (x : Fin m → ℤ) :
    ofInt (Fin.cons t x : Fin (m + 1) → ℤ) = Fin.cons (t : ℝ) (ofInt x) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [ofInt]

private theorem cons_dotProduct_cons (a b : ℝ) (v w : Fin m → ℝ) :
    (Fin.cons a v : Fin (m + 1) → ℝ) ⬝ᵥ Fin.cons b w = a * b + v ⬝ᵥ w := by
  simp [dotProduct, Fin.sum_univ_succ]

private theorem cons_sub_cons (a b : ℝ) (v w : Fin m → ℝ) :
    (Fin.cons a v : Fin (m + 1) → ℝ) - Fin.cons b w = Fin.cons (a - b) (v - w) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-! ### The block decomposition of a symmetric matrix -/

section Blocks

variable (P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)

/-- The off-diagonal column `p` of `P = (d pᵗ; p P′)`. -/
private def blkP : Fin m → ℝ := fun i => P 0 i.succ

/-- The block `P′`. -/
private def blkQ : Matrix (Fin m) (Fin m) ℝ := P.submatrix Fin.succ Fin.succ

/-- The row `pᵗ` as a `1 × m` matrix. -/
private def blkRow : Matrix (Fin 1) (Fin m) ℝ := Matrix.of fun _ j => blkP P j

/-- The Schur complement `S = P′ − ppᵗ/d`. -/
private noncomputable def schur : Matrix (Fin m) (Fin m) ℝ :=
  blkQ P - (P 0 0)⁻¹ • Matrix.vecMulVec (blkP P) (blkP P)

variable {P}

private theorem quadForm_cons (hs : ∀ i j, P i j = P j i) (a : ℝ) (v : Fin m → ℝ) :
    quadForm P (Fin.cons a v) = P 0 0 * a ^ 2 + 2 * a * (blkP P ⬝ᵥ v) + quadForm (blkQ P) v := by
  have h1 : ∑ x : Fin m, v x * (P x.succ 0 * a) = a * ∑ x : Fin m, P 0 x.succ * v x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [hs]; ring
  simp only [quadForm, dotProduct, Matrix.mulVec, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    blkP, blkQ, Matrix.submatrix_apply, mul_add, Finset.sum_add_distrib, h1]
  ring

private theorem quadForm_vecMulVec (p v : Fin m → ℝ) :
    quadForm (Matrix.vecMulVec p p) v = (p ⬝ᵥ v) ^ 2 := by
  simp only [quadForm, dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem quadForm_schur (v : Fin m → ℝ) :
    quadForm (schur P) v = quadForm (blkQ P) v - (P 0 0)⁻¹ * (blkP P ⬝ᵥ v) ^ 2 := by
  rw [← quadForm_vecMulVec]
  simp only [quadForm, schur, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul]

private theorem quadForm_cons_eq (hs : ∀ i j, P i j = P j i) (hd : P 0 0 ≠ 0) (a : ℝ)
    (v : Fin m → ℝ) :
    quadForm P (Fin.cons a v) =
      P 0 0 * (a + blkP P ⬝ᵥ v / P 0 0) ^ 2 + quadForm (schur P) v := by
  rw [quadForm_cons hs, quadForm_schur]
  field_simp
  ring

private theorem quadForm_cons_sub (hs : ∀ i j, P i j = P j i) (hd : P 0 0 ≠ 0) (t : ℝ)
    (x : Fin m → ℝ) (c : Fin (m + 1) → ℝ) :
    quadForm P (Fin.cons t x - c) =
      P 0 0 * (t - (c 0 - blkP P ⬝ᵥ (x - Fin.tail c) / P 0 0)) ^ 2 +
        quadForm (schur P) (x - Fin.tail c) := by
  conv_lhs => rw [← Fin.cons_self_tail c, cons_sub_cons, quadForm_cons_eq hs hd]
  ring

private theorem symm_of_posDef (hP : P.PosDef) (i j : Fin (m + 1)) : P i j = P j i := by
  simpa using hP.1.apply j i

private theorem pos_of_posDef (hP : P.PosDef) : 0 < P 0 0 := by
  have h := quadForm_pos hP (x := Fin.cons 1 0) (by
    intro h; simpa using congrFun h 0)
  rw [quadForm_cons (symm_of_posDef hP)] at h
  simpa [quadForm] using h

/-- `Fin 1 ⊕ Fin m ≃ Fin (m + 1)`: `inl 0 ↦ 0`, `inr i ↦ i.succ`. -/
private def splitEquiv : Fin 1 ⊕ Fin m ≃ Fin (m + 1) :=
  finSumFinEquiv.trans (finCongr (Nat.add_comm 1 m))

private theorem splitEquiv_inl (i : Fin 1) : splitEquiv (m := m) (Sum.inl i) = 0 := by
  obtain rfl := Subsingleton.elim i 0
  ext
  simp [splitEquiv]

private theorem splitEquiv_inr (i : Fin m) : splitEquiv (Sum.inr i) = i.succ := by
  ext
  simp [splitEquiv]

/-- `P = (d pᵗ; p P′)` as a block matrix over `Fin 1 ⊕ Fin m`. -/
private theorem submatrix_splitEquiv (hs : ∀ i j, P i j = P j i) :
    P.submatrix splitEquiv splitEquiv =
      Matrix.fromBlocks (P 0 0 • (1 : Matrix (Fin 1) (Fin 1) ℝ)) (blkRow P) (blkRow P)ᴴ
        (blkQ P) := by
  ext (i | i) (j | j)
  · simp [splitEquiv_inl, Subsingleton.elim i j]
  · simp [splitEquiv_inl, splitEquiv_inr, blkRow, blkP]
  · simp [splitEquiv_inl, splitEquiv_inr, blkRow, blkP, hs i.succ 0]
  · simp [splitEquiv_inr, blkQ]

/-- The Schur complement of the block form is `schur P`. -/
private theorem schur_eq (hd : P 0 0 ≠ 0) :
    blkQ P - (blkRow P)ᴴ * (P 0 0 • (1 : Matrix (Fin 1) (Fin 1) ℝ))⁻¹ * blkRow P = schur P := by
  have h := Matrix.inv_smul' (Units.mk0 (P 0 0) hd) (A := (1 : Matrix (Fin 1) (Fin 1) ℝ))
    (by simp)
  simp only [Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, inv_one] at h
  rw [h, schur]
  ext i j
  simp [Matrix.mul_apply, Matrix.vecMulVec_apply, blkRow, blkP]
  ring

/-- `det P = d det S` (`Matrix.det_fromBlocks₁₁`). -/
private theorem det_eq_mul_det_schur (hP : P.PosDef) : P.det = P 0 0 * (schur P).det := by
  have hd := (pos_of_posDef hP).ne'
  let _ : Invertible (P 0 0 • (1 : Matrix (Fin 1) (Fin 1) ℝ)) :=
    Matrix.invertibleOfIsUnitDet _ (by simp [hd])
  rw [← Matrix.det_reindex_self splitEquiv.symm P, Matrix.reindex_apply, Equiv.symm_symm,
    submatrix_splitEquiv (symm_of_posDef hP), Matrix.det_fromBlocks₁₁,
    Matrix.invOf_eq_nonsing_inv, schur_eq hd]
  simp

/-- `S ≻ 0` (`Matrix.PosDef.fromBlocks₁₁`). -/
private theorem schur_posDef (hP : P.PosDef) : (schur P).PosDef := by
  have hd := pos_of_posDef hP
  let _ : Invertible (P 0 0 • (1 : Matrix (Fin 1) (Fin 1) ℝ)) :=
    Matrix.invertibleOfIsUnitDet _ (by simp [hd.ne'])
  have h := hP.submatrix splitEquiv.injective
  rw [submatrix_splitEquiv (symm_of_posDef hP)] at h
  have hS := (Matrix.PosDef.fromBlocks₁₁ _ _ (Matrix.PosDef.one.smul hd)).1 h.posSemidef
  rw [schur_eq hd.ne'] at hS
  refine hS.posDef_iff_det_ne_zero.2 fun h0 => hP.det_pos.ne' ?_
  rw [det_eq_mul_det_schur hP, h0, mul_zero]

private theorem quadForm_inv_cons (hP : P.PosDef) (a : ℝ) (v : Fin m → ℝ) :
    quadForm P⁻¹ (Fin.cons a v) =
      a ^ 2 / P 0 0 + quadForm (schur P)⁻¹ (v - (a / P 0 0) • blkP P) := by
  have hs := symm_of_posDef hP
  have hd := (pos_of_posDef hP).ne'
  have hSu : IsUnit (schur P).det := (schur_posDef hP).isUnit.map Matrix.detMonoidHom
  set z := P⁻¹ *ᵥ Fin.cons a v with hz
  have hPz : P *ᵥ z = Fin.cons a v := by
    rw [hz, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hP.isUnit.map Matrix.detMonoidHom),
      Matrix.one_mulVec]
  set z' : Fin m → ℝ := Fin.tail z
  have hzc : z = Fin.cons (z 0) z' := (Fin.cons_self_tail z).symm
  have h0 : P 0 0 * z 0 + blkP P ⬝ᵥ z' = a := by
    have := congrFun hPz 0
    rw [hzc] at this
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, blkP] using this
  have h1 : z 0 • blkP P + blkQ P *ᵥ z' = v := by
    funext i
    have := congrFun hPz i.succ
    rw [hzc] at this
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at this
    simpa [blkP, blkQ, Matrix.mulVec, dotProduct, hs i.succ 0, mul_comm] using this
  have hS : schur P *ᵥ z' = v - (a / P 0 0) • blkP P := by
    rw [schur, Matrix.sub_mulVec, Matrix.smul_mulVec, ← h1, ← h0]
    funext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec,
      Matrix.vecMulVec_apply, dotProduct]
    rw [show ∑ x, blkP P i * blkP P x * z' x = blkP P i * ∑ x, blkP P x * z' x by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring]
    field_simp
    ring
  have hz' : z' = (schur P)⁻¹ *ᵥ (v - (a / P 0 0) • blkP P) := by
    rw [← hS, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hSu, Matrix.one_mulVec]
  have hq : quadForm P⁻¹ (Fin.cons a v) = a * z 0 + v ⬝ᵥ z' := by
    rw [quadForm, ← hz]
    conv_lhs => rw [hzc]
    rw [cons_dotProduct_cons]
  have hz0 : z 0 = (a - blkP P ⬝ᵥ z') / P 0 0 := by
    field_simp; linarith
  rw [hq, quadForm, ← hz', hz0]
  simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul, dotProduct_comm (blkP P) z']
  field_simp
  ring

end Blocks

/-! ### One dimension -/

/-- The one-dimensional Gaussian weights `exp(−πd(t − a)²)`, `t ∈ ℤ`, are summable for `d > 0`. -/
theorem summable_exp_neg_sq {d : ℝ} (hd : 0 < d) (a : ℝ) :
    Summable fun t : ℤ => Real.exp (-π * d * ((t : ℝ) - a) ^ 2) := by
  have hσ : 0 < 1 / √(2 * π * d) := by positivity
  refine (LatticeCrypto.discreteGaussianSum_summable _ a hσ).congr fun t => ?_
  rw [LatticeCrypto.discreteGaussianWeight, div_pow, Real.sq_sqrt (by positivity)]
  congr 1
  field_simp

private theorem exists_tsum_exp_neg_sq_le {d : ℝ} (hd : 0 < d) :
    ∃ C, ∀ a : ℝ, ∑' t : ℤ, Real.exp (-π * d * ((t : ℝ) - a) ^ 2) ≤ C := by
  set σ := 1 / √(2 * π * d) with hσdef
  have hσ : 0 < σ := by positivity
  refine ⟨σ * √(2 * π) + σ * √(2 * π) *
    (2 / (1 - Real.exp (-2 * π ^ 2 * σ ^ 2)) * Real.exp (-2 * π ^ 2 * σ ^ 2)), fun a => ?_⟩
  have h := LatticeCrypto.abs_discreteGaussianSum_sub_le σ a hσ
  have he : LatticeCrypto.discreteGaussianSum σ a =
      ∑' t : ℤ, Real.exp (-π * d * ((t : ℝ) - a) ^ 2) := by
    refine tsum_congr fun t => ?_
    rw [LatticeCrypto.discreteGaussianWeight, hσdef, div_pow, Real.sq_sqrt (by positivity)]
    congr 1
    field_simp
  rw [← he]
  linarith [le_abs_self (LatticeCrypto.discreteGaussianSum σ a - σ * √(2 * π))]

/-- One-dimensional Poisson summation with shift and phase. -/
private theorem tsum_cexp_one {d : ℝ} (hd : 0 < d) (a w : ℝ) :
    ∑' t : ℤ, cexp (-π * d * ((t : ℂ) - a) ^ 2 + 2 * π * I * w * t) =
      ((√d)⁻¹ : ℝ) * ∑' k : ℤ, cexp (-π * ((k : ℂ) - w) ^ 2 / d - 2 * π * I * (k - w) * a) := by
  have ha : 0 < ((d : ℝ) : ℂ).re := by simpa using hd
  have h := Complex.tsum_exp_neg_quadratic ha (d * a + I * w)
  have hroot : ((d : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((√d : ℝ) : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hd.le,
      ← Real.sqrt_eq_rpow]
  have hd' : (d : ℂ) ≠ 0 := ofReal_ne_zero.2 hd.ne'
  have hL : ∀ t : ℤ, cexp (-π * d * ((t : ℂ) - a) ^ 2 + 2 * π * I * w * t) =
      cexp (-π * d * t ^ 2 + 2 * π * (d * a + I * w) * t) * cexp (-π * d * a ^ 2) := fun t => by
    rw [← Complex.exp_add]; congr 1; ring
  have hR : ∀ k : ℤ, cexp (-π / d * (k + I * (d * a + I * w)) ^ 2) * cexp (-π * d * a ^ 2) =
      cexp (-π * ((k : ℂ) - w) ^ 2 / d - 2 * π * I * (k - w) * a) := fun k => by
    rw [← Complex.exp_add]; congr 1
    field_simp
    ring_nf
    simp only [I_sq, show I ^ 3 = -I by rw [pow_succ, I_sq]; ring, Complex.I_pow_four]
    ring
  rw [tsum_congr hL, tsum_mul_right, h, hroot, ← tsum_congr hR, tsum_mul_right]
  push_cast
  ring

/-! ### Induction on the dimension -/

/-- The Gaussian weights `exp(−π (x − c)ᵗ P (x − c))`, `x ∈ ℤ^m`, of a positive definite `P` are
summable. -/
theorem summable_exp_neg_quadForm {P : Matrix (Fin m) (Fin m) ℝ} (hP : P.PosDef)
    (c : Fin m → ℝ) :
    Summable fun x : Fin m → ℤ => Real.exp (-π * quadForm P (ofInt x - c)) := by
  induction m with
  | zero => exact Summable.of_finite
  | succ m ih =>
    have hs := symm_of_posDef hP
    have hd := pos_of_posDef hP
    obtain ⟨C, hC⟩ := exists_tsum_exp_neg_sq_le hd
    have hf : ∀ (x' : Fin m → ℤ) (t : ℤ),
        Real.exp (-π * quadForm P (ofInt (Fin.cons t x' : Fin (m + 1) → ℤ) - c)) =
          Real.exp (-π * P 0 0 * ((t : ℝ) -
            (c 0 - blkP P ⬝ᵥ (ofInt x' - Fin.tail c) / P 0 0)) ^ 2) *
          Real.exp (-π * quadForm (schur P) (ofInt x' - Fin.tail c)) := fun x' t => by
      rw [← Real.exp_add, ofInt_cons, quadForm_cons_sub hs hd.ne']
      ring_nf
    have hg : Summable fun q : (Fin m → ℤ) × ℤ =>
        Real.exp (-π * quadForm P (ofInt (Fin.cons q.2 q.1 : Fin (m + 1) → ℤ) - c)) := by
      refine (summable_prod_of_nonneg fun _ => (Real.exp_pos _).le).2 ⟨fun x' => ?_, ?_⟩
      · simp only [hf]
        exact (summable_exp_neg_sq hd _).mul_right _
      · refine Summable.of_nonneg_of_le (fun _ => tsum_nonneg fun _ => (Real.exp_pos _).le)
          (fun x' => ?_) ((ih (schur_posDef hP) (Fin.tail c)).mul_left C)
        simp only [hf, tsum_mul_right]
        exact mul_le_mul_of_nonneg_right (hC _) (Real.exp_pos _).le
    exact ((Equiv.prodComm _ _).trans (Fin.consEquiv fun _ => ℤ)).summable_iff.1 hg

private theorem norm_cexp_add_mul_I (α β : ℝ) : ‖cexp ((α : ℂ) + (β : ℂ) * I)‖ = Real.exp α := by
  rw [Complex.norm_exp]
  simp

/-- The Gaussian term `exp(−π (x − c)ᵗ P (x − c) + 2πi⟨w, x⟩)`. -/
private noncomputable def gTerm (P : Matrix (Fin m) (Fin m) ℝ) (c w : Fin m → ℝ)
    (x : Fin m → ℤ) : ℂ :=
  cexp (-π * (quadForm P (ofInt x - c) : ℂ) + 2 * π * I * (w ⬝ᵥ ofInt x : ℝ))

/-- The dual term `exp(−π (y − w)ᵗ P⁻¹ (y − w) − 2πi⟨y − w, c⟩)`. -/
private noncomputable def dTerm (P : Matrix (Fin m) (Fin m) ℝ) (c w : Fin m → ℝ)
    (y : Fin m → ℤ) : ℂ :=
  cexp (-π * (quadForm P⁻¹ (ofInt y - w) : ℂ) - 2 * π * I * ((ofInt y - w) ⬝ᵥ c : ℝ))

private theorem summable_gTerm {P : Matrix (Fin m) (Fin m) ℝ} (hP : P.PosDef)
    (c w : Fin m → ℝ) : Summable (gTerm P c w) := by
  refine Summable.of_norm ((summable_exp_neg_quadForm hP c).congr fun x => ?_)
  rw [gTerm, show -π * (quadForm P (ofInt x - c) : ℂ) + 2 * π * I * (w ⬝ᵥ ofInt x : ℝ) =
      ((-π * quadForm P (ofInt x - c) : ℝ) : ℂ) + ((2 * π * (w ⬝ᵥ ofInt x) : ℝ) : ℂ) * I by
    push_cast; ring, norm_cexp_add_mul_I]

private theorem summable_dTerm {P : Matrix (Fin m) (Fin m) ℝ} (hP : P.PosDef)
    (c w : Fin m → ℝ) : Summable (dTerm P c w) := by
  refine Summable.of_norm ((summable_exp_neg_quadForm hP.inv w).congr fun y => ?_)
  rw [dTerm, show -π * (quadForm P⁻¹ (ofInt y - w) : ℂ) - 2 * π * I * ((ofInt y - w) ⬝ᵥ c : ℝ) =
      ((-π * quadForm P⁻¹ (ofInt y - w) : ℝ) : ℂ) + ((-(2 * π * ((ofInt y - w) ⬝ᵥ c)) : ℝ) : ℂ) *
        I by push_cast; ring, norm_cexp_add_mul_I]

private theorem tsum_fin_zero (f : (Fin 0 → ℤ) → ℂ) : ∑' x, f x = f 0 :=
  tsum_eq_single 0 fun b hb => absurd (Subsingleton.elim b 0) hb

/-- The summand after the one-dimensional step in the first coordinate. -/
private noncomputable def gStep (P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (c w : Fin (m + 1) → ℝ)
    (x' : Fin m → ℤ) (k : ℤ) : ℂ :=
  (((√(P 0 0))⁻¹ : ℝ) : ℂ) *
    cexp ((-π * (quadForm (schur P) (ofInt x' - Fin.tail c) : ℂ) +
      2 * π * I * (Fin.tail w ⬝ᵥ ofInt x' : ℝ)) +
      (-π * ((k : ℂ) - (w 0 : ℝ)) ^ 2 / (P 0 0 : ℝ) - 2 * π * I * ((k : ℂ) - (w 0 : ℝ)) *
        ((c 0 - blkP P ⬝ᵥ (ofInt x' - Fin.tail c) / P 0 0 : ℝ) : ℂ)))

/-- The one-dimensional step: the sum over the first coordinate (`tsum_cexp_one`). -/
private theorem tsum_gTerm_cons {P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (hP : P.PosDef)
    (c w : Fin (m + 1) → ℝ) (x' : Fin m → ℤ) :
    ∑' t : ℤ, gTerm P c w (Fin.cons t x') = ∑' k : ℤ, gStep P c w x' k := by
  have hs := symm_of_posDef hP
  have hd := pos_of_posDef hP
  have ht : ∀ t : ℤ, gTerm P c w (Fin.cons t x') =
      cexp (-π * (quadForm (schur P) (ofInt x' - Fin.tail c) : ℂ) +
        2 * π * I * (Fin.tail w ⬝ᵥ ofInt x' : ℝ)) *
      cexp (-π * ((P 0 0 : ℝ) : ℂ) * ((t : ℂ) -
        ((c 0 - blkP P ⬝ᵥ (ofInt x' - Fin.tail c) / P 0 0 : ℝ) : ℂ)) ^ 2 +
        2 * π * I * ((w 0 : ℝ) : ℂ) * t) := by
    intro t
    rw [gTerm, ← Complex.exp_add, ofInt_cons, quadForm_cons_sub hs hd.ne']
    conv_lhs => rw [← Fin.cons_self_tail w]
    rw [cons_dotProduct_cons]
    congr 1
    push_cast
    ring
  rw [tsum_congr ht, tsum_mul_left, tsum_cexp_one hd, ← tsum_mul_left, ← tsum_mul_left]
  exact tsum_congr fun k => by rw [gStep, mul_left_comm, ← Complex.exp_add]

/-- Poisson summation with a phase:
`Σ_x e^{−π(x−c)ᵗP(x−c)} e^{2πi⟨w,x⟩} = det(P)^{−1/2} Σ_y e^{−π(y−w)ᵗP⁻¹(y−w)} e^{−2πi⟨y−w,c⟩}`. -/
private theorem tsum_gTerm {P : Matrix (Fin m) (Fin m) ℝ} (hP : P.PosDef) (c w : Fin m → ℝ) :
    ∑' x, gTerm P c w x = ((√P.det)⁻¹ : ℝ) * ∑' y, dTerm P c w y := by
  induction m with
  | zero =>
    rw [tsum_fin_zero, tsum_fin_zero]
    simp [gTerm, dTerm, quadForm, Matrix.det_isEmpty]
  | succ m ih =>
    have hd := pos_of_posDef hP
    let e : (Fin m → ℤ) × ℤ ≃ (Fin (m + 1) → ℤ) :=
      (Equiv.prodComm _ _).trans (Fin.consEquiv fun _ => ℤ)
    let e₂ : ℤ × (Fin m → ℤ) ≃ (Fin (m + 1) → ℤ) := Fin.consEquiv fun _ => ℤ
    have hgS := (summable_gTerm hP c w).comp_injective e.injective
    have hdS := (summable_dTerm hP c w).comp_injective e₂.injective
    have hL : ∑' x, gTerm P c w x = ∑' x' : Fin m → ℤ, ∑' k : ℤ, gStep P c w x' k := by
      rw [← e.tsum_eq]
      exact (hgS.tsum_prod' fun x' => hgS.prod_factor x').trans
        (tsum_congr (tsum_gTerm_cons hP c w))
    have hGS : Summable (Function.uncurry (gStep P c w)) := by
      refine Summable.of_norm (((Summable.mul_of_nonneg
        (summable_exp_neg_quadForm (schur_posDef hP) (Fin.tail c))
        (summable_exp_neg_sq (inv_pos.2 hd) (w 0)) (fun _ => (Real.exp_pos _).le)
        (fun _ => (Real.exp_pos _).le)).mul_left (√(P 0 0))⁻¹).congr fun q => ?_)
      rw [Function.uncurry, gStep, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity),
        show (-π * (quadForm (schur P) (ofInt q.1 - Fin.tail c) : ℂ) +
          2 * π * I * (Fin.tail w ⬝ᵥ ofInt q.1 : ℝ)) +
          (-π * ((q.2 : ℂ) - (w 0 : ℝ)) ^ 2 / (P 0 0 : ℝ) - 2 * π * I * ((q.2 : ℂ) - (w 0 : ℝ)) *
            ((c 0 - blkP P ⬝ᵥ (ofInt q.1 - Fin.tail c) / P 0 0 : ℝ) : ℂ)) =
          ((-π * quadForm (schur P) (ofInt q.1 - Fin.tail c) +
            -π * (P 0 0)⁻¹ * ((q.2 : ℝ) - w 0) ^ 2 : ℝ) : ℂ) +
          ((2 * π * (Fin.tail w ⬝ᵥ ofInt q.1) - 2 * π * ((q.2 : ℝ) - w 0) *
            (c 0 - blkP P ⬝ᵥ (ofInt q.1 - Fin.tail c) / P 0 0) : ℝ) : ℂ) * I by
          push_cast; ring,
        norm_cexp_add_mul_I, Real.exp_add]
    have hsw : ∑' x' : Fin m → ℤ, ∑' k : ℤ, gStep P c w x' k =
        ∑' k : ℤ, ∑' x' : Fin m → ℤ, gStep P c w x' k :=
      (hGS.tsum_comm' (fun x' => hGS.prod_factor x') fun k => hGS.prod_symm.prod_factor k).symm
    have h4 : ∀ k : ℤ, ∑' x' : Fin m → ℤ, gStep P c w x' k =
        (((√(P 0 0))⁻¹ * (√(schur P).det)⁻¹ : ℝ) : ℂ) *
          ∑' y' : Fin m → ℤ, dTerm P c w (Fin.cons k y') := by
      intro k
      have hx : ∀ x' : Fin m → ℤ, gStep P c w x' k =
          (((√(P 0 0))⁻¹ : ℝ) : ℂ) * cexp (-π * ((k : ℂ) - (w 0 : ℝ)) ^ 2 / (P 0 0 : ℝ) -
            2 * π * I * ((((k : ℝ) - w 0) * c 0 +
              ((k : ℝ) - w 0) / P 0 0 * (blkP P ⬝ᵥ Fin.tail c) : ℝ) : ℂ)) *
          gTerm (schur P) (Fin.tail c) (Fin.tail w + (((k : ℝ) - w 0) / P 0 0) • blkP P) x' := by
        intro x'
        rw [gStep, gTerm, mul_assoc (((√(P 0 0))⁻¹ : ℝ) : ℂ), ← Complex.exp_add, add_dotProduct,
          smul_dotProduct, smul_eq_mul, dotProduct_sub]
        congr 2
        push_cast
        ring
      have hy : ∀ y' : Fin m → ℤ, cexp (-π * ((k : ℂ) - (w 0 : ℝ)) ^ 2 / (P 0 0 : ℝ) -
            2 * π * I * ((((k : ℝ) - w 0) * c 0 +
              ((k : ℝ) - w 0) / P 0 0 * (blkP P ⬝ᵥ Fin.tail c) : ℝ) : ℂ)) *
          dTerm (schur P) (Fin.tail c) (Fin.tail w + (((k : ℝ) - w 0) / P 0 0) • blkP P) y' =
          dTerm P c w (Fin.cons k y') := by
        intro y'
        have hv : ofInt (Fin.cons k y' : Fin (m + 1) → ℤ) - w =
            Fin.cons ((k : ℝ) - w 0) (ofInt y' - Fin.tail w) := by
          rw [ofInt_cons]
          conv_lhs => rw [← Fin.cons_self_tail w]
          rw [cons_sub_cons]
        have hq : quadForm P⁻¹ (ofInt (Fin.cons k y' : Fin (m + 1) → ℤ) - w) =
            ((k : ℝ) - w 0) ^ 2 / P 0 0 + quadForm (schur P)⁻¹
              (ofInt y' - (Fin.tail w + (((k : ℝ) - w 0) / P 0 0) • blkP P)) := by
          rw [hv, quadForm_inv_cons hP, sub_sub]
        have hph : (ofInt (Fin.cons k y' : Fin (m + 1) → ℤ) - w) ⬝ᵥ c =
            ((k : ℝ) - w 0) * c 0 + ((k : ℝ) - w 0) / P 0 0 * (blkP P ⬝ᵥ Fin.tail c) +
              (ofInt y' - (Fin.tail w + (((k : ℝ) - w 0) / P 0 0) • blkP P)) ⬝ᵥ Fin.tail c := by
          rw [hv]
          conv_lhs => rw [← Fin.cons_self_tail c]
          simp only [cons_dotProduct_cons, sub_dotProduct, add_dotProduct, smul_dotProduct,
            smul_eq_mul]
          ring
        rw [dTerm, dTerm, ← Complex.exp_add, hq, hph]
        congr 1
        push_cast
        ring
      rw [tsum_congr hx, tsum_mul_left, ih (schur_posDef hP), ← tsum_congr hy, tsum_mul_left]
      push_cast
      ring
    rw [hL, hsw, tsum_congr h4, tsum_mul_left, det_eq_mul_det_schur hP, Real.sqrt_mul hd.le,
      mul_inv]
    congr 1
    rw [← e₂.tsum_eq]
    exact (hdS.tsum_prod' fun k => hdS.prod_factor k).symm

/-- **Gaussian Poisson summation over `ℤ^m`**: for positive definite `V`,
`Σ_{x ∈ ℤ^m} e^{−π(x−c)ᵗV⁻¹(x−c)} = det(V)^{1/2} Σ_{y ∈ ℤ^m} e^{−π yᵗVy} e^{2πi⟨y,c⟩}`. -/
theorem tsum_exp_neg_quadForm_eq {V : Matrix (Fin m) (Fin m) ℝ} (hV : V.PosDef)
    (c : Fin m → ℝ) :
    ∑' x : Fin m → ℤ, (Real.exp (-π * quadForm V⁻¹ (ofInt x - c)) : ℂ) =
      (√V.det : ℂ) * ∑' y : Fin m → ℤ, (Real.exp (-π * quadForm V (ofInt y)) : ℂ) *
        Complex.exp (2 * π * Complex.I * (ofInt y ⬝ᵥ c : ℝ)) := by
  have hu : IsUnit V.det := hV.isUnit.map Matrix.detMonoidHom
  have h := tsum_gTerm hV.inv c 0
  have hl : ∀ x : Fin m → ℤ, gTerm V⁻¹ c 0 x = (Real.exp (-π * quadForm V⁻¹ (ofInt x - c)) : ℂ) :=
    fun x => by simp [gTerm, Complex.ofReal_exp]
  have hr : ∀ y : Fin m → ℤ, dTerm V⁻¹ c 0 (-y) =
      (Real.exp (-π * quadForm V (ofInt y)) : ℂ) * cexp (2 * π * I * (ofInt y ⬝ᵥ c : ℝ)) := by
    intro y
    have hn : ofInt (-y) = -ofInt y := by ext i; simp [ofInt]
    rw [dTerm, Matrix.nonsing_inv_nonsing_inv _ hu, sub_zero, hn, quadForm_neg, neg_dotProduct,
      Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [tsum_congr hl] at h
  rw [h, ← (Equiv.neg (Fin m → ℤ)).tsum_eq, Matrix.det_nonsing_inv, Ring.inverse_eq_inv',
    Real.sqrt_inv, inv_inv]
  exact congrArg _ (tsum_congr fun y => hr y)

/-- Real form of `tsum_exp_neg_quadForm_eq`:
`Σ_x e^{−π(x−c)ᵗV⁻¹(x−c)} = det(V)^{1/2} Σ_y e^{−π yᵗVy} cos(2π⟨y,c⟩)`. -/
theorem tsum_exp_neg_quadForm_eq_real {V : Matrix (Fin m) (Fin m) ℝ} (hV : V.PosDef)
    (c : Fin m → ℝ) :
    ∑' x : Fin m → ℤ, Real.exp (-π * quadForm V⁻¹ (ofInt x - c)) =
      √V.det * ∑' y : Fin m → ℤ,
        Real.exp (-π * quadForm V (ofInt y)) * Real.cos (2 * π * (ofInt y ⬝ᵥ c)) := by
  have h := congrArg Complex.re (tsum_exp_neg_quadForm_eq hV c)
  have hs : Summable fun y : Fin m → ℤ =>
      (Real.exp (-π * quadForm V (ofInt y)) : ℂ) * cexp (2 * π * I * (ofInt y ⬝ᵥ c : ℝ)) := by
    refine Summable.of_norm ((summable_exp_neg_quadForm hV 0).congr fun y => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      show 2 * π * I * ((ofInt y ⬝ᵥ c : ℝ) : ℂ) = (((2 * π * (ofInt y ⬝ᵥ c)) : ℝ) : ℂ) * I by
        push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one, sub_zero]
  rw [← Complex.ofReal_tsum, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.re_tsum hs] at h
  rw [h]
  congr 1
  refine tsum_congr fun y => ?_
  rw [Complex.re_ofReal_mul, show 2 * π * I * ((ofInt y ⬝ᵥ c : ℝ) : ℂ) =
    (((2 * π * (ofInt y ⬝ᵥ c)) : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_ofReal_mul_I_re]

end Mitaka.LatticeGaussian
