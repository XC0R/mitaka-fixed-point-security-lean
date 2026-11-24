/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import FalconPrecision.Errors.PathCompose
public import LatticeCrypto.Ring.SchoolbookCert
public import Mitaka.Lemma5
public import Mitaka.RenyiTriangle
public import Mitaka.Embedding

/-! # Algorithm 3 of [ZKLY26] and the fixed-point centre step

[ZKLY26] (ePrint 2026/2521), Algorithm 3 "New Mitaka_Z Sampler" (p. 6), over
`K = ℚ[X]/(Xⁿ + 1)` in the coefficient embedding:

1. `x ← D_{ℤ^{2n}, Lr}`; 2. `p ← (1/L) Â x`; 3. `ĉ ← B̂⁻¹ (c - p)`; 4. `z₂ ← D_{ℤⁿ, r, ĉ₂}`;
5. `c'₁ ← ĉ₁ - û z₂`; 6. `z₁ ← D_{ℤⁿ, r, c'₁}`; 7. return `z ← B (z₁, z₂)ᵗ`.

The trapdoor basis is `B = (g G; -f -F)` with `B⁻¹ = (1/q)(-F -G; f g)` when `fG - gF = q`
(p. 4, l. 136-137), `U_a = (1 a; 0 1)`, `B̂ = B U_{-û}` (p. 5, l. 170-171), so
`B̂⁻¹ = U_û B⁻¹`. The expanded key stores `p_u û = ⌊p_u u⌉` and `p_A Â = ⌊p_A A⌉` as integers
(p. 9, l. 294-295). `centre` computes `U_û (1/q)(-F -G; f g) v`; it is `B̂⁻¹ v` under the NTRU
equation, which is a key hypothesis, not part of `Key`.

The computation `sampleCoords` makes `4n` integer-Gaussian queries (`2n` perturbation queries
`Query.perturb`, `2n` online queries `Query.online c`), and returns `(z₁, z₂)`; `sample` returns
`B (z₁, z₂)ᵗ`. All centre arithmetic is exact (real arithmetic; the 64-bit and CRT
representation of [ZKLY26, §4.3] is not modelled here). The samplers are perfect, as in the paper
(p. 6, l. 214-215; p. 8, l. 268-270): a world is a `QueryImpl` whose answers have the laws
`answer P fp`. The exact world uses `fp = id`; the fixed-point world converts each online centre by
`fp` (Algorithm 4, p. 12; its claim `|c^fp - c| ≤ 2⁻⁶⁴` is p. 13, l. 388-391, for inputs within the
§4.3 bounds; here any `fp` with `|fp c - c| ≤ Δ` for every `c`). `Mitaka.Witness` shows that such
worlds exist.

* `renyiDiv_sampleCoords_le`, `renyiDiv_sample_le`: the fixed-point step [ZKLY26, p. 8-9,
  l. 277-282], `log R_a(P_fp ‖ P) ≤ 2n (aπΔ²/r² + a(a+1)Δ²/(2³¹(a-1)))`, from
  `Lemma5.renyiDiv_shift_le` per online query and `RenyiPath.renyiMGF_simulateQ_le_path` along
  executions.
* `renyiDiv_sample_le_of_renyiDiv_le`: combined with any bound on `R_b(P ‖ ν)` at
  `b = (pa-1)/(p-1)` (Theorem 1 of [ZKLY26] is such a bound for `ν = D_{L(B),rs,c}`, not stated
  here) through `RenyiTriangle.renyiDiv_le_rpow_mul_renyiDiv`. -/

@[expose] public section

open Real MeasureTheory InformationTheory OracleSpec OracleComp LatticeCrypto
open scoped ENNReal

namespace Mitaka

/-- The parameters of Algorithm 3 and of its analysis (Table 2, p. 9). -/
structure Params where
  /-- The NTRU modulus `q`. -/
  q : ℕ
  /-- The online integer Gaussian width `r` (convention of [ZKLY26]). -/
  r : ℝ
  /-- The perturbation scaling factor `L`. -/
  L : ℕ
  /-- The denominator `p_u` of `û`. -/
  pu : ℕ
  /-- The denominator `p_A` of `Â`. -/
  pA : ℕ
  /-- The scaled Gaussian width `s` (Theorem 1, condition 2). -/
  s : ℝ
  /-- The trapdoor quality parameter `α ≥ 1` (Theorem 1, condition 1). -/
  alpha : ℝ

/-- The Mitaka-512 parameters of [ZKLY26, Table 2] (p. 9). -/
noncomputable def Params.mitaka512 : Params where
  q := 12289
  r := 3305 / 1000
  L := 2
  pu := 2 ^ 16
  pA := 2 ^ 42
  s := 12749 / 100
  alpha := 115 / 100

/-- The Mitaka-1024 parameters of [ZKLY26, Table 2] (p. 9). -/
noncomputable def Params.mitaka1024 : Params where
  q := 12289
  r := 334 / 100
  L := 2
  pu := 2 ^ 16
  pA := 2 ^ 43
  s := 138
  alpha := 123 / 100

/-- An expanded signing key: the NTRU trapdoor `f, g, F, G` and the stored integers
`uInt = p_u û` and `aInt = p_A Â` (a `2 × 2` matrix over `K`), as coefficient vectors. -/
structure Key (n : ℕ) where
  /-- The secret polynomial `f`. -/
  f : Fin n → ℤ
  /-- The secret polynomial `g`. -/
  g : Fin n → ℤ
  /-- The polynomial `F` of the NTRU equation `fG - gF = q`. -/
  F : Fin n → ℤ
  /-- The polynomial `G` of the NTRU equation `fG - gF = q`. -/
  G : Fin n → ℤ
  /-- `p_u û = ⌊p_u u⌉`. -/
  uInt : Fin n → ℤ
  /-- `p_A Â = ⌊p_A A⌉`. -/
  aInt : Fin 2 → Fin 2 → Fin n → ℤ

variable {n : ℕ}

/-- The coefficient vector of an integer polynomial, over `ℝ`. -/
def toReal (v : Fin n → ℤ) : Fin n → ℝ := fun k => v k

/-- `û = uInt / p_u`. -/
noncomputable def Key.uHat (P : Params) (K : Key n) : Fin n → ℝ := fun k => K.uInt k / P.pu

/-- `Â = aInt / p_A`. -/
noncomputable def Key.aHat (P : Params) (K : Key n) : Fin 2 → Fin 2 → Fin n → ℝ :=
  fun i j k => K.aInt i j k / P.pA

/-- The perturbation `p = (1/L) Â x` (step 2). -/
noncomputable def perturbation (P : Params) (K : Key n) (x : Fin 2 → Fin n → ℤ) :
    Fin 2 → Fin n → ℝ :=
  fun i k => (∑ j, negacyclicConvCoeff (K.aHat P i j) (toReal (x j)) k) / P.L

/-- `U_û (1/q)(-F -G; f g) v`, which is `B̂⁻¹ v` when `fG - gF = q` (step 3). -/
noncomputable def centre (P : Params) (K : Key n) (v : Fin 2 → Fin n → ℝ) :
    Fin 2 → Fin n → ℝ :=
  let c₂ : Fin n → ℝ := fun k =>
    (negacyclicConvCoeff (toReal K.f) (v 0) k + negacyclicConvCoeff (toReal K.g) (v 1) k) / P.q
  let c₁ : Fin n → ℝ := fun k =>
    -(negacyclicConvCoeff (toReal K.F) (v 0) k + negacyclicConvCoeff (toReal K.G) (v 1) k) / P.q
  ![c₁ + negacyclicConvCoeff (K.uHat P) c₂, c₂]

/-- The constant `q` as a coefficient vector. -/
theorem ofCoeffs_toReal_single [NeZero n] (q : ℕ) :
    ofCoeffs (toReal (Pi.single 0 (q : ℤ) : Fin n → ℤ)) = mkQ ℝ n (Polynomial.C (q : ℝ)) := by
  unfold ofCoeffs
  rw [Finset.sum_eq_single 0 (fun b _ hb => by simp [toReal, Pi.single_eq_of_ne hb])
    (fun h => absurd (Finset.mem_univ _) h)]
  simp [toReal]

/-- `toReal` commutes with subtraction. -/
theorem toReal_sub (x y : Fin n → ℤ) : toReal (x - y) = toReal x - toReal y := by
  funext k
  simp [toReal]

/-- `toReal` commutes with the negacyclic convolution. -/
theorem toReal_negacyclicConvCoeff (x y : Fin n → ℤ) :
    toReal (negacyclicConvCoeff x y) = negacyclicConvCoeff (toReal x) (toReal y) := by
  funext k
  simp only [toReal, negacyclicConvCoeff]
  push_cast
  rfl

/-- `B w` for `w ∈ K²` with `B = (g G; -f -F)`, over `ℝ`. -/
noncomputable def basisApply (K : Key n) (w : Fin 2 → Fin n → ℝ) : Fin 2 → Fin n → ℝ :=
  ![negacyclicConvCoeff (toReal K.g) (w 0) + negacyclicConvCoeff (toReal K.G) (w 1),
    -negacyclicConvCoeff (toReal K.f) (w 0) - negacyclicConvCoeff (toReal K.F) (w 1)]

/-- Under the NTRU equation `fG - gF = q`, `centre` inverts `B̂ = B U_{-û}`:
`B (ĉ₁ - û ĉ₂, ĉ₂)ᵗ = v` for `ĉ = centre P K v`. -/
theorem basisApply_centre [NeZero n] (P : Params) (K : Key n) (hq : 0 < P.q)
    (hntru : negacyclicConvCoeff K.f K.G - negacyclicConvCoeff K.g K.F = Pi.single 0 (P.q : ℤ))
    (v : Fin 2 → Fin n → ℝ) :
    basisApply K
        ![centre P K v 0 - negacyclicConvCoeff (K.uHat P) (centre P K v 1), centre P K v 1] =
      v := by
  have hn : 0 < n := NeZero.pos n
  have hq' : (P.q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hinv : mkQ ℝ n (Polynomial.C (P.q : ℝ)) * mkQ ℝ n (Polynomial.C (P.q : ℝ)⁻¹) = 1 := by
    rw [← map_mul, ← Polynomial.C_mul, mul_inv_cancel₀ hq', Polynomial.C_1, map_one]
  have hN : ofCoeffs (toReal K.f) * ofCoeffs (toReal K.G) -
      ofCoeffs (toReal K.g) * ofCoeffs (toReal K.F) = mkQ ℝ n (Polynomial.C (P.q : ℝ)) := by
    have h := congrArg (fun x : Fin n → ℤ => ofCoeffs (toReal x)) hntru
    simpa only [toReal_sub, toReal_negacyclicConvCoeff, ofCoeffs_sub,
      ofCoeffs_negacyclicConvCoeff hn, ofCoeffs_toReal_single] using h
  funext i
  fin_cases i
  · apply ofCoeffs_injective hn
    simp only [basisApply, centre, Fin.zero_eta, Matrix.cons_val_zero, Matrix.cons_val_one,
      add_sub_cancel_right, ofCoeffs_add, ofCoeffs_negacyclicConvCoeff hn, ofCoeffs_fun_div,
      ofCoeffs_fun_neg, ofCoeffs_fun_add]
    linear_combination (ofCoeffs (v 0) * mkQ ℝ n (Polynomial.C (P.q : ℝ)⁻¹)) * hN +
      ofCoeffs (v 0) * hinv
  · apply ofCoeffs_injective hn
    simp only [basisApply, centre, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      add_sub_cancel_right, ofCoeffs_sub, ofCoeffs_neg, ofCoeffs_negacyclicConvCoeff hn,
      ofCoeffs_fun_div, ofCoeffs_fun_neg, ofCoeffs_fun_add]
    linear_combination (ofCoeffs (v 1) * mkQ ℝ n (Polynomial.C (P.q : ℝ)⁻¹)) * hN +
      ofCoeffs (v 1) * hinv

/-- The lattice point `B (z₁, z₂)ᵗ` with `B = (g G; -f -F)` (step 7). -/
def latticePoint (K : Key n) (z₁ z₂ : Fin n → ℤ) : Fin 2 → Fin n → ℤ :=
  ![negacyclicConvCoeff K.g z₁ + negacyclicConvCoeff K.G z₂,
    -negacyclicConvCoeff K.f z₁ - negacyclicConvCoeff K.F z₂]

/-- An integer-Gaussian query: a perturbation sample (width `Lr`, centre `0`) or an online sample
(width `r`) at an exact centre `c`. -/
inductive Query
  /-- A perturbation sample: width `Lr`, centre `0`. -/
  | perturb
  /-- An online sample: width `r`, exact centre `c`. -/
  | online (c : ℝ)

/-- The oracle of Algorithm 3: integer-Gaussian queries, answered in `ℤ`. -/
@[reducible] def samplerSpec : OracleSpec Query := fun _ => ℤ

/-- Every answer type of `samplerSpec` is countable. -/
instance instCountableSamplerSpecRange (t : Query) : Countable (samplerSpec.Range t) :=
  inferInstanceAs (Countable ℤ)

/-- One query per coordinate, in order. -/
def queryVec : {m : ℕ} → (Fin m → Query) → OracleComp samplerSpec (Fin m → ℤ)
  | 0, _ => pure finZeroElim
  | _ + 1, t => do
    let z ← liftM (samplerSpec.query (t 0))
    let zs ← queryVec (Fin.tail t)
    pure (Fin.cons z zs)

/-- **Algorithm 3**, returning the integer coordinates `(z₁, z₂)`. -/
noncomputable def sampleCoords (P : Params) (K : Key n) (c : Fin 2 → Fin n → ℝ) :
    OracleComp samplerSpec ((Fin n → ℤ) × (Fin n → ℤ)) := do
  let x₁ ← queryVec fun _ => Query.perturb
  let x₂ ← queryVec fun _ => Query.perturb
  let ch := centre P K (c - perturbation P K ![x₁, x₂])
  let z₂ ← queryVec fun k => Query.online (ch 1 k)
  let c₁ := ch 0 - negacyclicConvCoeff (K.uHat P) (toReal z₂)
  let z₁ ← queryVec fun k => Query.online (c₁ k)
  pure (z₁, z₂)

/-- **Algorithm 3**: the lattice point `z = B (z₁, z₂)ᵗ`. -/
noncomputable def sample (P : Params) (K : Key n) (c : Fin 2 → Fin n → ℝ) :
    OracleComp samplerSpec (Fin 2 → Fin n → ℤ) :=
  (fun z => latticePoint K z.1 z.2) <$> sampleCoords P K c

/-- The law of a query answer when online centres are converted by `fp`: `D_{ℤ,Lr,0}` for a
perturbation query and `D_{ℤ,r,fp c}` for an online query. -/
noncomputable def answer (P : Params) (fp : ℝ → ℝ) : Query → Measure ℤ
  | .perturb => discreteGaussianMeasure (Lemma5.stdDev (P.L * P.r)) 0
  | .online c => discreteGaussianMeasure (Lemma5.stdDev P.r) (fp c)

/-- Weight `1` on online queries, `0` on perturbation queries. -/
def onlineWeight : Query → ℝ
  | .perturb => 0
  | .online _ => 1

open FalconPrecision.RenyiPath in
/-- Perturbation queries carry no online weight. -/
private theorem pathSum_queryVec_perturb (m : ℕ) :
    PathSum onlineWeight (queryVec fun _ : Fin m => Query.perturb) 0 := by
  induction m with
  | zero =>
    simp only [queryVec]
    exact .pure _ le_rfl
  | succ m ih =>
    simp only [queryVec]
    exact .query_bind Query.perturb _ fun u =>
      (PathSum.bind ih fun zs => .pure _ le_rfl).weaken (by simp [onlineWeight])

open FalconPrecision.RenyiPath in
/-- `m` online queries carry online weight `m`. -/
private theorem pathSum_queryVec_online (m : ℕ) (d : Fin m → ℝ) :
    PathSum onlineWeight (queryVec fun k => Query.online (d k)) m := by
  induction m with
  | zero =>
    simp only [queryVec]
    exact .pure _ (by simp)
  | succ m ih =>
    simp only [queryVec]
    exact .query_bind _ _ fun u =>
      (PathSum.bind (ih (Fin.tail d)) fun zs => .pure _ le_rfl).weaken (by simp [onlineWeight])

open FalconPrecision.RenyiPath in
/-- Along every execution, Algorithm 3 makes `2n` online queries. -/
theorem pathSum_sampleCoords (P : Params) (K : Key n) (c : Fin 2 → Fin n → ℝ) :
    PathSum onlineWeight (sampleCoords P K c) (2 * n) := by
  simp only [sampleCoords]
  refine (PathSum.bind (pathSum_queryVec_perturb n) fun x₁ =>
    PathSum.bind (pathSum_queryVec_perturb n) fun x₂ =>
      PathSum.bind (pathSum_queryVec_online n _) fun z₂ =>
        PathSum.bind (pathSum_queryVec_online n _) fun z₁ => .pure (z₁, z₂) le_rfl).weaken ?_
  linarith

variable {m : Type → Type*} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m]

/-- If every query answer is a probability measure, so is every simulated output law. -/
private theorem isProbabilityMeasure_evalDist_simulateQ (impl : QueryImpl samplerSpec m)
    (hI : ∀ t, IsProbabilityMeasure (@evalDist m _ (samplerSpec.Range t) ⊤ (impl t)))
    {α : Type} [MeasurableSpace α] (oa : OracleComp samplerSpec α) :
    IsProbabilityMeasure 𝒟[simulateQ impl oa] := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    simp only [simulateQ_pure, evalDist_pure]
    infer_instance
  | query_bind t k ih =>
    let : MeasurableSpace (samplerSpec.Range t) := ⊤
    have : MeasurableSingletonClass (samplerSpec.Range t) := ⟨fun _ => trivial⟩
    have := hI t
    simp only [simulateQ_bind, simulateQ_spec_query]
    rw [evalDist_bind_of_discrete]
    constructor
    rw [Measure.bind_apply MeasurableSet.univ measurable_from_top.aemeasurable,
      lintegral_congr fun u => @measure_univ _ _ _ (ih u), lintegral_one, measure_univ]

/-- A Rényi divergence bound `exp E` is a Rényi MGF bound `exp((a - 1)E)`. -/
private theorem renyiMGF_le_of_renyiDiv_le {α : Type*} [MeasurableSpace α] {a : ℝ} (ha : 1 < a)
    {μ ν : Measure α} {E : ℝ} (h : renyiDiv a μ ν ≤ ENNReal.ofReal (Real.exp E)) :
    renyiMGF a μ ν ≤ ENNReal.ofReal (Real.exp ((a - 1) * E)) := by
  have ham : a - 1 ≠ 0 := by linarith
  rw [renyiDiv_eq_rpow ha] at h
  calc renyiMGF a μ ν = (renyiMGF a μ ν ^ (a - 1)⁻¹) ^ (a - 1) :=
        (ENNReal.rpow_inv_rpow ham _).symm
    _ ≤ ENNReal.ofReal (Real.exp E) ^ (a - 1) := ENNReal.rpow_le_rpow h (by linarith)
    _ = _ := by
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by linarith), ← Real.exp_mul,
          mul_comm]

/-- With perfect samplers of positive widths, the output law of Algorithm 3 is a probability
measure. -/
theorem isProbabilityMeasure_evalDist_sample (P : Params) (K : Key n) (c : Fin 2 → Fin n → ℝ)
    (fp : ℝ → ℝ) (hr : 0 < P.r) (hL : 0 < P.L) (impl : QueryImpl samplerSpec m)
    (hI : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (impl t) = answer P fp t) :
    IsProbabilityMeasure 𝒟[simulateQ impl (sample P K c)] := by
  have hs : 0 < √(2 * π) := Real.sqrt_pos.2 (by positivity)
  have hσ : 0 < Lemma5.stdDev P.r := div_pos hr hs
  have hσL : 0 < Lemma5.stdDev (P.L * P.r) := div_pos (mul_pos (by exact_mod_cast hL) hr) hs
  refine isProbabilityMeasure_evalDist_simulateQ impl (fun t => ?_) _
  rw [hI t]
  cases t with
  | perturb => exact isProbabilityMeasure_discreteGaussianMeasure _ _ hσL
  | online x => exact isProbabilityMeasure_discreteGaussianMeasure _ _ hσ

/-- **The fixed-point step** on the coordinates: if every online centre is converted within `Δ`,
then `R_a(P_fp ‖ P) ≤ exp(2n (aπΔ²/r² + a(a+1)Δ²/(2³¹(a-1))))`. -/
theorem renyiDiv_sampleCoords_le (P : Params) (K : Key n) (c : Fin 2 → Fin n → ℝ)
    (fp : ℝ → ℝ) {Δ : ℝ} (hfp : ∀ x, |fp x - x| ≤ Δ) (hr : 1277 / 1000 ≤ Lemma5.stdDev P.r)
    {a : ℝ} (ha : 1 < a) (implE implF : QueryImpl samplerSpec m)
    (hE : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implE t) = answer P id t)
    (hF : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implF t) = answer P fp t) :
    renyiDiv a 𝒟[simulateQ implF (sampleCoords P K c)] 𝒟[simulateQ implE (sampleCoords P K c)] ≤
      ENNReal.ofReal (Real.exp
        (2 * n * (a * π * Δ ^ 2 / P.r ^ 2 + a * (a + 1) * Δ ^ 2 / (2 ^ 31 * (a - 1))))) := by
  have ha0 : 0 ≤ a := by linarith
  have ha1 : 0 < a - 1 := by linarith
  have ha1' : a - 1 ≠ 0 := ha1.ne'
  obtain ⟨E, hEd⟩ : ∃ E, E = a * π * Δ ^ 2 / P.r ^ 2 + a * (a + 1) * Δ ^ 2 / (2 ^ 31 * (a - 1)) :=
    ⟨_, rfl⟩
  rw [← hEd]
  have hE0 : 0 ≤ E := by
    rw [hEd]
    exact add_nonneg (div_nonneg (mul_nonneg (mul_nonneg ha0 Real.pi_pos.le) (sq_nonneg _))
      (sq_nonneg _)) (div_nonneg (mul_nonneg (mul_nonneg ha0 (by linarith)) (sq_nonneg _))
        (mul_pos (by norm_num) ha1).le)
  have hB : ∀ t, @renyiMGF _ ⊤ a (@evalDist m _ (samplerSpec.Range t) ⊤ (implF t))
      (@evalDist m _ (samplerSpec.Range t) ⊤ (implE t)) ≤
        ENNReal.ofReal (Real.exp ((a - 1) * E * onlineWeight t)) := by
    intro t
    cases t with
    | perturb =>
      have heq : @evalDist m _ (samplerSpec.Range .perturb) ⊤ (implF .perturb) =
          @evalDist m _ (samplerSpec.Range .perturb) ⊤ (implE .perturb) := by
        rw [hF, hE]
        rfl
      rw [heq]
      simp only [onlineWeight, mul_zero, Real.exp_zero, ENNReal.ofReal_one]
      exact FalconPrecision.RenyiPath.renyiMGF_self_le ha _ (evalDist_apply_univ_le_one _)
    | online x =>
      rw [hF, hE]
      simp only [answer, id, onlineWeight, mul_one]
      have h := Lemma5.renyiDiv_shift_le P.r x (fp x - x) a hr ha
      rw [add_sub_cancel] at h
      refine (renyiMGF_le_of_renyiDiv_le ha h).trans
        (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ ha1.le)))
      have hδ : (fp x - x) ^ 2 ≤ Δ ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hfp x) 2
      rw [hEd]
      exact Lemma5.explicit_exponent_le_of_sq_le ha hδ
  have h := FalconPrecision.RenyiPath.renyiMGF_simulateQ_le_path ha implF implE
    (mul_nonneg ha1.le hE0) onlineWeight hB (pathSum_sampleCoords P K c)
  rw [renyiDiv_eq_rpow ha]
  calc _ ≤ ENNReal.ofReal (Real.exp ((a - 1) * E * (2 * n))) ^ (a - 1)⁻¹ :=
        ENNReal.rpow_le_rpow h (inv_nonneg.2 ha1.le)
    _ = _ := by
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (inv_nonneg.2 ha1.le),
          ← Real.exp_mul]
        congr 2
        field_simp

/-- **The fixed-point step** ([ZKLY26, p. 8-9, l. 277-282], explicit): if every online centre is
converted within `Δ`, then `R_a(P_fp ‖ P) ≤ exp(2n (aπΔ²/r² + a(a+1)Δ²/(2³¹(a-1))))`. -/
theorem renyiDiv_sample_le (P : Params) (K : Key n) (c : Fin 2 → Fin n → ℝ)
    (fp : ℝ → ℝ) {Δ : ℝ} (hfp : ∀ x, |fp x - x| ≤ Δ) (hr : 1277 / 1000 ≤ Lemma5.stdDev P.r)
    {a : ℝ} (ha : 1 < a) (implE implF : QueryImpl samplerSpec m)
    (hE : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implE t) = answer P id t)
    (hF : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implF t) = answer P fp t) :
    renyiDiv a 𝒟[simulateQ implF (sample P K c)] 𝒟[simulateQ implE (sample P K c)] ≤
      ENNReal.ofReal (Real.exp
        (2 * n * (a * π * Δ ^ 2 / P.r ^ 2 + a * (a + 1) * Δ ^ 2 / (2 ^ 31 * (a - 1))))) := by
  have hg : Measurable fun z : (Fin n → ℤ) × (Fin n → ℤ) => latticePoint K z.1 z.2 :=
    measurable_of_countable _
  simp only [sample, simulateQ_map]
  rw [evalDist_map _ hg, evalDist_map _ hg]
  exact (renyiDiv_map_le a ha _ _ hg).trans
    (renyiDiv_sampleCoords_le P K c fp hfp hr ha implE implF hE hF)

/-- **The fixed-point step against a reference law.** If the exact sampler is within
`R_{(pa-1)/(p-1)}(P ‖ ν) ≤ exp E` of a probability measure `ν`, then the fixed-point sampler has
`log R_a(P_fp ‖ ν) ≤ ((a - 1/p)/(a - 1)) · 2n (paπΔ²/r² + pa(pa+1)Δ²/(2³¹(pa-1))) + E`. -/
theorem renyiDiv_sample_le_of_renyiDiv_le (P : Params) (K : Key n) (c : Fin 2 → Fin n → ℝ)
    (fp : ℝ → ℝ) {Δ : ℝ} (hfp : ∀ x, |fp x - x| ≤ Δ) (hr : 1277 / 1000 ≤ Lemma5.stdDev P.r)
    (hL : 0 < P.L) {a p : ℝ} (ha : 1 < a) (hp : 1 < p) (implE implF : QueryImpl samplerSpec m)
    (hE : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implE t) = answer P id t)
    (hF : ∀ t, @evalDist m _ (samplerSpec.Range t) ⊤ (implF t) = answer P fp t)
    (ν : Measure (Fin 2 → Fin n → ℤ)) [IsProbabilityMeasure ν] {E : ℝ}
    (hν : renyiDiv ((p * a - 1) / (p - 1)) 𝒟[simulateQ implE (sample P K c)] ν ≤
      ENNReal.ofReal (Real.exp E)) :
    renyiDiv a 𝒟[simulateQ implF (sample P K c)] ν ≤
      ENNReal.ofReal (Real.exp ((a - 1 / p) / (a - 1) *
        (2 * n * (p * a * π * Δ ^ 2 / P.r ^ 2 +
          p * a * (p * a + 1) * Δ ^ 2 / (2 ^ 31 * (p * a - 1)))) + E)) := by
  have hr0 : 0 < P.r := Lemma5.pos_of_pos_stdDev (lt_of_lt_of_le (by norm_num) hr)
  have := isProbabilityMeasure_evalDist_sample P K c fp hr0 hL implF hF
  have := isProbabilityMeasure_evalDist_sample P K c id hr0 hL implE hE
  have hpa : 1 < p * a := by nlinarith
  have hw : 0 ≤ (a - 1 / p) / (a - 1) := by
    have : 1 / p < 1 := by rw [div_lt_one (by linarith)]; exact hp
    exact div_nonneg (by linarith) (by linarith)
  have hFE := renyiDiv_sample_le P K c fp hfp hr hpa implE implF hE hF
  refine (RenyiTriangle.renyiDiv_le_rpow_mul_renyiDiv ha hp _ _ ν).trans
    ((mul_le_mul' (ENNReal.rpow_le_rpow hFE hw) hν).trans (le_of_eq ?_))
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hw, ← Real.exp_mul,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

end Mitaka
