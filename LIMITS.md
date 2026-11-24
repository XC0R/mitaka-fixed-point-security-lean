# Limits

What the theorems of this repository assume, what they do not prove, where the Lean statements differ from
[ZKLY26] (Zhang, Kirchner, Lin, Yu, ePrint 2026/2521), the gaps in the sources, the open items, and what the kernel
checks do not show. Page and line numbers are those of the ePrint PDF. Names are in namespace `Mitaka`.

## Hypotheses of the headline

`Key.headline_mitaka512` and `Key.headline_mitaka1024` are conditional statements. Their hypotheses, all for one fixed
key or about the experiment:

- The auxiliary oracles have countable answer types (`∀ t, Countable (aux.Range t)`), and the output type of the
  experiment is countable with measurable singletons.
- Condition 1 of Theorem 1 (`hK : Key.Annular`): `q/α² ≤ abs(f(ζ))² + abs(g(ζ))² ≤ α²q` at the `n` complex
  embeddings, `α = 1.15` (Mitaka-512) and `1.23` (Mitaka-1024). A property of annular (Antrag) key generation,
  assumed per key. The paper states it at every primitive `2n`-th root of unity; `Key.Annular.of_isPrimitiveRoot`
  derives our form from that one.
- The NTRU equation `fG − gF = q` over `ℝ[X]/(Xⁿ + 1)` (`hN : Key.NTRU`), with `0 < q` explicit (Lemma 2 is false
  at `q = 0`); `Key.NTRU.of_negacyclicConvCoeff` derives it from the coefficient form.
- The Gram–Schmidt coefficient `u` given by its equation `u(f*f + g*g) = g*G + f*F` (`hu : Key.GSCoeff u`), since
  `ℝ[X]/(Xⁿ + 1)` is not a field. That such a `u` exists under condition 1 is not proved.
- `‖u − û‖∞ ≤ 1/(2p_u)` for the stored `û` (`hr : Key.UClose`). The offline key expansion (`long double` in the
  paper's implementation) is not analysed; the bound is more general than exact rounding (`Key.UClose.of_round`
  shows that rounding implies it).
- A lower-triangular `A` with `AA* = Σ_p` (`hC : Key.CholeskyRoot`); the paper takes the Cholesky root, with positive
  diagonal.
- `Â₀₁ = 0` and every coefficient of `A − Â` at most `1/(2p_A)` in absolute value (`hAc : Key.AClose`;
  `Key.AClose.of_round` shows that rounding implies it).
- Perfect integer samplers (`hF`), the one assumption about the implementation's sampler: the perturbation samples
  are exact `D_{ℤ,Lr,0}` and the online samples exact `D_{ℤ,r,c'}` at Algorithm 4's centre `c' = q64Round c`. The
  offline CDT (88-bit, cut at 28 for Mitaka-512 and 29 for Mitaka-1024) and the online sampler (CDT maximum 14,
  bimodal proposal, polynomial `exp` rejection) are modelled as exact.
- The ideal world (`hI`): a sampler call at `c` is answered by `𝒬₀ = D_{L(B),rs,c}` (`Key.gaussianQ0`), the
  reference law of the loss. This defines the reference world; it is not an assumption about the implementation.
- Every auxiliary query (adversary coins, salts, the hash) is answered by the same implementation in both worlds
  (`hIA`). The signing logic (hash, norm check, retry) is part of the experiment `oa`, so it is the same function of
  the history in both worlds; the two worlds differ in the sampler.
- The call budget (`hcalls`): at most `(4/3)·2⁶⁴` (Mitaka-512) or `3·2⁶⁴` (Mitaka-1024) sampler calls along every
  execution. Mitaka signing has no hard cap on retries (it retries until the norm check passes), so a signer meets
  this hypothesis with a global budget of sampler calls. Table 2's measured per-attempt failure rates (1.196%,
  0.0722%) give on average about `1.012·2⁶⁴` and `1.0007·2⁶⁴` calls for `2⁶⁴` signatures; they are empirical, and
  nothing here proves them. `Key.headline_tableRate_mitaka512`, `…1024` take budgets computed from them
  (`2⁶⁴(1 + 0.01211)`, `2⁶⁴(1 + 0.0007231)`, from the upper ends `f = 1.1965%`, `0.07225%` of the printed rates'
  rounding intervals and `c ≥ f/(1 − f)`), required along every execution, and give 1.3 and 0.7 bits.

`hF` and `hI` are satisfiable by idealised oracles (`headlineWorlds_exist`); no `ProbComp` has a discrete-Gaussian
or lattice-Gaussian law, and none is claimed. Proved inside the headline, not assumed: `n = 2⁹` (`2¹⁰`) and the
Lemma 5 width, conditions 2-4 of Theorem 1 at Table 2, `0 < q`, `0 < ϵ ≤ 1/2`, the positivity of `r`, `s`, `L`,
`abs(q64Round c − c) ≤ 2⁻⁶⁴` (`Algorithm4.abs_q64Round_sub_le`), the bit-loss inequality, and the exact-sampler world
of the per-call bound.

## Not proved

- One fixed key. The theorems hold for one key that satisfies the six per-key hypotheses; key generation is outside
  the experiment. A statement averaged over key generation is neither stated nor proved; it would need the per-key
  hypotheses for every generated key.
- The per-key hypotheses are shown jointly satisfiable in Lean at `n = 1` (`q = 2`; `witness_hypotheses`). No key
  with `n = 512` or `1024` is checked.
- The 1.5-bit computation is ours: the paper prints none. Ours are the bit-loss rule (from `R_a ≤ exp D`, loss
  `λ/a + ((a − 1)/a)·D/ln 2`), the orders `a = 198` (Mitaka-512) and `a = 738` (Mitaka-1024), the Hölder exponent
  `p = 1024`, and the reading of "`Q_s = 2⁶⁴` signatures" (p. 9, l. 291) as sampler calls along every execution.
- The integer samplers are assumed perfect. The offline CDT truncation and the online sampler are not analysed, and
  the truncated mass is not charged.
- Centres are exact real numbers in the model. That the C implementation (NTT modulo two 31-bit primes, CRT,
  Algorithms 3 and 4 in C) computes the same values is not proved. `Algorithm4.runBV` models the operations the
  paper names on 64-bit words, not the paper's source code, which was not available; the reciprocal-multiplication
  divisions by `q` (p. 13, l. 379-382) are not modelled (`runBV` uses unsigned division).
- The bounds of §4.3 (Table 4, the bound on `A_int`, CRT exactness `ℓ₀ℓ₁ < 2⁶²`, the NTT) are not proved; Algorithm 4
  takes them as the hypothesis `Algorithm4.Table4Input`. So the link between the implementation's inputs to
  Algorithm 4 and the model's exact centres is not proved.
- The modular norm check (Lemma 6, Eq. (1)) is not modelled, and how its statistical-distance term would enter the
  loss is not addressed.
- The paper's statement that its analysis "does not rely on any empirical assumptions" (p. 2, l. 78-79) concerns
  the error bounds of intermediate values. Key expansion, the integer samplers and the retry rate rest on assumptions
  or measurements here.
- No UF-CMA game is defined. Table 2's security estimates and failure rates are taken from the paper, not proved; the
  loss is measured against the ideal lattice Gaussian `D_{L(B),rs,c}`; `T` is a parameter, not a running time (no
  cost model ties it to the experiment).

## Differences from the paper's statements

- Lemma 5 is proved for `r/√(2π) ≥ 1.277` (`r ≥ 1.277·√(2π) ≈ 3.20`), through the explicit theta tail of the vendored
  `FalconPrecision.NumTail`; the paper needs `r ≥ η_ϵ(ℤ)` with `ϵ ≤ 1/4` (about `r ≥ 0.81`). Table 2's widths 3.305
  and 3.34 satisfy it.
- Lemma 5's `(1 + O(ϵ))` is explicit: `(1 + σ²/2³⁰)`, and `(1 + 2⁻²⁹)` at Table 2.
- The Rényi weak triangle inequality is proved in a general-`p` form on countable measurable spaces with probability
  measures; the paper uses the instance `p = (2a − 1)/a` on `L(B)`.
- The bounded-ratio step of Lemma 4 uses `Measure.tilted` with an a.e. bound and Hoeffding's lemma (the same constant
  as the paper's route through Popoviciu's inequality).
- `Params` carries no `n` and no `ϵ`: the Table 2 theorems hold for every `n`, and the headline instantiates
  `n = 512`, `1024`. `Params` does not force `q, p_u, p_A, L > 0`; these are discharged at Table 2.
- `Key` allows a general 2×2 `Â` (the paper's is lower triangular) and omits the size facts
  `‖f‖∞, ‖g‖∞, ‖F‖∞, ‖G‖∞ ≤ 127` and `abs(u_int,i) ≤ p_u/2`, which the unproved implementation link would need.
- The online samples of one vector are queried in index order (the paper fixes no order; the law is the same).
- Widths: `σ = r/√(2π)` (VCVio's `discreteGaussianMeasure`) against the paper's `ρ_r`.
- `n = 2^ℓ` with `ℓ ≥ 0` (the paper: `ℓ ≥ 1`); real coefficients; `B̂⁻¹` as the explicit `U_û B⁻¹` with both
  inverse identities; `λ_max` as the Rayleigh maximum.
- Some hypotheses are carried but partly used: `Key.one_add_sq_norm2_eq` and `Key.lambdaMax_le` carry `n = 2^ℓ` but
  use `0 < n`; `Key.norm2_aMat_le` does not use `s > β`.
- `smoothingParam ϵ B = 0` for a singular `B` or `ϵ ≤ 0`, so `GeSmoothing` holds for every singular `M`; every
  theorem that uses them carries `det ≠ 0` and `0 < ϵ`.
- Lattices are full rank, `L(B)` with a square invertible basis, and centres range over all of `ℝ^m`; `0 < s` is added
  at p. 3, l. 105; the bound on `η_ϵ(ℤ^m)` is for `m ≥ 1`.
- [Jia+26, Theorem 3] is proved for any invertible real `B`, any `G ≥ max‖b̃_i‖`, with the condition `S < 1`
  stated; its slab bound is two-sided, for any shift, with `≤` for the sources' `<`.
- Poisson summation is stated with the phase `e^{+2πi⟨y,c⟩}` (the paper: `e^{−2πi⟨v,c⟩}`, the same by `y ↦ −y`), and
  `φ` in a real `cos` form.
- Statements not in the paper (bridges, `rhoSum_le_rhoSum_zero`, `smoothingParam_anti`, closed-form and fixed-point
  corollaries, witnesses) and generalisations (`rho_eq_exp_quadForm`, `rho_congr` without `det` hypotheses).
- Lemma 4 under fewer hypotheses (`0 < ϵ < 1`, no `a`, no condition 4); the support is stated on `ℤ^{2n}`
  coordinates; the density as `∃ w ∈ [κ⁻¹, κ²]` everywhere.
- `abs(θᵢ) ≤ τ̄` as a quadratic-form bound; `𝒬_e` with any factor `M` (Mitaka: `CFC.sqrt`); the bound on `abs(φ″)`
  stated existentially.
- Some displays are stated as inequalities or kept private: the integral equality of p. 7, l. 244 (as
  `detTerm_le`), the eigenvalue formula of l. 240 (private), the identity of l. 242 (for coordinate laws; `≤` for
  `𝒬_e`, `𝒬₀`).
- Algorithm 4 is proved on `ℤ` for all integer inputs and `b + t ≤ 64` (the paper: under the bounds of §4.3); the
  words need `h + ⌊ℓ/2^b⌋` to be a signed 64-bit integer; `b`, `t` are general with `q = 12289` fixed; reassigned
  variables are indexed; the error statements hold for every real `c`.

## Gaps in the sources

- The paper does not compute the 1.5-bit figure: the order `a`, the rule from Rényi divergence to bits, how Theorem 1
  and the fixed-point step combine, whether `Q_s` counts signatures or sampler calls, and how the TV term of Lemma 6
  enters are not stated. The computation here is ours (above).
- The paper does not bound `η_ϵ(L(B))`, so condition 4 is not shown at Table 2 in the paper. Here
  `Key.smoothingParam_basisMat_le` (`η_ϵ(L(B)) ≤ α√q·√(ln(4n(1 + 1/ϵ))/π)`, ours, through [Jia+26, Theorem 3])
  gives a sufficient condition, checked at Table 2 in `Mitaka/Table2.lean`.
- Table 2 gives rounded decimals with no link to code (the implemented `s`, `r` are not known here), and the paper
  does not say which bound on `η_ϵ(ℤⁿ)` it uses. `Params.mitaka512` and `Params.mitaka1024` fix the printed
  decimals; that the implementation's `s`, `r` equal them is not proved.
- That Lemma 5 "requires error smaller than 2⁻⁴⁴" (p. 13, l. 392-393) is not derived in the paper and not stated
  here; the fixed-point step takes the error bound `Δ` explicitly.
- The coefficient-to-evaluation bound holds at primitive `2n`-th roots of unity for every `n` and fails at
  non-primitive roots of `Xⁿ + 1` (which exist exactly when `n` is not a power of two); the paper fixes `n = 2^ℓ`.
- A convexity step in the trace bound of Lemma 2 (`γ ↦ γ(1 + abs(δ)²) + q²/γ` is maximal at `γ = α²q`) is implicit in
  the paper and proved here.
- The fixed-point step (p. 8-9) does not define `P_fp` and does not name its composition bound; here one
  `OracleComp` runs under two query implementations, with `fp` any map with `abs(fp x − x) ≤ Δ` and path budgets
  over the `2n` online calls.
- The termwise differentiation of the dual sum in the proof of Theorem 1 is used without justification in the
  paper; `exists_deriv2_logMass_le` proves it (`hasDerivAt_tsum_of_isPreconnected` with a Gaussian majorant).
- [Jia+26, Theorem 3]: its proof uses `S < 1`, which the statement does not state; the remark that `Λ*` has no
  non-zero point inside `P(B̃*)` is not used here; the integrality of `B` is not used.
- [Jia+26, Lemma 8] is not used. [Jia+26, Lemma 9] and Theorem 3 use [Ban95, Lemma 2.4] in slab form, which
  `tsum_slab_le` proves; the wording of [Ban95, Lemma 2.4] itself was not checked against [Ban95].
- In the proof of its Theorem 3, [Jia+26] p. 14 writes `ρ_s` for `ρ_{1/s}`.
- [Jia+26]'s closed form `ϵ′ ≈ 1.15ϵ/abs(ln(ϵ/4n))` and its per-key losses (its Table 5) are not used.
- Sources cited by the paper whose mathematics was not checked for this work: EFG+22 (only its abstract was read, for
  the related-work line of the README), ENS+23 (not read; its related-work line rests on [ZKLY26]'s reference list and
  p. 9), DGPY20, Pre15, Per26.

## Open items

- The coefficient-to-evaluation bound of `Mitaka/Embedding.lean` could be generalised to `n ≥ 1` with
  `IsPrimitiveRoot ζ (2n)` by the same proof; not done.
- Lean issue #14875 (recursors of class inductives across a module boundary): whether it is fixed at Lean v4.36.0
  was not checked. `test/Axioms.lean` lists the six such recursor constants that the headline reaches (of `Finite`,
  `Nonempty`, `WellFounded`; declared in Lean core and Mathlib); `Nonempty.casesOn`, `Nonempty.rec` and
  `WellFounded.casesOn` are used across module boundaries in Lean core and Mathlib.
- In the docstrings of `Mitaka/Headline.lean`, `K` names both the key and the call budget.
- Not read: a written paper on ATMACA (if any), the body of SOLMAE (ePrint 2026/817) and of ePrint 2026/2583.
- Zulip and open Mathlib pull requests were not searched.

## Kernel checks

The README's comparator and second-kernel paragraph does not show:

- That comparator ran in its own sandbox: it ran with `--inadvisably-no-sandbox` (comparator prints that such a run
  is not trustworthy), inside a rootless container without network.
- That the Challenge states the intended mathematics: comparator shows identity with the Challenge file (up to binder
  names and binder info). Fidelity of the statements to [ZKLY26] rests on reading them against the paper, which any
  reader can do. Binder info and binder order are not compared by any tool here; numeral types are not visible in the
  `HYP|` output of `test/Axioms.lean` (`(2 : ℝ≥0∞) ^ (-(128 : ℝ))` prints as `2 ^ (-128)`).
- Anything about the definitions of Mathlib, VCVio or Lean core: the Challenge imports the same libraries, so their
  constants are the same on both sides by construction and the comparison says nothing about them; the identity covers
  the 106 constants of `Mitaka` and `FalconPrecision`.
- An independent check by the bundled `nanoda_bin` 0.4.17: it predates nanoda's soundness fixes #47, #60, #64, #68,
  #73, #74, #76, #79, #81 and #83, and it accepted a Lean Kernel Arena file that proves `False`
  (`nested-name-capture`). Its acceptance is recorded, not relied on; the nanoda result cited is 0.4.32.
- That `leanchecker-paranoid` and `lean4lean` are independent of Lean's C++ kernel: they are not.
- That `con-leche` and `con-ron` are two independent checks: `con-ron` is a port of `con-leche`. That the bundled
  versions are those with a formal soundness proof was not checked. `con-leche --compare` was not run.
- That any checker is independent of `leanexport` (lean4export 3.1.0) or of the Lean build that produced the
  `.olean` files: all read one export.
- Negative evidence for every checker on every known kernel bug: on Lean Kernel Arena bug exports, `con-leche` and
  `con-ron` declined `nested-name-capture` and `rec-missing-ih` and gave no isolated verdict on a wrong `Nat.rec`
  rule; `lean4lean` rejected the wrong-`Nat.rec`-rule export at `Nat.beq`'s form; comparator counts any non-zero exit
  of a checker (also a decline or an abort) as a rejection.
- Anything about the step theorems other than the two headline theorems, or about Lean issue #14875.
- That the Rust compiler that built nanoda 0.4.32 (rustc 1.100.0, from its signed release archive, with 28 vendored
  crates) is trustworthy; it is in nanoda's trusted base.
