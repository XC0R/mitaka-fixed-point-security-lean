# MitakaFixedPoint

Kernel-checked Rényi loss of the fixed-point Mitaka sampler at the parameters of Table 2 of ePrint 2026/2521, for
one fixed key, with every hypothesis explicit.

A Lean 4 formalisation of the distributional analysis of

> Shiduo Zhang, Paul Kirchner, Xiuhan Lin, Yang Yu, *Efficient Fixed-Point Implementation of Mitaka*, IACR ePrint
> 2026/2521, 2026.

The Lean sources cite it as [ZKLY26], with page and line numbers of the ePrint PDF (the paper numbers its lines). The
paper states (p. 9, l. 289-292) that for Mitaka-512 and Mitaka-1024 with the parameters of its Table 2, "the Rényi loss
incurred by using the new sampler is at most 1.5 bits for up to `Q_s = 2⁶⁴` signatures" (the introduction, p. 2, l.
80-82: "at most 1.5 bits of security loss"). The paper prints no computation of this figure. This repository proves, in
Lean, the paper's Lemmas 1-5 (Lemma 5 for `r/√(2π) ≥ 1.277`) and Theorem 1 (per sampler call), Algorithm 4 (the
fixed-point centres) on integers and on 64-bit words, the fixed-point step at Algorithm 4's centres, the conditions of
Theorem 1 at the Table 2 decimals, and a 1.5-bit statement over a whole experiment of sampler calls; where these
statements differ from the paper's is listed in [LIMITS.md](LIMITS.md). The choice of the Rényi order, the conversion
to bits and the counting of sampler calls are ours, not the paper's; they are stated below and in
[LIMITS.md](LIMITS.md).

In the Lean comments, **M18** is the label of the two headline theorems `Mitaka.Key.headline_mitaka512` and
`Mitaka.Key.headline_mitaka1024`.

## The headline (M18)

Notation: `P` is `Params.mitaka512` (λ = 128, n = 512) or `Params.mitaka1024` (λ = 256, n = 1024), the decimals of
Table 2; `K : Key n` is a key `(f, g, F, G)` with its expanded data; `oa : OracleComp (gameSpec aux n) α` is one
experiment that makes auxiliary queries (adversary coins, salts, the hash: everything other than the sampler) and
sampler calls at target centres `c : Fin 2 → Fin n → ℝ`, each answered by a lattice point. Signing (hash, sample,
norm check, retry) is part of `oa`; each signing attempt is one sampler call. The fixed-point world
`fpWorld P K implA implF` answers a sampler call at `c` by running Algorithm 3 (`Mitaka.sample`) with the integer
samplers `implF`; the ideal world `implI` answers it from `D_{L(B),rs,c}` (`Key.gaussianQ0`).

`Mitaka.Key.headline_mitaka512` and `Mitaka.Key.headline_mitaka1024`: for every key `K`, every `u`, `A`, every family of
auxiliary oracles `aux` whose answer types are countable (`∀ t, Countable (aux.Range t)`), and every monad `m` with
`[Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]`, under the hypotheses

| Binder | Statement | Kind |
|---|---|---|
| `hK : K.Annular P` | condition 1 of Theorem 1: `q/α² ≤ abs(f(ζ))² + abs(g(ζ))² ≤ α²q` at the `n` embeddings (`α = 1.15`, `1.23`) | per key |
| `hN : K.NTRU P` | `fG − gF = q` | per key |
| `hu : K.GSCoeff u` | `u` is the Gram–Schmidt coefficient: `u(f*f + g*g) = g*G + f*F` | per key |
| `hr : K.UClose P u` | the stored `û` satisfies `‖u − û‖∞ ≤ 1/(2p_u)` | per key |
| `hC : K.CholeskyRoot P A` | `A` is lower triangular with `AA* = Σ_p` | per key |
| `hAc : K.AClose P A` | the stored `Â` has `Â₀₁ = 0` and every coefficient within `1/(2p_A)` of `A` | per key |
| `hF` | `implF` answers every integer-sampler query with the exact discrete Gaussian, the online ones at Algorithm 4's centre `q64Round c` (perfect integer samplers) | experiment |
| `hI` | in the ideal world, a sampler call at `c` returns each lattice point `x` with probability `D_{L(B),rs,c}(x)` | experiment |
| `hIA` | auxiliary queries are answered by the same `implA` in both worlds | experiment |
| `hcalls` | `oa` makes at most `(4/3)·2⁶⁴` (Mitaka-512) or `3·2⁶⁴` (Mitaka-1024) sampler calls along every execution (`PathSum samplerWeight oa _`) | experiment |

for every output type `α` (countable, measurable singletons), every measurable event `s` and every `T ≥ 1` in `ℝ≥0∞`:

```
T · 2^(−(λ − 1.5)) < Pr[s] in the fixed-point world   ⟹   T · 2^(−λ) < Pr[s] in the ideal world.
```

Conditions 2-4 of Theorem 1 at Table 2, `n = 2⁹` (`2¹⁰`), the width condition of Lemma 5 and
`abs(q64Round c − c) ≤ 2⁻⁶⁴` are proved inside, not assumed. `test/Axioms.lean` prints the binders of both theorems
as elaborated (`HYP|` lines), for comparison with this table.

The bit loss. `Mitaka.renyiDiv_game_le` composes a per-call bound `R_a ≤ exp X`, uniform in the centre, over at most
`S` sampler calls along every execution, to `R_a ≤ exp(X·S)`; `Mitaka.RealExponent.measure_lt_of_renyiDiv_le` turns
`R_a ≤ exp D` and `λ + (a − 1)·D/ln 2 ≤ a·L` into the implication above with loss `L`. The per-call constant is
`X = 2⁻⁸⁸ + b·1.216·10⁻²²` (Mitaka-512) and `X = 2⁻⁸⁸ + b·1.774·10⁻²³` (Mitaka-1024), `b = (pa − 1)/(p − 1)`, for
Rényi order `2 ≤ a ≤ 2¹⁹` and Hölder exponent `2 ≤ p ≤ 2¹⁰` (`Mitaka.Key.renyiDiv_call_le_mitaka512`, `…1024`). The
headline takes `a = 198` (Mitaka-512), `a = 738` (Mitaka-1024) and `p = 1024`; the inequality
`λ + (a − 1)·X·S/ln 2 ≤ a·1.5` at the two call budgets is proved with exact rationals and Mathlib's
`0.6931471803 < ln 2` (`Mitaka.headline_arith_mitaka512`, `Mitaka.headline_arith_mitaka1024`).

Related statements in `Mitaka/Headline.lean`:

- `Mitaka.Key.headline_of_mitaka512`, `…1024`: the same implication for every `a`, `p` in the ranges above, every
  call budget `S`, every `λ` and every loss `L` that satisfy `λ + (a − 1)·X·S/ln 2 ≤ a·L`.
- `Mitaka.Key.headline_tableRate_mitaka512`, `…1024`: loss 1.3 bits with at most `2⁶⁴(1 + 0.01211)` sampler calls
  (Mitaka-512) and 0.7 bits with at most `2⁶⁴(1 + 0.0007231)` (Mitaka-1024), along every execution. These budgets
  come from Table 2's measured per-attempt failure rates (1.196%, 0.0722%), which are empirical; nothing here proves
  them.
- `Mitaka.headlineWorlds_exist`: over idealised oracles (auxiliary oracles, a perfect integer Gaussian sampler, an ideal
  lattice-Gaussian oracle), for every key with `fG − gF = q` and parameters with `q, r, s, L > 0`, there are `implA`,
  `implF`, `implI` with `hF`, `hIA` and `hI`. No `ProbComp` implementation is claimed.

Scope in one paragraph (details in [LIMITS.md](LIMITS.md)): the theorems hold for one fixed key that satisfies the six
per-key hypotheses; key generation, key expansion and a statement averaged over keys are outside them, and the per-key
hypotheses are shown jointly satisfiable in Lean at `n = 1` with toy parameters (`q = 2`; `witness_hypotheses`), not for
a key with `n = 512` or `1024`. The integer samplers are assumed perfect (no CDT truncation is charged). Mitaka signing
has no hard cap on retries, so a signer meets `hcalls` with a global budget of sampler calls. No UF-CMA game is defined:
the loss is measured against the ideal lattice Gaussian `D_{L(B),rs,c}`, and `T` is a parameter, not a running time.

## Steps of the paper

All names below are in namespace `Mitaka`.

| Paper | Lean | File |
|---|---|---|
| Lemma 1 ([Pei10, Lemma 2.4]) | `LatticeGaussian.rhoSum_one_mem_Icc` (`ℤ^m`), `LatticeGaussian.rhoSum_mem_Icc` (`L(B)`) | `Mitaka/Smoothing.lean` |
| Gaussian Poisson summation over `ℤ^m` (used for Lemma 1) | `LatticeGaussian.tsum_exp_neg_quadForm_eq` | `Mitaka/Poisson.lean` |
| Lemma 2: `‖B̂‖₂ ≤ β(p_u)`, `σ_min(B̂) ≥ q/β(p_u)` | `Key.norm2_bHat_le`, `Key.div_beta_le_sigmaMin_bHat` | `Mitaka/Lemma2.lean` |
| Lemma 3: `‖Σ_e‖₂ ≤ τ̄s²`, `‖Σ_e‖_F` bound | `Key.norm2_sigmaE_le`, `Key.normF_sigmaE_le` | `Mitaka/Lemma3.lean` |
| Lemma 4: `log R_v(𝒫‖𝒬_e) ≤ (9v/8)(log κ)²` | `Key.renyiDiv_sample_gaussianQe_le` | `Mitaka/Lemma4.lean` |
| Lemma 5 (for `r/√(2π) ≥ 1.277`) | `Lemma5.renyiDiv_le_of_abs_sub_le` | `Mitaka/Lemma5.lean` |
| Scale change in the proof of Theorem 1 | `Key.renyiDiv_gaussianQe_le_tauBar` | `Mitaka/ScaleChange.lean` |
| Theorem 1: `log R_a(𝒫‖𝒬₀) ≤ ℰ_a` under conditions 1-4 | `Key.renyiDiv_sample_gaussianQ0_le` | `Mitaka/Theorem1.lean` |
| Rényi weak triangle inequality (general `p`) | `RenyiTriangle.renyiDiv_le_rpow_mul_renyiDiv` | `Mitaka/RenyiTriangle.lean` |
| `η_ϵ(L(B))` from the Gram–Schmidt profile ([Jia+26, Theorem 3]) | `LatticeGaussian.smoothingParam_le_profile`; at the Mitaka basis `Key.smoothingParam_basisMat_le` | `Mitaka/SmoothingGS.lean`, `Mitaka/SmoothingNTRU.lean` |
| Algorithm 4 on `ℤ` and on 64-bit words; `abs(q64Round c − c) ≤ 2⁻⁶⁴` | `Algorithm4.algorithm4_correct`, `Algorithm4.runBV_noOverflow`, `Algorithm4.abs_q64Round_sub_le` | `Mitaka/Algorithm4.lean` |
| Fixed-point step at Algorithm 4's centres, combined with Theorem 1 | `Key.renyiDiv_sample_q64Round_gaussianQ0_le` | `Mitaka/FixedPointCentre.lean` |
| Conditions 2-4, `τ̄`, `ℰ_a` at Table 2 (certified) | see the module doc | `Mitaka/Table2.lean` |
| Per-key hypotheses jointly satisfiable at `n = 1` | `witness_hypotheses` | `Mitaka/Lemma3.lean` |

The module docs give the paper's statements with page and line; [LIMITS.md](LIMITS.md) lists where the Lean
statements differ from them.

## Kernel checks

`lake build` checks every proof with the Lean kernel; it reports no `sorry`. `lake env lean test/Axioms.lean` runs
362 `#print axioms` commands, one for every public theorem of `Mitaka/*.lean` (356) and six theorems of the vendored
modules; each output lists a subset of `propext`, `Classical.choice` and `Quot.sound`. It also prints the
hypotheses of the two headline theorems (`HYP|` lines) and the recursors of class inductives (classes that are not
structures) reached by them (`REC|` lines; Lean issue #14875): six recursor constants of `Finite`, `Nonempty` and
`WellFounded`, classes declared in Lean core and Mathlib.

The two headline statements were also checked with `lake comparator` of Lean v4.36.0 (with `--paranoid`, without
comparator's own sandbox, in a container without network) against a Challenge file extracted from these sources: the 106
constants of `Mitaka` and `FalconPrecision` that the two statements reach, with the two target proofs replaced by
`sorry`. Comparator reported the statements and every constant they reach identical (up to binder names and binder info)
to the Challenge's, and proofs that use no axiom beyond `propext`, `Classical.choice` and `Quot.sound`. The exported
solution was accepted by Lean's default kernel, by the checkers bundled with Lean v4.36.0 (`leanchecker-paranoid`,
`lean4lean`, `nanoda_bin` 0.4.17, `con-leche`, `con-ron`), and by nanoda 0.4.32 (`ammkrn/nanoda_lib` commit
`0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929`) built from source. That run used an earlier revision of these sources.
Between it and this release, the Lean modules changed in comments and nowhere else (`Mitaka/Table2.lean`,
`Mitaka/ScaleChange.lean`, `Mitaka/Witness.lean`, the module doc of `Mitaka/Headline.lean` and a copyright header in
`Mitaka.lean`), the doc comment of `lakefile.lean` changed, `test/Axioms.lean` was added, and the export of
`Mitaka.Headline` (`lean4export` 3.1.0, the file the kernel checks read) is byte-identical for both revisions. The
Challenge file, the scripts and the logs of that run are not part of this repository. What these checks do not show is
listed in [LIMITS.md](LIMITS.md#kernel-checks).

## Vendored modules

`FalconPrecision/` holds eight modules of FalconPrecision release 0.4.0
(https://github.com/XC0R/falcon-fixed-point-security-lean, commit `1303738996923e3f8ab0989ada7576284064b4c1`), a
formalisation of ePrint 2026/1531 ([DFLP26] in the comments) by the same author, under the same license, with their
original headers, module names and namespaces. Six (`Taylor2`, `RenyiShift`, `ThetaTail`, `Lemma4`, `NumTail`,
`Errors/PathCompose`) are byte-identical to that commit. `RenyiHybrid` and `RenyiPath` differ in three proof lines,
for lemmas renamed in Mathlib (`ENNReal.le_tsum` → `le_tsum`, `ENNReal.tsum_prod'` → `tsum_prod'`,
`ENNReal.tsum_le_tsum` → `tsum_le_tsum`); no statement differs.

## References used in the sources

- [ZKLY26] Shiduo Zhang, Paul Kirchner, Xiuhan Lin, Yang Yu, *Efficient Fixed-Point Implementation of Mitaka*, IACR
  ePrint 2026/2521, 2026.
- [Jia+26] Huiwen Jia, Shiduo Zhang, Yang Yu, Chunming Tang, *Revisiting the Concrete Security of Falcon-type
  Signatures*, IACR ePrint 2026/096, 2026.
- [DFLP26] Daniel De Almeida Braga, Pierre-Alain Fouque, Bachir Lachguel, Thomas Prest, *Toward a Secure Fixed-Point
  Implementation of the Falcon Signature Scheme*, IACR ePrint 2026/1531, 2026.
- [Pei10] Chris Peikert, *An efficient and parallel Gaussian sampler for lattices*, CRYPTO 2010, LNCS 6223,
  pp. 80-97.
- [MR04] Daniele Micciancio, Oded Regev, *Worst-case to average-case reductions based on Gaussian measures*, 45th
  FOCS, 2004, pp. 372-381.
- [GPV08] Craig Gentry, Chris Peikert, Vinod Vaikuntanathan, *Trapdoors for hard lattices and new cryptographic
  constructions*, 40th ACM STOC, 2008, pp. 197-206.
- [Ban95] W. Banaszczyk, *Inequalities for convex bodies and polar reciprocal lattices in Rⁿ*, Discrete &
  Computational Geometry 13:217-231, 1995.

## Related work

- Thomas Espitau, Pierre-Alain Fouque, François Gérard, Mélissa Rossi, Akira Takahashi, Mehdi Tibouchi, Alexandre
  Wallet, Yang Yu, "Mitaka: A Simpler, Parallelizable, Maskable Variant of Falcon", EUROCRYPT 2022, LNCS 13277,
  pp. 222-253 (IACR ePrint 2021/1486): the Mitaka signature scheme, with the hybrid sampler in place of Falcon's
  fast Fourier sampler.
- Thomas Espitau, Thi Thu Quyen Nguyen, Chao Sun, Mehdi Tibouchi, Alexandre Wallet, "Antrag: Annular NTRU Trapdoor
  Generation – Making Mitaka as Secure as Falcon", ASIACRYPT 2023, LNCS 14444, pp. 3-36: the annular trapdoor
  generation used for the parameter sets of Table 2.
- Huiwen Jia, Shiduo Zhang, Yang Yu, Chunming Tang, "Revisiting the Concrete Security of Falcon-type Signatures",
  IACR ePrint 2026/096, 2026: concrete security analysis of Falcon-type signatures from the profile of the NTRU
  trapdoor bases; its Theorem 3 bounds the smoothing parameter of a lattice from a basis profile.
- Pierre-Alain Fouque, Phillip Gajland, Hubert de Groote, Jonas Janneck, Eike Kiltz, "A Closer Look at Falcon",
  IACR ePrint 2024/1769 (EUROCRYPT 2026): a security proof of Falcon in the random oracle model through an adaptation
  of the GPV framework to the Rényi divergence, and an analysis of Falcon's FFO sampler.
- Metin Bektaş, with Erdem Alkım, Erem Ersoy, Muhammed Said Gündoğan, "ATMACA: Lattice-Based Threshold Signing for
  FALCON", slides, NIST Threshold Call Preview Talks, presented 2026-10-06: state a Rényi-divergence precision
  analysis of a fixed-point hybrid sampler with Antrag keys, with outcomes below 1 bit (d = 512) and below 5 bits
  (d = 1024) at κ = 55 and 2⁶⁴ attempts.
- Navid Abapour, "Sharper and Closed-Form Attacks on SIS When Modulus Is Small", IACR ePrint 2026/1349, 2026:
  reports a Mitaka-512 forgery on the instance `(n, q, ν) = (512, 257, 1470.71)`, a different modulus from the
  `q = 12289` of Table 2.

## Building

Requires [elan](https://github.com/leanprover/elan). The toolchain and the dependencies are pinned
(`lean-toolchain`, `lakefile.lean`, `lake-manifest.json`): Lean `v4.36.0`, VCVio `f1e63c78`, Mathlib `fc4f59e5`.

```sh
lake exe cache get              # optional: download Mathlib's build cache
lake build                      # every module (Mitaka and the vendored FalconPrecision modules)
lake env lean test/Axioms.lean  # the axiom check, the hypotheses of the headline, the class-inductive recursors
```

For this release, the last two commands were run on x86_64 and on aarch64 (Linux, Lean `v4.36.0`, every dependency
at its pinned commit, no previously built module of this repository): `lake build` reported no error, no warning and
no `sorry`; each of the 362 `#print axioms` outputs lists a subset of `propext`, `Classical.choice` and
`Quot.sound`, and the output of `test/Axioms.lean` was the same on both.

## Acknowledgements

Developed with the assistance of Claude models (Anthropic).

## License

Apache 2.0, as VCVio and Mathlib. Some files contain parameter values and quotations from ePrint 2026/2521; how they
are used is in [NOTICE](NOTICE).
