/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
import Mitaka
-- The v4.36.0 definitions of the core overflow predicates used by
-- `Mitaka.Algorithm4.TraceBV.NoOverflow`, and the statements of the core lemmas the 64-bit layer of
-- `Mitaka/Algorithm4.lean` use. Not counted by the axiom check (only `#print axioms` lines are).
#print BitVec.saddOverflow
#print BitVec.ssubOverflow
#print BitVec.smulOverflow
#print BitVec.sdivOverflow
#print BitVec.uaddOverflow
#print BitVec.usubOverflow
#print BitVec.umulOverflow
#check BitVec.toInt_add_of_not_saddOverflow
#check BitVec.toInt_sub_of_not_ssubOverflow
#check BitVec.toInt_mul_of_not_smulOverflow
#check BitVec.toInt_sdiv_of_ne_or_ne
#check BitVec.toNat_add_of_not_uaddOverflow
#check BitVec.toNat_mul_of_not_umulOverflow
#check BitVec.toNat_sub_of_not_usubOverflow
#check BitVec.toInt_sshiftRight
#check Int.shiftRight_eq_div_pow
#check BitVec.toInt_eq_toNat_of_lt
#check BitVec.toInt_eq_toNat_cond
#check BitVec.toInt_lt
#check BitVec.le_toInt
#check BitVec.toInt_zero
#check BitVec.toNat_udiv
#check BitVec.udiv_eq
#check BitVec.toNat_ushiftRight
#check BitVec.toNat_and
#check BitVec.toNat_ofNat
#check BitVec.eq_of_toNat_eq
#check BitVec.or_zero
-- The hypothesis surface of the two headline theorems, read from each constant's elaborated type
-- (`forallTelescope`, no reduction, so the stated binders are listed), one `HYP|` line per binder:
-- index, user name, binder info, kind (`Prop`, `Prop-instance`, `instance`, `data`), and the type
-- with `pp.fullNames`; for a data or data-instance binder whose type is a structure, its
-- `Prop`-valued fields (instance binders included); last, the conclusion.
-- Compare with the hypotheses listed in README.md.
-- Every recursor or auxiliary recursor (`casesOn`, `recOn`, `brecOn`, ...) of a
-- `class inductive` (a class that is not a structure) in the transitive constant closure (types
-- and values) of the two headline theorems, with the module declaring the class and the modules
-- whose constants use it (Lean issue #14875: class-inductive recursors across a module
-- boundary). Output lines carry `HYP|` / `REC|`
-- prefixes; neither is counted by the axiom check (only `#print axioms` lines are).
open Lean Meta Elab Command in
elab "#hypothesis_surface " ids:ident+ : command => do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let ci ← getConstInfo n
    liftTermElabM <| withOptions (fun o => o.setBool `pp.fullNames true) do
      forallTelescope ci.type fun xs body => do
        let env ← getEnv
        for i in [0:xs.size] do
          let x := xs[i]!
          let ld ← x.fvarId!.getDecl
          let ty ← inferType x
          let isCls := (← isClass? ty).isSome
          let isP ← isProp ty
          let kind := if isCls then (if isP then "Prop-instance" else "instance")
            else if isP then "Prop" else "data"
          let bi := match ld.binderInfo with
            | .default => "explicit"
            | .implicit => "implicit"
            | .strictImplicit => "strict-implicit"
            | .instImplicit => "inst-implicit"
          let tyS := (← ppExpr ty).pretty 100000
          logInfo m!"HYP|{n}|{i}|{ld.userName.eraseMacroScopes}|{bi}|{kind}|{tyS}"
          if kind == "data" || kind == "instance" then
            if let some s := ty.getAppFn.constName? then
              if isStructure env s then
                let mut props : Array Name := #[]
                for f in getStructureFieldsFlattened env s (includeSubobjectFields := false) do
                  if let some p := getProjFnForField? env s f then
                    let pty := (← getConstInfo p).type
                    if ← forallTelescopeReducing pty fun _ b => isProp b then
                      props := props.push f
                logInfo m!"HYP|{n}|{i}|{ld.userName.eraseMacroScopes}|structure {s}|\
                  Prop fields: {props}"
        logInfo m!"HYP|{n}|conclusion|{(← ppExpr body).pretty 100000}"

open Lean Meta Elab Command in
elab "#class_recursors " ids:ident+ : command => do
  let env ← getEnv
  let modOf (c : Name) : String := match env.getModuleIdxFor? c with
    | some i => toString env.header.moduleNames[i.toNat]!
    | none => "(this file)"
  let mut roots : Array Name := #[]
  for id in ids do
    roots := roots.push (← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id)
  let mut seen : NameSet := {}
  let mut todo : Array Name := roots
  let mut users : Std.HashMap Name (Array String) := {}
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    let some ci := env.find? c | continue
    let used := ci.type.getUsedConstants ++
      ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
    for d in used do
      let isRec := (match env.find? d with | some (.recInfo _) => true | _ => false) ||
        isAuxRecursor env d
      if isRec && isClass env d.getPrefix && !isStructure env d.getPrefix then
        let us := users.getD d #[]
        let mc := modOf c
        unless us.contains mc do users := users.insert d (us.push mc)
      unless seen.contains d do todo := todo.push d
  logInfo (s!"REC|closure of {roots.toList}: {seen.size} constants; " ++
    s!"class-inductive recursor constants: {users.size}")
  for (d, us) in users.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    let ind := d.getPrefix
    let us := us.qsort (· < ·)
    let cross := us.any (· != modOf ind)
    let shown := String.intercalate ", " (us.toList.take 12)
    let more := if us.size > 12 then s!", … ({us.size} modules in total)" else ""
    logInfo (s!"REC|{d}|class inductive {ind} declared in {modOf ind}|" ++
      s!"used across a module boundary: {cross}|used from {us.size} modules: {shown}{more}")

#hypothesis_surface Mitaka.Key.headline_mitaka512 Mitaka.Key.headline_mitaka1024
#class_recursors Mitaka.Key.headline_mitaka512 Mitaka.Key.headline_mitaka1024
-- Theorems of `Mitaka/RealExponent.lean` and `Mitaka/Headline.lean` (counted by the axiom check).
#print axioms Mitaka.RealExponent.measure_lt_of_renyiDiv_le
#print axioms Mitaka.RealExponent.renyiDiv_simulateQ_le_path
#print axioms Mitaka.RealExponent.measure_simulateQ_lt_path
#print axioms Mitaka.evalDist_simulateQ_singleton_eq
#print axioms Mitaka.renyiDiv_game_le
#print axioms Mitaka.Key.renyiDiv_call_le_mitaka512
#print axioms Mitaka.Key.renyiDiv_call_le_mitaka1024
#print axioms Mitaka.Key.headline_of_mitaka512
#print axioms Mitaka.Key.headline_of_mitaka1024
#print axioms Mitaka.headline_arith_mitaka512
#print axioms Mitaka.headline_arith_mitaka1024
#print axioms Mitaka.headline_arith_tableRate_mitaka512
#print axioms Mitaka.headline_arith_tableRate_mitaka1024
#print axioms Mitaka.Key.headline_mitaka512
#print axioms Mitaka.Key.headline_mitaka1024
#print axioms Mitaka.Key.headline_tableRate_mitaka512
#print axioms Mitaka.Key.headline_tableRate_mitaka1024
#print axioms Mitaka.headlineWorlds_exist


#print axioms FalconPrecision.Lemma4.renyiDiv_shift_le
#print axioms FalconPrecision.NumTail.falcon_tail
#print axioms FalconPrecision.RenyiHybrid.renyiMGF_simulateQ_le
#print axioms FalconPrecision.RenyiPath.renyiMGF_simulateQ_le_path
#print axioms FalconPrecision.RenyiPath.lemma15
#print axioms FalconPrecision.RenyiPath.PathSum.bind
#print axioms Mitaka.Lemma5.two_mul_stdDev_sq
#print axioms Mitaka.Lemma5.stdDev_sq
#print axioms Mitaka.Lemma5.pos_of_pos_stdDev
#print axioms Mitaka.Lemma5.stdDev_pos
#print axioms Mitaka.Lemma5.stdDev_sq_le_two
#print axioms Mitaka.Lemma5.discreteGaussianWeight_stdDev
#print axioms Mitaka.Lemma5.stdDev_mitaka512
#print axioms Mitaka.Lemma5.stdDev_mitaka1024
#print axioms Mitaka.Lemma5.renyiDiv_shift_le
#print axioms Mitaka.Lemma5.explicit_exponent_le_of_sq_le
#print axioms Mitaka.Lemma5.explicit_exponent_le_paper
#print axioms Mitaka.Lemma5.explicit_exponent_le_paper_of_sq_le
#print axioms Mitaka.Lemma5.renyiDiv_le_of_abs_sub_le
#print axioms Mitaka.Lemma5.renyiDiv_le_of_abs_sub_le_mitaka512
#print axioms Mitaka.Lemma5.renyiDiv_le_of_abs_sub_le_mitaka1024
#print axioms Mitaka.RenyiTriangle.renyiMGF_le_rpow_mul_rpow
#print axioms Mitaka.RenyiTriangle.renyiDiv_le_rpow_mul_renyiDiv
#print axioms Mitaka.RenyiTriangle.renyiDiv_le_rpow_mul_renyiDiv_two_mul
#print axioms Mitaka.BoundedRatio.renyiDiv_tilted_le
#print axioms Mitaka.BoundedRatio.renyiDiv_withDensity_le
#print axioms Mitaka.basisApply_centre
#print axioms Mitaka.pathSum_sampleCoords
#print axioms Mitaka.isProbabilityMeasure_evalDist_sample
#print axioms Mitaka.renyiDiv_sampleCoords_le
#print axioms Mitaka.renyiDiv_sample_le
#print axioms Mitaka.renyiDiv_sample_le_of_renyiDiv_le
#print axioms Mitaka.evalDist_gaussian
#print axioms Mitaka.evalDist_world
#print axioms Mitaka.worlds_exist
#print axioms Mitaka.Params.mitaka512_r_pos
#print axioms Mitaka.Params.mitaka512_L_pos
#print axioms Mitaka.Params.mitaka1024_r_pos
#print axioms Mitaka.Params.mitaka1024_L_pos
#print axioms Mitaka.renyiDiv_sample_le_mitaka512
#print axioms Mitaka.renyiDiv_sample_le_mitaka1024
#print axioms Mitaka.renyiDiv_sample_world_mitaka512
#print axioms Mitaka.renyiDiv_sample_world_mitaka1024
#print axioms Mitaka.ofCoeffs_zero
#print axioms Mitaka.ofCoeffs_add
#print axioms Mitaka.ofCoeffs_sub
#print axioms Mitaka.ofCoeffs_neg
#print axioms Mitaka.ofCoeffs_fun_add
#print axioms Mitaka.ofCoeffs_fun_neg
#print axioms Mitaka.ofCoeffs_fun_div
#print axioms Mitaka.ofCoeffs_negacyclicConvCoeff
#print axioms Mitaka.ofCoeffs_injective
#print axioms Mitaka.root_pow
#print axioms Mitaka.isPrimitiveRoot_root
#print axioms Mitaka.emb_mkQ
#print axioms Mitaka.emb_ofCoeffs
#print axioms Mitaka.emb_algebraMap
#print axioms Mitaka.eval₂_negacyclicModulus
#print axioms Mitaka.neg_pow_pred_pow_add_one
#print axioms Mitaka.eval₂_neg_xK_pow
#print axioms Mitaka.xK_pow
#print axioms Mitaka.emb_xK
#print axioms Mitaka.conjK_xK
#print axioms Mitaka.xK_mul_conjK_xK
#print axioms Mitaka.conjK_conjK
#print axioms Mitaka.emb_conjK
#print axioms Mitaka.embM_adjM
#print axioms Mitaka.embM_apply
#print axioms Mitaka.emb_smul
#print axioms Mitaka.embM_smul_one
#print axioms Mitaka.adjM_add
#print axioms Mitaka.adjM_sub
#print axioms Mitaka.adjM_mul
#print axioms Mitaka.adjM_adjM
#print axioms Mitaka.adjM_one
#print axioms Mitaka.adjM_smul_one
#print axioms Mitaka.sum_abs_cos_le
#print axioms Mitaka.sum_abs_cos_root_le
#print axioms Mitaka.norm_sum_mul_root_pow_le
#print axioms Mitaka.norm_emb_ofCoeffs_le
#print axioms Mitaka.sum_norm_sq_emb_ofCoeffs
#print axioms Mitaka.normSq_lagrange
#print axioms Mitaka.CMat.vecNormSq_nonneg
#print axioms Mitaka.CMat.vecNormSq_smul
#print axioms Mitaka.CMat.vecNormSq_perp
#print axioms Mitaka.CMat.norm_sq_eq_vecNormSq
#print axioms Mitaka.CMat.norm_toEuclideanLin_sq
#print axioms Mitaka.CMat.frob_nonneg
#print axioms Mitaka.CMat.frob_sq
#print axioms Mitaka.CMat.vecNormSq_add_perp
#print axioms Mitaka.CMat.normSq_det_mul_le
#print axioms Mitaka.CMat.vecNormSq_mulVec_le_of_frob
#print axioms Mitaka.CMat.normSq_det_mul_le_of_frob
#print axioms Mitaka.CMat.sigmaMax_nonneg
#print axioms Mitaka.CMat.sigmaMax_le_of
#print axioms Mitaka.CMat.vecNormSq_mulVec_le
#print axioms Mitaka.CMat.sigmaMax_conjTranspose
#print axioms Mitaka.CMat.sigmaMax_mul_le
#print axioms Mitaka.CMat.sigmaMax_add_le
#print axioms Mitaka.CMat.sigmaMax_sub_le
#print axioms Mitaka.CMat.sigmaMax_smul_one
#print axioms Mitaka.CMat.sigmaMin_nonneg
#print axioms Mitaka.CMat.le_sigmaMin_of
#print axioms Mitaka.CMat.sigmaMin_sq_mul_le
#print axioms Mitaka.CMat.star_dotProduct_self
#print axioms Mitaka.CMat.star_dotProduct_mul_conjTranspose
#print axioms Mitaka.CMat.lambdaMax_le_of
#print axioms Mitaka.CMat.le_lambdaMax
#print axioms Mitaka.CMat.lambdaMax_le_sigmaMax
#print axioms Mitaka.CMat.lambdaMax_mul_conjTranspose_add_one
#print axioms Mitaka.CMat.sigmaMax_le_of_lower
#print axioms Mitaka.CMat.frob_mul_le
#print axioms Mitaka.CMat.frob_conjTranspose
#print axioms Mitaka.CMat.frob_mul_le'
#print axioms Mitaka.CMat.frob_eq_norm
#print axioms Mitaka.CMat.frob_add_le
#print axioms Mitaka.CMat.frob_sub_le
#print axioms Mitaka.KMat.sigmaMax_le_norm2
#print axioms Mitaka.KMat.norm2_le_of
#print axioms Mitaka.KMat.sigmaMin_le
#print axioms Mitaka.KMat.le_sigmaMin_of
#print axioms Mitaka.KMat.lambdaMax_le_of
#print axioms Mitaka.KMat.le_lambdaMax
#print axioms Mitaka.KMat.normF_nonneg
#print axioms Mitaka.KMat.normF_sq
#print axioms Mitaka.Key.UClose.of_round
#print axioms Mitaka.Key.NTRU.of_negacyclicConvCoeff
#print axioms Mitaka.Key.Annular.of_isPrimitiveRoot
#print axioms Mitaka.Key.bHatInv_mul_bHat
#print axioms Mitaka.Key.bHat_mul_bHatInv
#print axioms Mitaka.beta_pos
#print axioms Mitaka.traceBound_le_two_mul_sq_beta
#print axioms Mitaka.traceBound_mul_sq_beta_le
#print axioms Mitaka.Key.embM_bHat
#print axioms Mitaka.Key.normSq_det_embM_bHat
#print axioms Mitaka.Key.frob_sq_embM_bHat_le
#print axioms Mitaka.Key.norm2_bHat_le
#print axioms Mitaka.Key.div_beta_le_sigmaMin_bHat
#print axioms Mitaka.Key.vecNormSq_conjTranspose_embM_bHat
#print axioms Mitaka.Key.posDef_sigmaP
#print axioms Mitaka.CMat.sigmaMax_lowerOnes
#print axioms Mitaka.Key.AClose.of_round
#print axioms Mitaka.Key.sigmaE_eq
#print axioms Mitaka.Key.norm2_sub_aHatMat_le
#print axioms Mitaka.Key.normF_sub_aHatMat_le
#print axioms Mitaka.Key.norm2_aMat_le
#print axioms Mitaka.Key.norm2_sigmaE_le
#print axioms Mitaka.Key.normF_sigmaE_le
#print axioms Mitaka.Key.one_add_sq_norm2_eq
#print axioms Mitaka.Key.lambdaMax_le
#print axioms Mitaka.Key.one_add_sq_norm2_le
#print axioms Mitaka.witness_hypotheses
#print axioms Mitaka.ofCoeffs_toReal_single
#print axioms Mitaka.toReal_sub
#print axioms Mitaka.toReal_negacyclicConvCoeff
#print axioms Mitaka.CMat.vecNormSq_pos
#print axioms Mitaka.LatticeGaussian.quadForm_pos
#print axioms Mitaka.LatticeGaussian.quadForm_neg
#print axioms Mitaka.LatticeGaussian.summable_exp_neg_sq
#print axioms Mitaka.LatticeGaussian.summable_exp_neg_quadForm
#print axioms Mitaka.LatticeGaussian.tsum_exp_neg_quadForm_eq
#print axioms Mitaka.LatticeGaussian.tsum_exp_neg_quadForm_eq_real
#print axioms Mitaka.LatticeGaussian.sqNorm_nonneg
#print axioms Mitaka.LatticeGaussian.sqNorm_smul
#print axioms Mitaka.LatticeGaussian.quadForm_transpose_mul_self
#print axioms Mitaka.LatticeGaussian.rho_smul_one
#print axioms Mitaka.LatticeGaussian.rho_eq_exp_quadForm
#print axioms Mitaka.LatticeGaussian.rho_congr
#print axioms Mitaka.LatticeGaussian.ofInt_zero
#print axioms Mitaka.LatticeGaussian.sqNorm_pos
#print axioms Mitaka.LatticeGaussian.injective_mulVec_ofInt
#print axioms Mitaka.LatticeGaussian.points_dualBasis
#print axioms Mitaka.LatticeGaussian.summable_rho
#print axioms Mitaka.LatticeGaussian.rhoSum_eq_tsum_points
#print axioms Mitaka.LatticeGaussian.rhoSum_pos
#print axioms Mitaka.LatticeGaussian.gaussianMeasure_singleton
#print axioms Mitaka.LatticeGaussian.isProbabilityMeasure_gaussianMeasure
#print axioms Mitaka.LatticeGaussian.isProbabilityMeasure_gaussian
#print axioms Mitaka.LatticeGaussian.gaussian_singleton
#print axioms Mitaka.LatticeGaussian.gaussian_compl_points
#print axioms Mitaka.LatticeGaussian.hasSum_prod_pi
#print axioms Mitaka.LatticeGaussian.gaussianPMF_one_smul
#print axioms Mitaka.LatticeGaussian.points_inv_mul
#print axioms Mitaka.LatticeGaussian.det_inv_smul_one_ne_zero
#print axioms Mitaka.LatticeGaussian.rho_inv_smul_one
#print axioms Mitaka.LatticeGaussian.rhoSum_inv_smul_one
#print axioms Mitaka.LatticeGaussian.summable_exp_sqNorm
#print axioms Mitaka.LatticeGaussian.det_dualBasis_ne_zero
#print axioms Mitaka.LatticeGaussian.rhoSum_dualBasis_eq_tsum_dual
#print axioms Mitaka.LatticeGaussian.rhoSum_eq_tsum_dual
#print axioms Mitaka.LatticeGaussian.rhoSum_eq_tsum_dual_real
#print axioms Mitaka.LatticeGaussian.rhoSum_le_rhoSum_zero
#print axioms Mitaka.LatticeGaussian.smoothingParam_le_iff
#print axioms Mitaka.LatticeGaussian.smoothingParam_pos
#print axioms Mitaka.LatticeGaussian.smoothingParam_anti
#print axioms Mitaka.LatticeGaussian.geSmoothing_iff
#print axioms Mitaka.LatticeGaussian.geSmoothing_smul_one_iff
#print axioms Mitaka.LatticeGaussian.geSmoothing_of_posSemidef
#print axioms Mitaka.LatticeGaussian.rhoSum_mem_Icc
#print axioms Mitaka.LatticeGaussian.rhoSum_one_mem_Icc
#print axioms Mitaka.LatticeGaussian.rhoSum_dualBasis_one
#print axioms Mitaka.LatticeGaussian.smoothingParam_one_le_iff_tail
#print axioms Mitaka.LatticeGaussian.smoothingParam_one_le
#print axioms Mitaka.LatticeGaussian.gs_ne_zero
#print axioms Mitaka.LatticeGaussian.col_sub_gs_mem_span
#print axioms Mitaka.LatticeGaussian.norm_gs_le_norm_sub
#print axioms Mitaka.LatticeGaussian.tsum_slab_le
#print axioms Mitaka.LatticeGaussian.exists_one_le_abs_dotProduct_gs
#print axioms Mitaka.LatticeGaussian.rhoSum_dualBasis_le_profile
#print axioms Mitaka.LatticeGaussian.smoothingParam_le_profile
#print axioms Mitaka.LatticeGaussian.smoothingParam_le_of_norm_gs_le
#print axioms Mitaka.negacyclicMat_mulVec
#print axioms Mitaka.Key.basisMat_mulVec
#print axioms Mitaka.Key.basisMat_mulVec_ofInt
#print axioms Mitaka.Key.det_basisMat_ne_zero
#print axioms Mitaka.Key.norm_gs_basisMat_le
#print axioms Mitaka.Key.smoothingParam_basisMat_le_profile
#print axioms Mitaka.Key.smoothingParam_basisMat_le
#print axioms Mitaka.splitVec_append
#print axioms Mitaka.append_splitVec
#print axioms Mitaka.splitVec_blocks_mulVec
#print axioms Mitaka.toKVec_add
#print axioms Mitaka.ofCoeffs_smul
#print axioms Mitaka.toKVec_smul
#print axioms Mitaka.toKVec_surjective
#print axioms Mitaka.re_sum_conj_emb_mul_emb
#print axioms Mitaka.embV_mulVec
#print axioms Mitaka.re_sum_star_dotProduct
#print axioms Mitaka.sum_vecNormSq_embV
#print axioms Mitaka.coefMat_mulVec
#print axioms Mitaka.toKVec_sub
#print axioms Mitaka.toKVec_injective
#print axioms Mitaka.Key.bHatMat_mulVec
#print axioms Mitaka.Key.sigmaEMat_mulVec
#print axioms Mitaka.Key.abs_dotProduct_sigmaEMat_le
#print axioms Mitaka.Key.sum_sq_sigmaEMat
#print axioms Mitaka.Key.det_bHatMat_ne_zero
#print axioms Mitaka.Key.sqNorm_inv_bHatMat_mul_le
#print axioms Mitaka.Key.perturbation_eq
#print axioms Mitaka.Key.bHatMat_mulVec_centre
#print axioms Mitaka.Key.latticeGaussian_singleton
#print axioms Mitaka.Key.isProbabilityMeasure_latticeGaussian
#print axioms Mitaka.LatticeGaussian.sqrt_mul_transpose_sqrt
#print axioms Mitaka.LatticeGaussian.smul_mul_transpose_smul
#print axioms Mitaka.LatticeGaussian.rho_eq_of_mul_transpose
#print axioms Mitaka.LatticeGaussian.det_ne_zero_of_mul_transpose
#print axioms Mitaka.LatticeGaussian.inv_smul_of_ne
#print axioms Mitaka.LatticeGaussian.quadForm_smul
#print axioms Mitaka.LatticeGaussian.dotProduct_transpose_mulVec_left
#print axioms Mitaka.LatticeGaussian.tsum_rho_mul_rho_eq
#print axioms Mitaka.LatticeGaussian.sqNorm_sub_smul
#print axioms Mitaka.LatticeGaussian.sqNorm_transpose_mulVec_le
#print axioms Mitaka.LatticeGaussian.transpose_mul_inv_mul
#print axioms Mitaka.LatticeGaussian.posSemidef_convCov_sub
#print axioms Mitaka.LatticeGaussian.posDef_convCov
#print axioms Mitaka.LatticeGaussian.gaussianPMF_nonneg
#print axioms Mitaka.LatticeGaussian.gaussianPMF_pos
#print axioms Mitaka.LatticeGaussian.sqNorm_append
#print axioms Mitaka.LatticeGaussian.gaussianPMF_le_one
#print axioms Mitaka.LatticeGaussian.ofReal_gaussianPMF_one_smul
#print axioms Mitaka.LatticeGaussian.eq_withDensity_of_singleton
#print axioms Mitaka.Key.geSmoothing_convCov
#print axioms Mitaka.Key.sub_sigmaEMat
#print axioms Mitaka.Key.posDef_sub_sigmaEMat
#print axioms Mitaka.cscN_nonneg
#print axioms Mitaka.tauBar_nonneg
#print axioms Mitaka.Key.r_pos_and_L_pos
#print axioms Mitaka.one_le_kappa
#print axioms Mitaka.inv_kappa
#print axioms Mitaka.Key.evalDist_sampleCoords_singleton
#print axioms Mitaka.Key.evalDist_sample_pos_iff
#print axioms Mitaka.Key.isProbabilityMeasure_gaussianQe
#print axioms Mitaka.Key.exists_evalDist_sample_eq_withDensity
#print axioms Mitaka.Key.renyiDiv_sample_gaussianQe_le
#print axioms Mitaka.LatticeGaussian.pathCov_one
#print axioms Mitaka.LatticeGaussian.pathCov_zero
#print axioms Mitaka.LatticeGaussian.posDef_pathCov
#print axioms Mitaka.LatticeGaussian.inv_pathCov
#print axioms Mitaka.LatticeGaussian.posSemidef_pathCov_sub
#print axioms Mitaka.LatticeGaussian.geSmoothing_pathCov
#print axioms Mitaka.LatticeGaussian.renyiDiv_gaussianMeasure_eq
#print axioms Mitaka.LatticeGaussian.detTerm_le
#print axioms Mitaka.LatticeGaussian.exp_logMass_eq
#print axioms Mitaka.LatticeGaussian.exists_deriv2_logMass_le
#print axioms Mitaka.LatticeGaussian.renyiDiv_gaussianMeasure_scale_le
#print axioms Mitaka.Key.renyiDiv_gaussianQe_le
#print axioms Mitaka.Key.renyiDiv_gaussianQe_le_tauBar
#print axioms Mitaka.Key.isProbabilityMeasure_gaussianQ0
#print axioms Mitaka.Key.renyiDiv_sample_gaussianQ0_le
#print axioms Mitaka.Key.renyiDiv_sample_gaussianQ0_le_of_sqrt_log
#print axioms Mitaka.Key.renyiDiv_sample_fp_gaussianQ0_le
#print axioms Mitaka.witness_theorem1
#print axioms Mitaka.Key.renyiDiv_sample_gaussianQ0_le_witness
#print axioms Mitaka.Algorithm4.run_euclid
#print axioms Mitaka.Algorithm4.run_invariant
#print axioms Mitaka.Algorithm4.run_R₀
#print axioms Mitaka.Algorithm4.run_dividends
#print axioms Mitaka.Algorithm4.run_k
#print axioms Mitaka.Algorithm4.run_R
#print axioms Mitaka.Algorithm4.run_R_mem
#print axioms Mitaka.Algorithm4.run_R_complement_mem
#print axioms Mitaka.Algorithm4.run_fp
#print axioms Mitaka.Algorithm4.q64Round_sub_cases
#print axioms Mitaka.Algorithm4.abs_q64Round_sub_le
#print axioms Mitaka.Algorithm4.abs_q64Round_sub_eq_iff
#print axioms Mitaka.Algorithm4.run_inWords
#print axioms Mitaka.Algorithm4.run_inWords_of_table4
#print axioms Mitaka.Algorithm4.algorithm4_correct
#print axioms Mitaka.Algorithm4.table4Input_witness
#print axioms Mitaka.Algorithm4.runBV_noOverflow
#print axioms Mitaka.Algorithm4.runBV_refines
#print axioms Mitaka.Algorithm4.runBV_fp
#print axioms Mitaka.Algorithm4.runBV_correct_of_table4
#print axioms Mitaka.Algorithm4.run_examples
#print axioms Mitaka.Algorithm4.runBV_examples
#print axioms Mitaka.renyiDiv_sample_q64Round_le
#print axioms Mitaka.renyiDiv_sample_world_q64Round_mitaka512
#print axioms Mitaka.renyiDiv_sample_world_q64Round_mitaka1024
#print axioms Mitaka.Key.renyiDiv_sample_q64Round_gaussianQ0_le
#print axioms Mitaka.eps1024_eq
#print axioms Mitaka.cscN_512_le
#print axioms Mitaka.cscN_1024_le
#print axioms Mitaka.beta_lt_mitaka512
#print axioms Mitaka.beta_lt_mitaka1024
#print axioms Mitaka.tauBar_le_mitaka512
#print axioms Mitaka.tauBar_le_mitaka1024
#print axioms Mitaka.sqrt_log_le_r_mitaka512
#print axioms Mitaka.sqrt_log_le_r_mitaka1024
#print axioms Mitaka.cond3L_mitaka512
#print axioms Mitaka.cond3L_mitaka1024
#print axioms Mitaka.cond4a_mitaka512
#print axioms Mitaka.cond4a_mitaka1024
#print axioms Mitaka.cond4_mitaka512
#print axioms Mitaka.cond4_mitaka1024
#print axioms Mitaka.renyiBound_le_mitaka512
#print axioms Mitaka.renyiBound_le_mitaka1024
#print axioms Mitaka.fpTerm_le_mitaka512
#print axioms Mitaka.fpTerm_le_mitaka1024
#print axioms Mitaka.holderFpTerm_le_mitaka512
#print axioms Mitaka.holderFpTerm_le_mitaka1024
#print axioms Mitaka.Key.renyiDiv_sample_gaussianQ0_le_mitaka512
#print axioms Mitaka.Key.renyiDiv_sample_gaussianQ0_le_mitaka1024
#print axioms Mitaka.Key.renyiDiv_sample_q64Round_gaussianQ0_le_mitaka512
#print axioms Mitaka.Key.renyiDiv_sample_q64Round_gaussianQ0_le_mitaka1024
