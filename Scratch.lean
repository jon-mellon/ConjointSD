import ConjointSD

-- Scratchpad to inspect SD-consistency assumptions.

#print ConjointSD.EvalAttrIID
#print ConjointSD.EvalAttrLawEqPop
#print ConjointSD.SplitEvalAssumptionsBounded
#print ConjointSD.attrMean_tendsto_of_theta_tendsto
#print ConjointSD.attrM2_tendsto_of_theta_tendsto
#print ConjointSD.attrSD_tendsto_of_mean_m2_tendsto
#print ConjointSD.olsThetaHat_tendsto_of_attr_moments
#print ConjointSD.cont_mean_gLin_of_bounded
#print ConjointSD.cont_m2_gLin_of_bounded
#print ConjointSD.cont_mean_gBlockTerm_of_bounded
#print ConjointSD.cont_m2_gBlockTerm_of_bounded
#print ConjointSD.cont_mean_blocks_gBlockTerm_of_bounded
#print ConjointSD.cont_m2_blocks_gBlockTerm_of_bounded
#print ConjointSD.paper_ols_gramInv_tendsto_of_design_ae
#print ConjointSD.paper_ols_theta0_eq_of_normal_eq
#print ConjointSD.paper_ols_normal_eq_of_wellSpecified
#print ConjointSD.theta_tendsto_of_paper_ols_design_ae
#print ConjointSD.ConjointRandomizationStream
#print ConjointSD.subject_lln_gPop_of_iid
-- Core SD and decomposition.
#print ConjointSD.meanHatZ_tendsto_ae_of_score
#print ConjointSD.sdHatZ_tendsto_ae_of_score

-- Sample splitting (evaluation stage).
#print ConjointSD.sdHat_fixed_m_tendsto_ae_attrSD

-- Sequential consistency (train then eval).
#print ConjointSD.totalErr_tendsto_trainErr_fixed_m
#print ConjointSD.trainErr_tendsto_zero
#print ConjointSD.sequential_consistency_ae

-- Decomposition sequential consistency.
#print ConjointSD.sequential_consistency_blocks_ae

-- Target equivalence.
#print ConjointSD.attrMean_congr_ae
#print ConjointSD.attrM2_congr_ae
#print ConjointSD.attrVar_congr_ae
#print ConjointSD.attrSD_congr_ae

-- Model bridge.
#print ConjointSD.gLin_eq_gTotal_blocks

-- Paper core estimands.

-- Paper-facing wrappers.
#print ConjointSD.paper_sd_blocks_sequential_consistency_to_true_target_ae
#print ConjointSD.paper_ols_attr_moments_of_design_ae
#print ConjointSD.paper_sd_blocks_sequential_consistency_to_true_target_ae_of_paper_ols_design_ae_of_NoInteractions_of_randomization




-- Auto-generated DAG coverage: all ConjointSD theorems.
#print ConjointSD.attrVar_tendsto_of_mean_m2_tendsto
#print ConjointSD.designMeanZ_Zcomp_eq_attrMean
#print ConjointSD.gTotal
#print ConjointSD.paper_ols_attr_moments_of_lln_fullrank_ae
#print ConjointSD.paper_ols_lln_of_design_ae
#print ConjointSD.paper_ols_lln_of_score_assumptions_ae
#print ConjointSD.wellSpecified_of_noInteractions_of_fullMainEffects
