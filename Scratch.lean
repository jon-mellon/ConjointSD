import ConjointSD

-- Scratchpad to inspect SD-consistency assumptions.

#print ConjointSD.EvalAttrIID
#print ConjointSD.EvalAttrLawEqPop
#print ConjointSD.SplitEvalAssumptions
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
#print ConjointSD.plugInMomentAssumptions_of_theta_tendsto
#print ConjointSD.plugInMomentAssumptions_blocks_of_theta_tendsto
#print ConjointSD.paper_ols_gramInv_tendsto_of_design_ae
#print ConjointSD.paper_ols_theta0_eq_of_normal_eq
#print ConjointSD.paper_ols_normal_eq_of_wellSpecified
#print ConjointSD.theta_tendsto_of_paper_ols_design_ae
#print ConjointSD.ConjointIdRandomized
#print ConjointSD.ConjointRandomizationStream
#print ConjointSD.DesignAttrIID.of_randomization_stream
#print ConjointSD.subject_lln_gPop_of_iid
#print ConjointSD.subjectSamplingLLN_of_iid_of_lln_gStar
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

-- Identification.
#print ConjointSD.condMean_eq_potMean_of_rand
#print ConjointSD.ae_restrict_consistency
#print ConjointSD.identified_potMean_from_condMean
#print ConjointSD.identified_amce_from_condMeans

-- Target equivalence and approximation bounds.
#print ConjointSD.attrMean_congr_ae
#print ConjointSD.attrM2_congr_ae
#print ConjointSD.attrVar_congr_ae
#print ConjointSD.attrSD_congr_ae
#print ConjointSD.attrMean_diff_le_of_L2Approx
#print ConjointSD.attrMean_abs_le_of_bounded_ae
#print ConjointSD.attrMean_diff_le_of_approx_ae
#print ConjointSD.attrM2_diff_le_of_approx_ae
#print ConjointSD.attrVar_diff_le_of_approx_ae
#print ConjointSD.attrSD_diff_le_of_approx_ae

-- Model bridge.
#print ConjointSD.gLin_eq_gTotal_blocks
#print ConjointSD.approxWellSpecified_of_approxNoInteractions_of_fullMainEffects

-- Paper core estimands.

-- Paper-facing wrappers.
#print ConjointSD.paper_identifies_potMean_from_condMean
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
#print ConjointSD.status_event_pos
#print ConjointSD.status_id_randomized
#print ConjointSD.wellSpecified_of_noInteractions_of_fullMainEffects
