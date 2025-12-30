import ConjointSD

-- Scratchpad to inspect SD-consistency assumptions.

#print ConjointSD.PopIID
#print ConjointSD.ScoreAssumptions
#print ConjointSD.sd_component_consistent_to_popSDAttr
#print ConjointSD.SplitEvalAssumptions
#print ConjointSD.GEstimationAssumptions
#print ConjointSD.FunctionalContinuityAssumptions
#print ConjointSD.sequential_consistency_ae

-- Proven statements (base layer).
#print ConjointSD.sdHatZ_tendsto_ae
#print ConjointSD.sd_component_consistent
#print ConjointSD.sd_component_consistent_to_popSDAttr
#print ConjointSD.gExp_eq_gPot
#print ConjointSD.popSDAttr_congr_ae
#print ConjointSD.gStar_eq_sum_blocks_of_WellSpecified
#print ConjointSD.sequential_consistency_ae

-- Proven statements (paper-facing wrappers).
#print ConjointSD.paper_identifies_potMean_from_condMean
#print ConjointSD.paper_identifies_amce_from_condMeans
#print ConjointSD.paper_sd_total_sequential_consistency_ae
#print ConjointSD.paper_sd_total_sequential_consistency_to_true_target_ae
#print ConjointSD.paper_total_sd_estimator_consistency_ae_of_gBTerm
#print ConjointSD.paper_sd_total_sequential_consistency_to_gStar_ae_of_gBTerm
