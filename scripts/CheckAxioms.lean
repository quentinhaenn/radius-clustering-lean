import RadiusClustering

/-! Axioms of the key theorems; run through `scripts/check_axioms.sh`. -/

open RadiusClustering

#print axioms exists_validClustering_iff_exists_dominating
#print axioms minClusters_iff_minDominating
#print axioms exists_isCentreSet
#print axioms exists_isDerivedFrom
#print axioms isDerivedFrom_minDominating
#print axioms thresholdGraph_graphDissim
#print axioms isDissimilarity_graphDissim
#print axioms exists_dominating_iff_exists_validClustering_graphDissim
#print axioms isCentreSet_minClustering_graphDissim
#print axioms exists_surjective_validClustering_iff
#print axioms not_surjective_of_card_lt
#print axioms exists_surjective_validClustering_iff_exists_dominating
#print axioms IsDominating.thresholdGraph_mono
#print axioms isMinRadius_of_lastDominable
#print axioms isDerivedFrom_lastDominable
#print axioms exists_validClustering_one_iff
#print axioms fig34_isDissimilarity
#print axioms fig34_minRadius
#print axioms isValidClustering_comp_strictMono
#print axioms thresholdGraph_comp_strictMono
#print axioms exists_nat_copy
