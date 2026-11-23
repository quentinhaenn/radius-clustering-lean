import RadiusClustering

/-! Axioms of the key theorems; run through `scripts/check_axioms.sh`. -/

open RadiusClustering

#print axioms exists_validClustering_iff_exists_dominating
#print axioms thresholdGraph_graphDissim
#print axioms graphDissim_eq_zero_iff
#print axioms graphDissim_comm
#print axioms graphDissim_triangle
#print axioms exists_dominating_iff_exists_validClustering_graphDissim
#print axioms exists_surjective_validClustering_iff
#print axioms not_surjective_of_card_lt
#print axioms exists_surjective_validClustering_iff_exists_dominating
