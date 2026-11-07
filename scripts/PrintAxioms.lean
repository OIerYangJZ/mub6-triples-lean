import MUBTriples

/-! Axiom check for the main results.  Run with `lake env lean scripts/PrintAxioms.lean`
after `lake build`.  Expected output for every declaration:
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no project axioms). -/

#print axioms MUBTriples.mubTriple_classification
#print axioms MUBTriples.no_four_mubs
#print axioms MUBTriples.no_four_mubs_of_classification
#print axioms MUBTriples.every_mubTriple_hasOrder3Symmetry
#print axioms MUBTriples.tripleClassification_of_certificate
#print axioms MUBTriples.symmetricRecognition
#print axioms MUBTriples.ΓF_exp_eq_ΓFpaper
#print axioms MUBTriples.ΓF_eq_ΓFpaper
#print axioms MUBTriples.minTransition_iff_paper
#print axioms MUBTriples.ΓF_of_equivalent
#print axioms MUBTriples.ΓF_conjTranspose
#print axioms MUBTriples.Contraction.symmetry_criterion
#print axioms MUBTriples.isolatedTriple_isMUBTriple
#print axioms MUBTriples.familyTriple_isMUBTriple_iff
#print axioms MUBTriples.ΓFpaper_congr
#print axioms MUBTriples.classified_of_paper
-- Seed parametrization (MUBTriples/Seeds.lean)
#print axioms MUBTriples.construct_spec
#print axioms MUBTriples.seedTriple_spec
#print axioms MUBTriples.seedTriple_isFamilyMember
#print axioms MUBTriples.exists_isRootTriple
#print axioms MUBTriples.domainPoly_eq_disc
#print axioms MUBTriples.IsRootTriple.normSq_of_domain
#print axioms MUBTriples.domainPoly_nonpos_iff
#print axioms MUBTriples.inDomain_iff
#print axioms MUBTriples.seedσ_center
#print axioms MUBTriples.exists_familyMember
#print axioms MUBTriples.seedOf_seedTriple_corner
#print axioms MUBTriples.seedOf_corner142
#print axioms MUBTriples.familyMember_tripleEquiv_seedTriple
#print axioms MUBTriples.exists_familyMember_iff_seed
-- Non-equivalence of the isolated triple (MUBTriples/Inequivalence.lean)
#print axioms MUBTriples.bargmann4_of_tripleEquiv
#print axioms MUBTriples.familyTriple_conj_frame
#print axioms MUBTriples.bargmann4_isolatedTriple
#print axioms MUBTriples.not_tripleEquiv_isolatedTriple_of_familyMember
#print axioms MUBTriples.seedOf_isolatedTriple
#print axioms MUBTriples.family_and_isolated_exclusive
#print axioms MUBTriples.tripleClassification_iff_seedClassification
#print axioms MUBTriples.mubTriple_seedClassification
#print axioms MUBTriples.symmetric_seedClassification
