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
