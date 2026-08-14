import Mathlib.Util.AssertNoSorry
import stoch_to_det.NVarAllDeletion

/-! Kernel audit for the arbitrary-deletion natural-latent theorem. -/

#check stoch_to_det.card_deletionSet
#check stoch_to_det.NLatent.replicaDefect_le_deletionSumScore_of_optimal
#check stoch_to_det.exists_hardCode_deletionSumScore_le
#check stoch_to_det.deletionMaxConstant_eq_choose
#check stoch_to_det.deletionMaxT_le_alphabetFree
#check stoch_to_det.deletionMaxT_le_alphabetFree_for_range

assert_no_sorry stoch_to_det.card_deletionSet
assert_no_sorry stoch_to_det.NLatent.replicaDefect_le_deletionSumScore_of_optimal
assert_no_sorry stoch_to_det.exists_hardCode_deletionSumScore_le
assert_no_sorry stoch_to_det.deletionMaxConstant_eq_choose
assert_no_sorry stoch_to_det.deletionMaxT_le_alphabetFree
assert_no_sorry stoch_to_det.deletionMaxT_le_alphabetFree_for_range

/--
info: 'stoch_to_det.deletionMaxT_le_alphabetFree_for_range' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stoch_to_det.deletionMaxT_le_alphabetFree_for_range
