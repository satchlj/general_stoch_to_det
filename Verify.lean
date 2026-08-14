import Mathlib.Util.AssertNoSorry
import stoch_to_det.MainTheorems

/-!
This file is a compact index of the public results and a kernel-level audit of
their transitive dependencies.
-/

#check stoch_to_det.general_stoch_to_det
#check stoch_to_det.general_stoch_to_det_three
#check stoch_to_det.general_stoch_to_det_all_deletions
#check stoch_to_det.NVarAlphabetFree.nT_le_alphabetFree
#check stoch_to_det.T_le_270

assert_no_sorry stoch_to_det.general_stoch_to_det
assert_no_sorry stoch_to_det.general_stoch_to_det_three
assert_no_sorry stoch_to_det.general_stoch_to_det_all_deletions
assert_no_sorry stoch_to_det.NVarAlphabetFree.nT_le_alphabetFree
assert_no_sorry stoch_to_det.T_le_270

/--
info: 'stoch_to_det.general_stoch_to_det_all_deletions' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stoch_to_det.general_stoch_to_det_all_deletions

/--
info: 'stoch_to_det.general_stoch_to_det' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stoch_to_det.general_stoch_to_det

/--
info: 'stoch_to_det.general_stoch_to_det_three' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stoch_to_det.general_stoch_to_det_three

/--
info: 'stoch_to_det.NVarAlphabetFree.nT_le_alphabetFree' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stoch_to_det.NVarAlphabetFree.nT_le_alphabetFree

/--
info: 'stoch_to_det.T_le_270' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stoch_to_det.T_le_270
