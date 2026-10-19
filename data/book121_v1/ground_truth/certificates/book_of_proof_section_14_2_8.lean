import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_section_14_2_8_certificate :
(Set.univ : Set (ℤ × ℚ)).Countable ∧ (Set.univ : Set (ℤ × ℚ)).Infinite := by
  constructor
  · exact Set.countable_univ
  · exact Set.infinite_univ

#print axioms GroundTruth.book_of_proof_section_14_2_8_certificate
