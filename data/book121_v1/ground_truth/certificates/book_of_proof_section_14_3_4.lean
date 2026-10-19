import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_section_14_3_4_certificate :
∀ (α : Type) (A B C : Set α), A ⊆ B → B ⊆ C →
  A.Countable → A.Infinite → C.Countable → C.Infinite → B.Countable ∧ B.Infinite := by
  intro α A B C hAB hBC hAc hAi hCc hCi
  constructor
  · exact hCc.mono hBC
  · exact hAi.mono hAB

#print axioms GroundTruth.book_of_proof_section_14_3_4_certificate
