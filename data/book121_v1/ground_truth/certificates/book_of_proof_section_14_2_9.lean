import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_section_14_2_9_certificate :
(Set.univ : Set (({x : ℕ | x = 0 ∨ x = 1} × ℕ+))).Countable ∧ (Set.univ : Set (({x : ℕ | x = 0 ∨ x = 1} × ℕ+))).Infinite := by
  classical
  letI : Nonempty {x : ℕ | x = 0 ∨ x = 1} := ⟨⟨0, Or.inl rfl⟩⟩
  constructor
  · exact Set.countable_univ
  · exact Set.infinite_univ

#print axioms GroundTruth.book_of_proof_section_14_2_9_certificate
