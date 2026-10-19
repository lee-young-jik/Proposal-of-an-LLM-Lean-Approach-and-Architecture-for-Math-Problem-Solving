import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_section_12_6_13_certificate :
∀ (α β : Type) (f : α → β) (X : Set α), Set.image f (Set.preimage f (Set.image f X)) = Set.image f X := by
  intro α β f X
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, ⟨x, hx, rfl⟩, rfl⟩

#print axioms GroundTruth.book_of_proof_section_12_6_13_certificate
