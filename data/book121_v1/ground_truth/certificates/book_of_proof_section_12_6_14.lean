import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_section_12_6_14_certificate :
∀ (α β : Type) (f : α → β) (Y : Set β), Set.preimage f (Set.image f (Set.preimage f Y)) = Set.preimage f Y := by
  intro α β f Y
  exact Set.preimage_image_preimage

#print axioms GroundTruth.book_of_proof_section_12_6_14_certificate
