import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_chapter_9_6_certificate :
∀ (α β : Type) (A C : Set α) (B D : Set β),
  (A ×ˢ B) ∩ (C ×ˢ D) = (A ∩ C) ×ˢ (B ∩ D) := by
  intro α β A C B D
  ext p
  simp only [Set.mem_prod, Set.mem_inter_iff]
  tauto

#print axioms GroundTruth.book_of_proof_chapter_9_6_certificate
