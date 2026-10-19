import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_chapter_9_16_certificate :
∃ (α : Type) (A : Finset α) (B : Finset α), (A ∪ B).card ≠ A.card + B.card := by
  refine ⟨Fin 1, {0}, {0}, ?_⟩
  norm_num

#print axioms GroundTruth.book_of_proof_chapter_9_16_certificate
