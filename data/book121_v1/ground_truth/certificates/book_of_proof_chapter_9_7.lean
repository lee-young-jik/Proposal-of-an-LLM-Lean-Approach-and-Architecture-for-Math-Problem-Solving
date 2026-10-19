import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_chapter_9_7_certificate :
∃ (α : Type) (β : Type) (A : Set α) (B : Set α) (C : Set β), A ×ˢ C = B ×ˢ C ∧ A ≠ B := by
  refine ⟨Fin 1, Fin 1, Set.univ, ∅, ∅, ?_, ?_⟩ <;> simp

#print axioms GroundTruth.book_of_proof_chapter_9_7_certificate
