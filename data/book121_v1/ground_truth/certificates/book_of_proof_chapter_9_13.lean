import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_chapter_9_13_certificate :
∃ X : Set (ℝ ⊕ Unit), Set.range (Sum.inl : ℝ → ℝ ⊕ Unit) ⊆ X ∧ Sum.inr () ∈ X := by
  refine ⟨Set.univ, ?_, ?_⟩ <;> simp

#print axioms GroundTruth.book_of_proof_chapter_9_13_certificate
