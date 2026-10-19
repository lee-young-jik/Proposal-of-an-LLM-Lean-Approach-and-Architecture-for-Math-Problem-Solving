import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_chapter_9_11_certificate :
∃ (a : ℕ) (b : ℕ), (1 : ℕ) ≤ a ∧ (1 : ℕ) ≤ b ∧ a * b ≤ a + b := by
  refine ⟨1, 1, ?_, ?_, ?_⟩ <;> norm_num

#print axioms GroundTruth.book_of_proof_chapter_9_11_certificate
