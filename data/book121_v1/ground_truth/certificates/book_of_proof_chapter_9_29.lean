import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_chapter_9_29_certificate :
∃ (x : ℝ) (y : ℝ), |x + y| = |x - y| ∧ y ≠ (0 : ℝ) := by
  refine ⟨0, 1, ?_, ?_⟩ <;> norm_num

#print axioms GroundTruth.book_of_proof_chapter_9_29_certificate
