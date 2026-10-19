import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_chapter_9_20_certificate :
∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ (p : ℤ) - (q : ℤ) = 1000 := by
  refine ⟨1013, 13, ?_, ?_, ?_⟩ <;> norm_num

#print axioms GroundTruth.book_of_proof_chapter_9_20_certificate
