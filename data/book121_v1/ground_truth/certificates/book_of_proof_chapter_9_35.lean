import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_chapter_9_35_certificate :
∃ (n : ℕ), Nat.Prime n ∧ ¬Nat.Prime ((2 : ℕ) ^ n - (1 : ℕ)) := by
  refine ⟨11, ?_, ?_⟩ <;> norm_num

#print axioms GroundTruth.book_of_proof_chapter_9_35_certificate
