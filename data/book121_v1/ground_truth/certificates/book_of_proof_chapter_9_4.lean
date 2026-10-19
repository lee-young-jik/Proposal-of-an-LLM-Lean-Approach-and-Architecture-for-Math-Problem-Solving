import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_chapter_9_4_certificate :
∃ (n : ℕ), (1 : ℕ) ≤ n ∧ ¬Nat.Prime (n ^ (2 : ℕ) + (17 : ℕ) * n + (17 : ℕ)) := by
  refine ⟨17, ?_, ?_⟩ <;> norm_num

#print axioms GroundTruth.book_of_proof_chapter_9_4_certificate
