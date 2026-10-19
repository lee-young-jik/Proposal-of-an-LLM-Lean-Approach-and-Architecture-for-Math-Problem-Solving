import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_chapter_9_25_certificate :
∃ (a : ℤ) (b : ℤ) (c : ℤ), a ∣ b * c ∧ ¬a ∣ b ∧ ¬a ∣ c := by
  refine ⟨6, 2, 3, ?_, ?_, ?_⟩ <;> norm_num

#print axioms GroundTruth.book_of_proof_chapter_9_25_certificate
