import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_chapter_9_15_certificate :
∀ n : ℤ, Odd n → ∃ a b c : ℤ, Odd a ∧ Odd b ∧ Odd c ∧ n = a+b+c := by
  intro n hn
  refine ⟨n, 1, -1, hn, ?_, ?_, ?_⟩ <;> norm_num

#print axioms GroundTruth.book_of_proof_chapter_9_15_certificate
