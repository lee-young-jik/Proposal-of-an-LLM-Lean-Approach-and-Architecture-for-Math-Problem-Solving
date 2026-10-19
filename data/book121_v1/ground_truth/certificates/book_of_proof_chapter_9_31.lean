import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_chapter_9_31_certificate :
∃ (m : ℕ), m ≠ (1 : ℕ) ∧ ∃ (S : Finset (ℕ × ℕ)), (∀ p ∈ S, p.2 ≤ p.1 ∧ p.1.choose p.2 = m) ∧ (4 : ℕ) < S.card := by
  refine ⟨3003, ?_, {(14,6),(14,8),(15,5),(15,10),(78,2),(78,76)}, ?_, ?_⟩
  · norm_num
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with h|h|h|h|h|h <;> subst p <;> decide
  · norm_num

#print axioms GroundTruth.book_of_proof_chapter_9_31_certificate
