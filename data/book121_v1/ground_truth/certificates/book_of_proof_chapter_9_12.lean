import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_chapter_9_12_certificate :
∃ (a : ℕ) (b : ℕ) (c : ℕ),
  (1 : ℕ) ≤ a ∧
    (1 : ℕ) ≤ b ∧
      (1 : ℕ) ≤ c ∧
        a * b % (2 : ℕ) = b * c % (2 : ℕ) ∧
          b * c % (2 : ℕ) = a * c % (2 : ℕ) ∧ (a % (2 : ℕ) = b % (2 : ℕ) → b % (2 : ℕ) ≠ c % (2 : ℕ)) := by
  refine ⟨1, 2, 2, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

#print axioms GroundTruth.book_of_proof_chapter_9_12_certificate
