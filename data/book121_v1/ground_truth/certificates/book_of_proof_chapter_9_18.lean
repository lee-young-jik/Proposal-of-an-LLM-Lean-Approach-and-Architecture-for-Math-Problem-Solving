import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_chapter_9_18_certificate :
∀ a b c : ℕ, 1 ≤ a → 1 ≤ b → 1 ≤ c →
  Even ((a : ℤ) - (b : ℤ)) ∨ Even ((a : ℤ) + (c : ℤ)) ∨ Even ((b : ℤ) - (c : ℤ)) := by
  intro a b c ha hb hc
  simp only [Int.even_iff]
  omega

#print axioms GroundTruth.book_of_proof_chapter_9_18_certificate
