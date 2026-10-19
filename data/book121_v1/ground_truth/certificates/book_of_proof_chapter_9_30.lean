import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_chapter_9_30_certificate :
∀ (a b : ℤ), (42 : ℤ) * a + (7 : ℤ) * b ≠ (1 : ℤ) := by
  intro a b h
  omega

#print axioms GroundTruth.book_of_proof_chapter_9_30_certificate
