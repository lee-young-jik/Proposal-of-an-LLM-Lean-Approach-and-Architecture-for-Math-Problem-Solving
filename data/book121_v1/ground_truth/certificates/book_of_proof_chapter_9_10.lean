import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_chapter_9_10_certificate :
∀ (α : Type) (A B : Set α), A ∩ B = ∅ →
  Set.powerset A \ Set.powerset B ⊆ Set.powerset (A \ B) := by
  intro α A B hAB S hS x hx
  constructor
  · exact hS.1 hx
  · intro hxB
    have hab : x ∈ A ∩ B := ⟨hS.1 hx, hxB⟩
    rw [hAB] at hab
    exact hab

#print axioms GroundTruth.book_of_proof_chapter_9_10_certificate
