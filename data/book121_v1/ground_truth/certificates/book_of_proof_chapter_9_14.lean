import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_chapter_9_14_certificate :
∀ (α : Type) (A B : Set α), Set.powerset A ∩ Set.powerset B = Set.powerset (A ∩ B) := by
  intro α A B
  ext S
  change (S ⊆ A ∧ S ⊆ B) ↔ S ⊆ A ∩ B
  constructor
  · rintro ⟨hA,hB⟩ x hx
    exact ⟨hA hx,hB hx⟩
  · intro h
    exact ⟨fun x hx => (h hx).1, fun x hx => (h hx).2⟩

#print axioms GroundTruth.book_of_proof_chapter_9_14_certificate
