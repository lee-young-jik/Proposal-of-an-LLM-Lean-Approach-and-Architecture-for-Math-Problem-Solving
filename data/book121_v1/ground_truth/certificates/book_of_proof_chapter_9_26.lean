import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_chapter_9_26_certificate :
∃ (α : Type) (A : Set α) (B : Set α) (C : Set α), A = B \ C ∧ B ≠ A ∪ C := by
  refine ⟨Fin 1, ∅, ∅, Set.univ, by simp, ?_⟩
  intro h
  have hh := congrArg (fun S : Set (Fin 1) => (0 : Fin 1) ∈ S) h
  simpa using hh

#print axioms GroundTruth.book_of_proof_chapter_9_26_certificate
