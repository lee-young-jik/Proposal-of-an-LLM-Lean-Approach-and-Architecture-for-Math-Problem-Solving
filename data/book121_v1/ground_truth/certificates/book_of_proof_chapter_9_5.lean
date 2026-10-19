import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_chapter_9_5_certificate :
∃ (α : Type) (β : Type) (A : Set α) (C : Set α) (B : Set β) (D : Set β), A ×ˢ B ∪ C ×ˢ D ≠ (A ∪ C) ×ˢ (B ∪ D) := by
  refine ⟨Fin 2, Fin 2, {0}, {1}, {0}, {1}, ?_⟩
  intro h
  have hh := congrArg (fun S : Set (Fin 2 × Fin 2) => ((0 : Fin 2), (1 : Fin 2)) ∈ S) h
  norm_num at hh

#print axioms GroundTruth.book_of_proof_chapter_9_5_certificate
