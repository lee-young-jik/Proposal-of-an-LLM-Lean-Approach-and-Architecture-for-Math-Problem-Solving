import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_chapter_9_34_certificate :
∃ (α : Type) (X : Set α) (A : Set α) (B : Set α), X ⊆ A ∪ B ∧ ¬X ⊆ A ∧ ¬X ⊆ B := by
  refine ⟨Fin 2, Set.univ, {0}, {1}, ?_, ?_, ?_⟩
  · intro x hx
    fin_cases x <;> simp
  · intro h
    have hh := h (Set.mem_univ (1 : Fin 2))
    norm_num at hh
  · intro h
    have hh := h (Set.mem_univ (0 : Fin 2))
    norm_num at hh

#print axioms GroundTruth.book_of_proof_chapter_9_34_certificate
