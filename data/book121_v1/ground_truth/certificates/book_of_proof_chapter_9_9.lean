import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_chapter_9_9_certificate :
∃ (α : Type) (A : Set α) (B : Set α), ¬𝒫 A \ 𝒫 B ⊆ 𝒫 (A \ B) := by
  refine ⟨Fin 2, Set.univ, {0}, ?_⟩
  intro h
  have hm : (Set.univ : Set (Fin 2)) ∈ Set.powerset Set.univ \ Set.powerset {0} := by
    constructor
    · intro x hx
      exact hx
    · intro hs
      have hh := hs (Set.mem_univ (1 : Fin 2))
      norm_num at hh
  have hh := h hm (Set.mem_univ (0 : Fin 2))
  exact hh.2 (by simp)

#print axioms GroundTruth.book_of_proof_chapter_9_9_certificate
