import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_section_14_3_6_certificate :
∃ (α : Type) (A : Set α), A.Infinite ∧ ∀ (B : Set α), A ⊆ B → B.Countable → B.Finite := by
  classical
  refine ⟨ℝ, Set.univ, Set.infinite_univ, ?_⟩
  intro B hAB hBc
  have hB : B = Set.univ := Set.eq_univ_of_univ_subset hAB
  subst B
  exact (not_countable (Set.countable_univ_iff.mp hBc)).elim

#print axioms GroundTruth.book_of_proof_section_14_3_6_certificate
