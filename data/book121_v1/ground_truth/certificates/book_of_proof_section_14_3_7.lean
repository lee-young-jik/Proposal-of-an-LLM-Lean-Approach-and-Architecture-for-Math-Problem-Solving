import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_section_14_3_7_certificate :
∀ (α : Type) (A B : Set α), A ⊆ B → A.Countable → A.Infinite →
  ¬ B.Countable → ¬ (B \ A).Countable := by
  classical
  intro α A B hAB hAcount _ hBuncount hDiffCount
  apply hBuncount
  have hEq : B = A ∪ (B \ A) := by
    ext x
    constructor
    · intro hx
      by_cases hxa : x ∈ A
      · exact Or.inl hxa
      · exact Or.inr ⟨hx, hxa⟩
    · rintro (hx | hx)
      · exact hAB hx
      · exact hx.1
  rw [hEq]
  exact hAcount.union hDiffCount

#print axioms GroundTruth.book_of_proof_section_14_3_7_certificate
