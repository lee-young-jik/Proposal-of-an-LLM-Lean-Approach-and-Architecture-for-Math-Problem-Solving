import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_chapter_9_27_certificate :
∀ (S : Finset ℝ), S.card = (3 : ℕ) → ∃ (x : ℝ), x ∈ S ∧ x ^ (2 : ℕ) ≠ (2 : ℝ) * x ∨ x ∉ S ∧ x ^ (2 : ℕ) = (2 : ℝ) * x := by
  classical
  intro S hcard
  by_cases hbad : ∃ x : ℝ, x ∈ S ∧ x ^ 2 ≠ 2 * x
  · rcases hbad with ⟨x, hxS, hx⟩
    exact ⟨x, Or.inl ⟨hxS, hx⟩⟩
  · exfalso
    push_neg at hbad
    have hsub : S ⊆ ({0, 2} : Finset ℝ) := by
      intro x hxS
      have heq := hbad x hxS
      have hfactor : x * (x - 2) = 0 := by
        nlinarith [heq]
      rcases mul_eq_zero.mp hfactor with hx0 | hx2
      · simp [hx0]
      · have hx : x = 2 := by nlinarith
        simp [hx]
    have hc := Finset.card_le_card hsub
    rw [hcard] at hc
    norm_num at hc

#print axioms GroundTruth.book_of_proof_chapter_9_27_certificate
