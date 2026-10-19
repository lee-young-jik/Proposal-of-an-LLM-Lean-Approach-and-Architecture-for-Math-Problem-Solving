import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_section_14_3_5_certificate :
¬ (Set.univ : Set ({x : ℕ | x = 0 ∨ x = 1} × ℝ)).Countable := by
  classical
  intro h
  have himg :
      ((fun p : {x : ℕ | x = 0 ∨ x = 1} × ℝ => p.2) '' Set.univ).Countable :=
    h.image (fun p => p.2)
  have heq :
      (fun p : {x : ℕ | x = 0 ∨ x = 1} × ℝ => p.2) '' Set.univ =
        (Set.univ : Set ℝ) := by
    ext x
    constructor
    · intro hx
      trivial
    · intro hx
      exact ⟨(⟨0, by simp⟩, x), by simp⟩
  have hu : (Set.univ : Set ℝ).Countable := by
    rw [← heq]
    exact himg
  have hr : Countable ℝ := Set.countable_univ_iff.mp hu
  exact not_countable hr

#print axioms GroundTruth.book_of_proof_section_14_3_5_certificate
