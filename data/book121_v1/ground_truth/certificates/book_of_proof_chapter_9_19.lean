import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_chapter_9_19_certificate :
∀ r s : ℚ, r < s → ∃ u : ℝ, (r : ℝ) < u ∧ u < (s : ℝ) ∧ Irrational u := by
  intro r s hrs
  obtain ⟨u, hu, hru, hus⟩ := exists_irrational_btwn (show (r : ℝ) < (s : ℝ) by exact_mod_cast hrs)
  exact ⟨u, hru, hus, hu⟩

#print axioms GroundTruth.book_of_proof_chapter_9_19_certificate
