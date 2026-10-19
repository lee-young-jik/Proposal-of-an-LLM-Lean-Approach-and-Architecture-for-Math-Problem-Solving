import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_section_14_2_6_certificate :
∀ (f : ℚ → ℝ), ¬Function.Bijective f := by
  intro f hf
  have hrange : Set.range f = (Set.univ : Set ℝ) := Set.range_eq_univ.mpr hf.2
  have hc : (Set.univ : Set ℝ).Countable := by
    rw [← hrange]
    exact Set.countable_range f
  exact Set.not_countable_univ hc

#print axioms GroundTruth.book_of_proof_section_14_2_6_certificate
