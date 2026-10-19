import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.basic_analysis_2_1_2_1_1_certificate :
∀ M : ℝ, ∃ n : ℕ, 1 ≤ n ∧ M < |3*(n : ℝ)| := by
  intro M
  obtain ⟨n, hn⟩ := exists_nat_gt (max M 1)
  have hM : M < (n : ℝ) := lt_of_le_of_lt (le_max_left M 1) hn
  have h1 : (1 : ℝ) < (n : ℝ) := lt_of_le_of_lt (le_max_right M 1) hn
  refine ⟨n, ?_, ?_⟩
  · exact_mod_cast h1.le
  · rw [abs_of_nonneg (by positivity)]
    nlinarith

#print axioms GroundTruth.basic_analysis_2_1_2_1_1_certificate
