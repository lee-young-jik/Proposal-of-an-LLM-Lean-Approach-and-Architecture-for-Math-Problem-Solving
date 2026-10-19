import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.basic_analysis_2_1_2_1_15_a_certificate :
∀ M : ℝ, ∃ n : ℕ, 1 ≤ n ∧ M < |(if Odd n then (n : ℝ) else 1/(n : ℝ))| := by
  intro M
  obtain ⟨k, hk⟩ := exists_nat_gt (max M 1)
  have hM : M < (k : ℝ) := lt_of_le_of_lt (le_max_left M 1) hk
  have ho : Odd (2*k+1) := ⟨k, by omega⟩
  refine ⟨2*k+1, by omega, ?_⟩
  simp only [if_pos ho]
  rw [abs_of_nonneg (by positivity)]
  push_cast
  nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]

#print axioms GroundTruth.basic_analysis_2_1_2_1_15_a_certificate
