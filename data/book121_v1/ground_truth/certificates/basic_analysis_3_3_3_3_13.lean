import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.basic_analysis_3_3_3_3_13_certificate :
∃ (f : ℝ → ℝ), Continuous f ∧ (∃ (M : ℝ), ∀ (n : ℤ), |f ↑n| ≤ M) ∧ ∀ (M : ℝ), ∃ (x : ℝ), M < |f x| := by
  classical
  let f : ℝ → ℝ := fun x => x * Real.sin (Real.pi * x)
  refine ⟨f, ?_, ⟨0, ?_⟩, ?_⟩
  · fun_prop
  · intro n
    simp [f, mul_comm Real.pi, Real.sin_int_mul_pi]
  · intro M
    obtain ⟨n, hn⟩ := exists_nat_gt (max M 0)
    refine ⟨2 * (n : ℝ) + 1/2, ?_⟩
    have hs : Real.sin (Real.pi * (2 * (n : ℝ) + 1/2)) = 1 := by
      rw [show Real.pi * (2 * (n : ℝ) + 1/2) = Real.pi / 2 + (n : ℝ) * (2 * Real.pi) by ring]
      rw [Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two]
    have hnonneg : 0 ≤ 2 * (n : ℝ) + 1/2 := by positivity
    dsimp [f]
    rw [hs, mul_one, abs_of_nonneg hnonneg]
    have hM : M < (n : ℝ) := (le_max_left M 0).trans_lt hn
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith

#print axioms GroundTruth.basic_analysis_3_3_3_3_13_certificate
