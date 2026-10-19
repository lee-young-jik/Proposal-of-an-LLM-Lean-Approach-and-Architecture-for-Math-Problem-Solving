import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.linear_algebra_3A_10_certificate :
¬ (
∀ q : Polynomial ℝ, ∃ T : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ, ∀ p, T p = q.comp p
) := by
  intro H
  obtain ⟨T, hT⟩ := H (1 : Polynomial ℝ)
  have h := hT (0 : Polynomial ℝ)
  simpa using h

#print axioms GroundTruth.linear_algebra_3A_10_certificate
