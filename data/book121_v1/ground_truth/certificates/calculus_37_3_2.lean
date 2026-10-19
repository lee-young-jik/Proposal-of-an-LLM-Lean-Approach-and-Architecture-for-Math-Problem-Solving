import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.calculus_37_3_2_certificate :
∃ x y : ℝ × ℝ, x ≠ y ∧ (fun z : ℝ × ℝ => (z.1^2-z.2^2, 2*z.1*z.2)) x = (fun z : ℝ × ℝ => (z.1^2-z.2^2, 2*z.1*z.2)) y := by
  refine ⟨(0,1), (0,-1), ?_, ?_⟩ <;> norm_num

#print axioms GroundTruth.calculus_37_3_2_certificate
