import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.calculus_37_3_4_a_certificate :
∃ x y : ℝ × ℝ, x ≠ y ∧ (fun z : ℝ × ℝ => ((8 : ℝ)*z.1+(12 : ℝ)*z.2, (6 : ℝ)*z.1+(9 : ℝ)*z.2)) x = (fun z : ℝ × ℝ => ((8 : ℝ)*z.1+(12 : ℝ)*z.2, (6 : ℝ)*z.1+(9 : ℝ)*z.2)) y := by
  refine ⟨(0,0), (3,-2), ?_, ?_⟩ <;> norm_num

#print axioms GroundTruth.calculus_37_3_4_a_certificate
