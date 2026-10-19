import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.calculus_37_3_1_b_certificate :
Function.Surjective (fun z : ℝ × ℝ => ((3 : ℝ)*z.1+(-4 : ℝ)*z.2, (1 : ℝ)*z.1+(5 : ℝ)*z.2)) := by
  intro y
  refine ⟨((5*y.1+4*y.2)/19, (-y.1+3*y.2)/19), ?_⟩
  apply Prod.ext <;> dsimp <;> ring

#print axioms GroundTruth.calculus_37_3_1_b_certificate
