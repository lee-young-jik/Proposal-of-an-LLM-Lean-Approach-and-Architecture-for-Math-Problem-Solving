import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.calculus_37_3_3_b_certificate :
Function.Surjective (fun z : ℝ × ℝ => ((4 : ℝ)*z.1+(13 : ℝ)*z.2, (2 : ℝ)*z.1+(7 : ℝ)*z.2)) := by
  intro y
  refine ⟨((7*y.1-13*y.2)/2, (-2*y.1+4*y.2)/2), ?_⟩
  apply Prod.ext <;> dsimp <;> ring

#print axioms GroundTruth.calculus_37_3_3_b_certificate
