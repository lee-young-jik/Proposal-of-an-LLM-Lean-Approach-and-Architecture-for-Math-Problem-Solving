import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.calculus_37_3_1_a_certificate :
Function.Injective (fun z : ℝ × ℝ => ((3 : ℝ)*z.1+(-4 : ℝ)*z.2, (1 : ℝ)*z.1+(5 : ℝ)*z.2)) := by
  intro x y h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  apply Prod.ext <;> dsimp at * <;> linarith

#print axioms GroundTruth.calculus_37_3_1_a_certificate
