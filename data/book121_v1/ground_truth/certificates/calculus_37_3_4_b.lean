import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.calculus_37_3_4_b_certificate :
∃ y : ℝ × ℝ, ∀ x : ℝ × ℝ, (fun z : ℝ × ℝ => ((8 : ℝ)*z.1+(12 : ℝ)*z.2, (6 : ℝ)*z.1+(9 : ℝ)*z.2)) x ≠ y := by
  refine ⟨(0,1), ?_⟩
  intro x h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  dsimp at *
  linarith

#print axioms GroundTruth.calculus_37_3_4_b_certificate
