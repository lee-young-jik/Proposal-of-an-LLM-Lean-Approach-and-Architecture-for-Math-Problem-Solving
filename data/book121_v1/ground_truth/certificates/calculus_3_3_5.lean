import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.calculus_3_3_5_certificate :
∃ (f : ℝ → ℝ) (g : ℝ → ℝ) (h : ℝ → ℝ), (fun (x : ℝ) => f (g x + h x)) ≠ fun (x : ℝ) => f (g x) + f (h x) := by
  refine ⟨(fun x : ℝ => x^2), (fun _ => 1), (fun _ => 1), ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num at hh

#print axioms GroundTruth.calculus_3_3_5_certificate
