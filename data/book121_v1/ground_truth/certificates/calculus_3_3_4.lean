import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.calculus_3_3_4_certificate :
∃ (f : ℝ → ℝ) (g : ℝ → ℝ) (D : Set ℝ) (E : Set ℝ), ∃ x ∈ D, f x ∈ E ∧ x ∈ E ∧ g x ∈ D ∧ g (f x) ≠ f (g x) := by
  refine ⟨(fun x : ℝ => x+1), (fun x : ℝ => x^2), Set.univ, Set.univ, 1, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

#print axioms GroundTruth.calculus_3_3_4_certificate
