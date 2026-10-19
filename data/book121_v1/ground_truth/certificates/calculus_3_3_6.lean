import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.calculus_3_3_6_certificate :
∀ f g h : ℝ → ℝ, (fun x => f (h x)+g (h x)) = (fun x => (f ∘ h) x+(g ∘ h) x) := by
  classical
  first
  | solve | norm_num
  | solve | simp [Function.comp_def]
  | solve | aesop (config := { maxRuleApplications := 30 })

#print axioms GroundTruth.calculus_3_3_6_certificate
