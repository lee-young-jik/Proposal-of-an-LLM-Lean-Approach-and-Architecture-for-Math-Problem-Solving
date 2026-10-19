import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.linear_algebra_1C_19_certificate :
¬ (
∀ (F : Type) [RCLike F] (V : Type) [AddCommGroup V] [Module F V],
  ∀ V₁ V₂ U : Submodule F V, V₁ ⊔ U = V₂ ⊔ U → V₁ = V₂
) := by
  push_neg
  refine ⟨ℝ, inferInstance, ℝ, inferInstance, inferInstance, ⊥, ⊤, ⊤, ?_, ?_⟩ <;> simp

#print axioms GroundTruth.linear_algebra_1C_19_certificate
