import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.linear_algebra_8D_8_certificate :
¬ (
∀ (F : Type) [RCLike F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V],
  ∀ S T : V →ₗ[F] V, LinearMap.trace F V (S.comp T) = LinearMap.trace F V S * LinearMap.trace F V T
) := by
  classical
  intro h
  have heq := h ℝ (Fin 2 → ℝ) (LinearMap.id : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) LinearMap.id
  norm_num [LinearMap.trace_id] at heq

#print axioms GroundTruth.linear_algebra_8D_8_certificate
