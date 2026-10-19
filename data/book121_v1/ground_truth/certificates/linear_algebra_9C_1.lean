import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.linear_algebra_9C_1_certificate :
¬ (
∀ (F : Type) [RCLike F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V],
  ∀ S T : V →ₗ[F] V, LinearMap.det (S+T) = LinearMap.det S + LinearMap.det T
) := by
  classical
  intro h
  let I : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := LinearMap.id
  have heq := h ℝ (Fin 2 → ℝ) I I
  have hsum : I + I = (2 : ℝ) • I := by
    module
  rw [hsum] at heq
  norm_num [I, LinearMap.det_smul] at heq

#print axioms GroundTruth.linear_algebra_9C_1_certificate
