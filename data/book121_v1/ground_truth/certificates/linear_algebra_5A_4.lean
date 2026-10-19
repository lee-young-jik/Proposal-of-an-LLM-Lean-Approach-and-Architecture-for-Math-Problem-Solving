import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.linear_algebra_5A_4_certificate :
∀ (F : Type) [RCLike F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V],
  ∀ U : Submodule F V,
  (∀ T : V →ₗ[F] V, ∀ u ∈ U, T u ∈ U) → U = ⊥ ∨ U = ⊤ := by
  classical
  intro F _ V _ _ _ U hU
  by_cases hz : U = ⊥
  · exact Or.inl hz
  · right
    apply top_unique
    intro w hw
    obtain ⟨u, hu, hune⟩ := U.ne_bot_iff.mp hz
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one F hune
    have h := hU (φ.smulRight w) u hu
    simpa [hφ] using h

#print axioms GroundTruth.linear_algebra_5A_4_certificate
