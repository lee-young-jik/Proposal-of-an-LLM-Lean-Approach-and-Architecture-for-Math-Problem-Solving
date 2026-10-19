import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.linear_algebra_2A_10_certificate :
∀ (F : Type) [RCLike F] (V : Type) [AddCommGroup V] [Module F V],
  ∀ m : ℕ, 1 ≤ m → ∀ (v : Fin m → V) (a : F),
  LinearIndependent F v → a ≠ 0 → LinearIndependent F (fun i => a • v i) := by
  classical
  intro F _ V _ _ m hm v a hv ha
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro g hg i
  have hz : ∑ j, (g j * a) • v j = 0 := by
    simpa [smul_smul] using hg
  have hi : g i * a = 0 := hv (fun j => g j * a) hz i
  exact (mul_eq_zero.mp hi).resolve_right ha

#print axioms GroundTruth.linear_algebra_2A_10_certificate
