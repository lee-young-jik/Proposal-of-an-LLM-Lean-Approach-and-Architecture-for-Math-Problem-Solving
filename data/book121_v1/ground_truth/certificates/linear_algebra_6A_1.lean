import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.linear_algebra_6A_1_certificate :
∀ (F : Type) [RCLike F] (V : Type) [NormedAddCommGroup V] [InnerProductSpace F V] [FiniteDimensional F V],
  ∀ m : ℕ, 1 ≤ m → ∀ v : Fin m → V,
  0 ≤ RCLike.re (∑ j : Fin m, ∑ k : Fin m, inner F (v j) (v k)) ∧
  RCLike.im (∑ j : Fin m, ∑ k : Fin m, inner F (v j) (v k)) = 0 := by
  classical
  intro F _ V _ _ _ m hm v
  have h : (∑ j : Fin m, ∑ k : Fin m, inner F (v j) (v k)) = inner F (∑ j, v j) (∑ k, v k) := by
    simp only [sum_inner, inner_sum]
    exact Finset.sum_comm
  rw [h]
  exact ⟨inner_self_nonneg, inner_self_im _⟩

#print axioms GroundTruth.linear_algebra_6A_1_certificate
