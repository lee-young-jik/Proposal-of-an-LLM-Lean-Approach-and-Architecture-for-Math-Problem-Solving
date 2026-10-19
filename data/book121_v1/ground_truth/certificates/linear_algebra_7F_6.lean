import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.linear_algebra_7F_6_certificate :
¬ (
∀ (F : Type) [RCLike F] (V : Type) [NormedAddCommGroup V] [InnerProductSpace F V] [FiniteDimensional F V],
  ∀ S T : V →L[F] V, ‖S.comp T‖ = ‖T.comp S‖
) := by
  classical
  intro h
  let S : ℂ →L[ℝ] ℂ := Complex.reCLM.smulRight (1 : ℂ)
  let T : ℂ →L[ℝ] ℂ := Complex.imCLM.smulRight (1 : ℂ)
  have hST : S.comp T = T := by
    ext z
    simp [S, T, ContinuousLinearMap.smulRight_apply]
  have hTS : T.comp S = 0 := by
    ext z
    simp [S, T, ContinuousLinearMap.smulRight_apply]
  have hn := h ℝ ℂ S T
  rw [hST, hTS, norm_zero] at hn
  have htzero : T = 0 := norm_eq_zero.mp hn
  have hc := congrArg (fun L : ℂ →L[ℝ] ℂ => L Complex.I) htzero
  norm_num [T, ContinuousLinearMap.smulRight_apply] at hc

#print axioms GroundTruth.linear_algebra_7F_6_certificate
