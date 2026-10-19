import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.linear_algebra_7D_12_certificate :
¬ (
∀ (F : Type) [RCLike F] (V : Type) [NormedAddCommGroup V] [InnerProductSpace F V] [FiniteDimensional F V],
  ∀ S : V ≃ₗ[F] V,
  (∀ v : V, ‖S.symm v‖ = ‖S v‖) →
  (LinearMap.adjoint S.toLinearMap).comp S.toLinearMap = LinearMap.id ∧
  S.toLinearMap.comp (LinearMap.adjoint S.toLinearMap) = LinearMap.id
) := by
  classical
  intro h
  let T : ℂ →ₗ[ℝ] ℂ := (Complex.reLm + Complex.imLm).smulRight (1 : ℂ) - Complex.imLm.smulRight Complex.I
  have hTT : Function.Involutive T := by
    intro z
    apply Complex.ext <;> simp [T, LinearMap.smulRight_apply] <;> ring
  let S : ℂ ≃ₗ[ℝ] ℂ := LinearEquiv.ofInvolutive T hTT
  have hnorm : ∀ v : ℂ, ‖S.symm v‖ = ‖S v‖ := by
    intro v
    rfl
  have hc := congrArg (fun L : ℂ →ₗ[ℝ] ℂ => L Complex.I) (h ℝ ℂ S hnorm).1
  change LinearMap.adjoint T (T Complex.I) = Complex.I at hc
  have hi := LinearMap.adjoint_inner_left T Complex.I (T Complex.I)
  rw [hc] at hi
  norm_num [T, Complex.inner, LinearMap.smulRight_apply] at hi
  rw [← Complex.normSq_eq_norm_sq] at hi
  norm_num [Complex.normSq_apply] at hi

#print axioms GroundTruth.linear_algebra_7D_12_certificate
