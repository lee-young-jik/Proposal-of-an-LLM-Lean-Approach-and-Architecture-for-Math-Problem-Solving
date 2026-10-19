import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 600000
set_option maxRecDepth 2048

theorem GroundTruth.linear_algebra_7D_8_certificate :
¬ (
∀ (F : Type) [RCLike F] (V : Type) [NormedAddCommGroup V] [InnerProductSpace F V] [FiniteDimensional F V],
  ∀ (S : V →ₗ[F] V) (n : ℕ) (b : Module.Basis (Fin n) F V),
  Orthonormal F b → (∀ k, ‖S (b k)‖ = 1) → ((LinearMap.adjoint S).comp S = LinearMap.id ∧ S.comp (LinearMap.adjoint S) = LinearMap.id)
) := by
  classical
  intro h
  let S : ℂ →ₗ[ℝ] ℂ := (Complex.reLm + Complex.imLm).smulRight (1 : ℂ)
  let b : Module.Basis (Fin 2) ℝ ℂ := Complex.orthonormalBasisOneI.toBasis
  have hb : Orthonormal ℝ b := Complex.orthonormalBasisOneI.orthonormal
  have hbval : (b : Fin 2 → ℂ) = ![1, Complex.I] := Complex.coe_orthonormalBasisOneI
  have hn : ∀ k, ‖S (b k)‖ = 1 := by
    intro k
    rw [hbval]
    fin_cases k <;> norm_num [S, LinearMap.smulRight_apply]
  have he := (h ℝ ℂ S 2 b hb hn).1
  have hc := congrArg (fun L : ℂ →ₗ[ℝ] ℂ => L Complex.I) he
  change LinearMap.adjoint S (S Complex.I) = Complex.I at hc
  have hi := LinearMap.adjoint_inner_right S (1 : ℂ) (S Complex.I)
  rw [hc] at hi
  norm_num [S, Complex.inner, LinearMap.smulRight_apply] at hi

#print axioms GroundTruth.linear_algebra_7D_8_certificate
