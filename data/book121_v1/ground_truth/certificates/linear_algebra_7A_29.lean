import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 600000
set_option maxRecDepth 2048

theorem GroundTruth.linear_algebra_7A_29_certificate :
¬ (
∀ (F : Type) [RCLike F] (V : Type) [NormedAddCommGroup V] [InnerProductSpace F V] [FiniteDimensional F V],
  ∀ (T : V →ₗ[F] V) (n : ℕ) (b : Module.Basis (Fin n) F V),
  Orthonormal F b → (∀ k, ‖T (b k)‖ = ‖(LinearMap.adjoint T) (b k)‖) → (T.comp (LinearMap.adjoint T) = (LinearMap.adjoint T).comp T)
) := by
  classical
  intro h
  let S : ℂ →ₗ[ℝ] ℂ := (Complex.reLm+Complex.imLm).smulRight (1:ℂ) - Complex.reLm.smulRight Complex.I
  let A : ℂ →ₗ[ℝ] ℂ := (Complex.reLm-Complex.imLm).smulRight (1:ℂ) + Complex.reLm.smulRight Complex.I
  have hA : A = LinearMap.adjoint S := by
    apply (LinearMap.eq_adjoint_iff A S).mpr
    intro x y
    simp [A,S,Complex.inner,LinearMap.smulRight_apply]
    ring
  let b : Module.Basis (Fin 2) ℝ ℂ := Complex.orthonormalBasisOneI.toBasis
  have hb : Orthonormal ℝ b := Complex.orthonormalBasisOneI.orthonormal
  have hbval : (b : Fin 2 → ℂ) = ![1,Complex.I] := Complex.coe_orthonormalBasisOneI
  have hn : ∀ k, ‖S (b k)‖ = ‖(LinearMap.adjoint S) (b k)‖ := by
    intro k
    rw [← hA,hbval]
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    fin_cases k <;> norm_num [S,A,LinearMap.smulRight_apply,Complex.normSq_apply]
  have he := h ℝ ℂ S 2 b hb hn
  rw [← hA] at he
  have hc := congrArg (fun L : ℂ →ₗ[ℝ] ℂ => (L 1).im) he
  norm_num [S,A,LinearMap.smulRight_apply] at hc

#print axioms GroundTruth.linear_algebra_7A_29_certificate
