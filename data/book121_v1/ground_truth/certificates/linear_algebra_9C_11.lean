import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 600000
set_option maxRecDepth 2048

theorem GroundTruth.linear_algebra_9C_11_certificate :
¬ (
∀ (V : Type) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] (T : V →ₗ[ℝ] V),
  0 < LinearMap.det T → ∃ S : V →ₗ[ℝ] V, S.comp S = T
) := by
  classical
  intro h
  let D : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![-1,-2]
  let T : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := Matrix.toLin' D
  have hdet : 0 < LinearMap.det T := by norm_num [T,D,Matrix.det_diagonal,Fin.prod_univ_succ]
  obtain ⟨S,hS⟩ := h (Fin 2 → ℝ) T hdet
  let M : Matrix (Fin 2) (Fin 2) ℝ := LinearMap.toMatrix' S
  have hMM : M*M = D := by
    have he := congrArg (fun L : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) => LinearMap.toMatrix' L) hS
    simpa only [LinearMap.toMatrix'_comp, T, LinearMap.toMatrix'_toLin'] using he
  have h00 := congrArg (fun Q : Matrix (Fin 2) (Fin 2) ℝ => Q 0 0) hMM
  have h01 := congrArg (fun Q : Matrix (Fin 2) (Fin 2) ℝ => Q 0 1) hMM
  have h11 := congrArg (fun Q : Matrix (Fin 2) (Fin 2) ℝ => Q 1 1) hMM
  norm_num [Matrix.mul_apply,Fin.sum_univ_two,D,Matrix.diagonal,Fin.ext_iff] at h00 h01 h11
  have hsumne : M 0 0 + M 1 1 ≠ 0 := by
    intro hz
    have hd : M 1 1 = -M 0 0 := by linarith
    rw [hd] at h11
    nlinarith [h00]
  have hprod : (M 0 0 + M 1 1) * M 0 1 = 0 := by nlinarith [h01]
  have hb : M 0 1 = 0 := (mul_eq_zero.mp hprod).resolve_left hsumne
  rw [hb] at h00
  nlinarith [sq_nonneg (M 0 0)]

#print axioms GroundTruth.linear_algebra_9C_11_certificate
