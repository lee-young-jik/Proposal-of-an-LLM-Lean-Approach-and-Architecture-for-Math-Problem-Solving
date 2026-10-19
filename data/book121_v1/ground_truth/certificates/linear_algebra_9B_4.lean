import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 600000
set_option maxRecDepth 2048

theorem GroundTruth.linear_algebra_9B_4_certificate :
¬ (
∀ (F : Type) [RCLike F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V],
  ∀ a : AlternatingMap F V F (Fin 4),
  ∃ U : Submodule F (Fin 4 → V), (U : Set (Fin 4 → V)) = {v | a v = 0}
) := by
  classical
  intro h
  let a : AlternatingMap ℝ (Fin 4 → ℝ) ℝ (Fin 4) := Matrix.detRowAlternating
  let A : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![1,1,0,0]
  let B : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![0,0,1,1]
  have haA : a A = 0 := by change Matrix.det A = 0; norm_num [A, Matrix.det_diagonal, Fin.prod_univ_succ]
  have haB : a B = 0 := by change Matrix.det B = 0; norm_num [B, Matrix.det_diagonal, Fin.prod_univ_succ]
  have hsum : A+B = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [A,B,Matrix.diagonal,Matrix.one_apply]
  obtain ⟨U,hU⟩ := h ℝ (Fin 4 → ℝ) a
  have hA : A ∈ U := by change A ∈ (U : Set (Fin 4 → Fin 4 → ℝ)); rw [hU]; exact haA
  have hB : B ∈ U := by change B ∈ (U : Set (Fin 4 → Fin 4 → ℝ)); rw [hU]; exact haB
  have hAB := U.add_mem hA hB
  change A+B ∈ (U : Set (Fin 4 → Fin 4 → ℝ)) at hAB
  rw [hU] at hAB
  change Matrix.det (A+B) = 0 at hAB
  rw [hsum, Matrix.det_one] at hAB
  norm_num at hAB

#print axioms GroundTruth.linear_algebra_9B_4_certificate
