import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.linear_algebra_5E_4_certificate :
¬ (
∀ (F : Type) [RCLike F] (n : ℕ) (A B : Matrix (Fin n) (Fin n) F),
  (∀ i j, i ≠ j → A i j = 0) → (∀ i j, j < i → B i j = 0) → A*B = B*A
) := by
  classical
  push_neg
  refine ⟨ℝ, inferInstance, 2, ![![0, 0], ![0, 1]], ![![0, 1], ![0, 0]], ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i j hji
    fin_cases i <;> fin_cases j <;> simp_all
  · intro h
    have h01 := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
    norm_num [Matrix.mul_apply, Fin.sum_univ_two] at h01

#print axioms GroundTruth.linear_algebra_5E_4_certificate
