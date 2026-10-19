import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.basic_analysis_7_2_7_2_13_b_certificate :
¬ (
∀ (X : Type) [MetricSpace X] (x : X) (δ : ℝ), 0 < δ →
  closure (Metric.ball x δ) = Metric.closedBall x δ
) := by
  intro h
  have hb : Metric.ball (0 : ℤ) 1 = ({0} : Set ℤ) := by
    ext z
    simp only [Metric.mem_ball, Set.mem_singleton_iff]
    rw [Int.dist_eq]
    simp only [Int.cast_zero, sub_zero]
    constructor
    · intro hz
      have hz' := (abs_lt.mp hz)
      have hlo : (-1 : ℤ) < z := by exact_mod_cast hz'.1
      have hhi : z < (1 : ℤ) := by exact_mod_cast hz'.2
      omega
    · rintro rfl
      norm_num
  have heq := h ℤ (0 : ℤ) 1 (by norm_num)
  have heq' : closure ({0} : Set ℤ) = Metric.closedBall (0 : ℤ) 1 := by
    rw [← hb]
    exact heq
  have hmem : (1 : ℤ) ∈ Metric.closedBall (0 : ℤ) 1 := by
    simp [Metric.mem_closedBall]
  have hmem' : (1 : ℤ) ∈ closure ({0} : Set ℤ) := by
    rw [heq']
    exact hmem
  rw [isClosed_singleton.closure_eq] at hmem'
  norm_num at hmem'

#print axioms GroundTruth.basic_analysis_7_2_7_2_13_b_certificate
