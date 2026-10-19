import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.basic_analysis_7_2_7_2_11_b_certificate :
¬ (
∀ (X : Type) [MetricSpace X] (A : Set X), IsConnected A → IsConnected (interior A)
) := by
  intro h
  have hc := h ℝ ({0} : Set ℝ) isConnected_singleton
  have hn := hc.nonempty
  simpa using hn

#print axioms GroundTruth.basic_analysis_7_2_7_2_11_b_certificate
