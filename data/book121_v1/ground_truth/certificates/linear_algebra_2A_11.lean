import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.linear_algebra_2A_11_certificate :
¬ (
∀ (F : Type) [RCLike F] (V : Type) [AddCommGroup V] [Module F V],
  ∀ m : ℕ, 1 ≤ m → ∀ v w : Fin m → V,
  LinearIndependent F v → LinearIndependent F w → LinearIndependent F (fun i => v i+w i)
) := by
  classical
  intro h
  have hv : LinearIndependent ℝ (fun _ : Fin 1 => (1 : ℝ)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    fin_cases i
    simpa using hg
  have hw : LinearIndependent ℝ (fun _ : Fin 1 => (-1 : ℝ)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    fin_cases i
    simpa using hg
  have ht := h ℝ ℝ 1 (by omega)
    (fun _ : Fin 1 => (1 : ℝ))
    (fun _ : Fin 1 => (-1 : ℝ)) hv hw
  have hn := ht.ne_zero (0 : Fin 1)
  norm_num at hn

#print axioms GroundTruth.linear_algebra_2A_11_certificate
