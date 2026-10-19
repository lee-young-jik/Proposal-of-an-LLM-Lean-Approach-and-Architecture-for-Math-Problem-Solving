import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.linear_algebra_1C_7_certificate :
∃ (U : Set (Fin (2 : ℕ) → ℝ)),
  U.Nonempty ∧ (∀ u ∈ U, ∀ v ∈ U, u + v ∈ U) ∧ (∀ u ∈ U, -u ∈ U) ∧ ∀ (W : Submodule ℝ (Fin (2 : ℕ) → ℝ)), ↑W ≠ U := by
  classical
  let U : Set (Fin 2 → ℝ) := {u | ∃ z : ℤ, u = fun _ => (z : ℝ)}
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun _ => 0, ?_⟩
    exact ⟨0, by funext i; simp⟩
  · intro u hu v hv
    rcases hu with ⟨z, rfl⟩
    rcases hv with ⟨w, rfl⟩
    refine ⟨z + w, ?_⟩
    funext i
    simp
  · intro u hu
    rcases hu with ⟨z, rfl⟩
    refine ⟨-z, ?_⟩
    funext i
    simp
  · intro W hWU
    have honeU : (fun _ : Fin 2 => (1 : ℝ)) ∈ U := by
      exact ⟨1, by funext i; simp⟩
    have honeW : (fun _ : Fin 2 => (1 : ℝ)) ∈ W := by
      change (fun _ : Fin 2 => (1 : ℝ)) ∈ (W : Set (Fin 2 → ℝ))
      rw [hWU]
      exact honeU
    have hscaled := W.smul_mem (1 / 2 : ℝ) honeW
    have hhalfW : (fun _ : Fin 2 => (1 / 2 : ℝ)) ∈ W := by
      convert hscaled using 1
      funext i
      norm_num [Pi.smul_apply]
    have hhalfU : (fun _ : Fin 2 => (1 / 2 : ℝ)) ∈ U := by
      change (fun _ : Fin 2 => (1 / 2 : ℝ)) ∈ (U : Set (Fin 2 → ℝ))
      rw [← hWU]
      exact hhalfW
    rcases hhalfU with ⟨z, hz⟩
    have hz' := congrFun hz (0 : Fin 2)
    have hcast : (2 : ℝ) * (z : ℝ) = 1 := by
      norm_num at hz' ⊢
      linarith
    have hint : (2 : ℤ) * z = 1 := by exact_mod_cast hcast
    omega

#print axioms GroundTruth.linear_algebra_1C_7_certificate
