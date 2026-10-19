import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.calculus_30_3_1_conjecture_3_certificate :
∃ f : (ℝ × ℝ) → ℝ,
  ∃ θ φ : Fin 3 → ℝ,
  (0 ≤ θ 0 ∧ θ 0 < 2*Real.pi) ∧
  (∀ i, θ i < φ i) ∧
  (∀ i j, i < j → φ i < θ j) ∧
  φ (Fin.last 2) < θ 0 + 2*Real.pi ∧
  (∀ i, ∃ δ : ℝ, 0 < δ ∧ MonotoneOn (fun t : ℝ => f (t * Real.cos (θ i), t * Real.sin (θ i))) (Set.Icc 0 δ)) ∧
  (∀ i, ∃ δ : ℝ, 0 < δ ∧ AntitoneOn (fun t : ℝ => f (t * Real.cos (φ i), t * Real.sin (φ i))) (Set.Icc 0 δ)) := by
  classical
  refine ⟨fun _ => 0, (fun i : Fin 3 => 2*(i.val : ℝ)*Real.pi/3),
    (fun i : Fin 3 => (2*(i.val : ℝ)+1)*Real.pi/3), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
    exact Real.pi_pos
  · intro i
    dsimp
    linarith [Real.pi_pos]
  · intro i j hij
    have hval : i.val + 1 ≤ j.val := Nat.succ_le_iff.mpr hij
    have hcast : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by exact_mod_cast hval
    have hmul := mul_le_mul_of_nonneg_right hcast Real.pi_pos.le
    dsimp
    nlinarith [Real.pi_pos]
  · norm_num
    linarith [Real.pi_pos]
  · intro i
    exact ⟨1, by norm_num, fun _ _ _ _ _ => le_rfl⟩
  · intro i
    exact ⟨1, by norm_num, fun _ _ _ _ _ => le_rfl⟩

#print axioms GroundTruth.calculus_30_3_1_conjecture_3_certificate
