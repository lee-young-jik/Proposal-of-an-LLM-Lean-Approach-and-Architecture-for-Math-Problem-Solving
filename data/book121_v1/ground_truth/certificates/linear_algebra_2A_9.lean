import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.linear_algebra_2A_9_certificate :
∀ (F : Type) [RCLike F] (V : Type) [AddCommGroup V] [Module F V],
  ∀ m : ℕ, 2 ≤ m → ∀ v : ℕ → V, LinearIndependent F (fun i : Fin m => v i.val) →
  LinearIndependent F (fun i : Fin m => if i.val = 0 then (5 : F) • v 0 - (4 : F) • v 1 else v i.val) := by
  classical
  intro F _ V _ _ m hm v hv
  let w : Fin m → Fˣ := fun i => if i.val = 0 then Units.mk0 (5 : F) (by norm_num) else 1
  let u : Fin m → V := w • (fun i : Fin m => v i.val)
  have hu : LinearIndependent F u := hv.units_smul w
  let j : Fin m := ⟨1, by omega⟩
  let c : Fin m → F := fun i => if i.val = 0 then -4 else 0
  have hc : c j = 0 := by simp [c, j]
  have hnew : LinearIndependent F (u + (fun i => c i • u j)) :=
    (linearIndependent_add_smul_iff hc).mpr hu
  convert hnew using 1
  funext i
  by_cases hi : i.val = 0
  · simp [u, w, c, j, hi, sub_eq_add_neg]
  · simp [u, w, c, j, hi]

#print axioms GroundTruth.linear_algebra_2A_9_certificate
