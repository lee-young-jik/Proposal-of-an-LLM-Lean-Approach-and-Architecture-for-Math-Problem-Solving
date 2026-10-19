import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.linear_algebra_2A_2_certificate :
∀ (F : Type) [RCLike F] (V : Type) [AddCommGroup V] [Module F V],
  ∀ v : Fin 4 → V, Submodule.span F (Set.range v) = ⊤ →
  Submodule.span F (Set.range (fun i : Fin 4 => if i.val = 0 then v 0-v 1 else if i.val = 1 then v 1-v 2 else if i.val = 2 then v 2-v 3 else v 3)) = ⊤ := by
  classical
  intro F _ V _ _ v h
  let w : Fin 4 → V := fun i =>
    if i.val = 0 then v 0 - v 1
    else if i.val = 1 then v 1 - v 2
    else if i.val = 2 then v 2 - v 3
    else v 3
  let S : Submodule F V := Submodule.span F (Set.range w)
  have hw (i : Fin 4) : w i ∈ S :=
    Submodule.subset_span ⟨i, rfl⟩
  have h3 : v 3 ∈ S := by
    simpa [w] using hw 3
  have h2 : v 2 ∈ S := by
    have ht := S.add_mem (hw 2) h3
    simpa [w] using ht
  have h1 : v 1 ∈ S := by
    have ht := S.add_mem (hw 1) h2
    simpa [w] using ht
  have h0 : v 0 ∈ S := by
    have ht := S.add_mem (hw 0) h1
    simpa [w] using ht
  change S = ⊤
  apply top_unique
  rw [← h]
  apply Submodule.span_le.2
  rintro x ⟨i, rfl⟩
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

#print axioms GroundTruth.linear_algebra_2A_2_certificate
