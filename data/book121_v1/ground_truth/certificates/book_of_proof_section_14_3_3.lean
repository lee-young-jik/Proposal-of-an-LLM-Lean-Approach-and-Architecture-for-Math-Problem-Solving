import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_section_14_3_3_certificate :
∃ (α : Type) (A : Set α), ¬A.Countable ∧ Cardinal.mk ↑A ≠ Cardinal.mk ℝ := by
  classical
  let f : ℝ → Set ℝ := fun x => {x}
  have hf : Function.Injective f := by
    intro x y h
    have hx : x ∈ f y := h ▸ (by simp [f])
    simpa [f] using hx
  letI : Uncountable (Set ℝ) := hf.uncountable
  refine ⟨Set ℝ, Set.univ, Set.not_countable_univ, ?_⟩
  intro h
  have he : Cardinal.mk (Set ℝ) = Cardinal.mk ℝ := by
    simpa only [Cardinal.mk_univ] using h
  obtain ⟨e⟩ := Cardinal.eq.mp he
  exact Function.cantor_injective e e.injective

#print axioms GroundTruth.book_of_proof_section_14_3_3_certificate
