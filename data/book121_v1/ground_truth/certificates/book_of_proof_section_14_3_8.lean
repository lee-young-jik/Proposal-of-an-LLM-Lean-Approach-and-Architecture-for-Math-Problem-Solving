import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_section_14_3_8_certificate :
¬ (
(Set.univ : Set (ℕ+ → ℤ)).Countable ∧ (Set.univ : Set (ℕ+ → ℤ)).Infinite
) := by
  classical
  intro h
  letI : Countable (ℕ+ → ℤ) := Set.countable_univ_iff.mp h.1
  obtain ⟨f, hf⟩ := exists_surjective_nat (ℕ+ → ℤ)
  let g : ℕ+ → ℤ := fun n => f (n.val-1) n + 1
  obtain ⟨m, hm⟩ := hf g
  have hd := congrFun hm (⟨m+1, by omega⟩ : ℕ+)
  dsimp [g] at hd
  simp only [Nat.add_sub_cancel] at hd
  omega

#print axioms GroundTruth.book_of_proof_section_14_3_8_certificate
