import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_section_14_2_13_certificate :
({X : Set ℕ | X.Finite} : Set (Set ℕ)).Countable ∧
  ({X : Set ℕ | X.Finite} : Set (Set ℕ)).Infinite := by
  classical
  constructor
  · exact (Set.countable_range (fun s : Finset ℕ => (s : Set ℕ))).mono (by
      intro X hX
      have hfin : X.Finite := hX
      exact ⟨hfin.toFinset, by ext x; simp⟩)
  · let f : ℕ → Set ℕ := fun n => {n}
    have hf : Function.Injective f := by
      intro m n h
      have hm : m ∈ f m := by simp [f]
      rw [h] at hm
      simpa [f] using hm
    apply (Set.infinite_range_of_injective hf).mono
    rintro X ⟨n, rfl⟩
    simp [f]

#print axioms GroundTruth.book_of_proof_section_14_2_13_certificate
