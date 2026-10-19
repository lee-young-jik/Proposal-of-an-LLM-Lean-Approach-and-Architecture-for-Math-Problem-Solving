import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_section_14_2_5_certificate :
∃ S : Set ℝ, (∀ x ∈ S, Irrational x) ∧ S.Countable ∧ S.Infinite := by
  classical
  let f : ℕ → ℝ := fun n => Classical.choose (exists_irrational_btwn (show (n : ℝ) < n + 1 by norm_num))
  refine ⟨Set.range f, ?_, Set.countable_range f, ?_⟩
  · rintro x ⟨n, rfl⟩
    exact (Classical.choose_spec (exists_irrational_btwn (show (n : ℝ) < n + 1 by norm_num))).1
  · apply Set.infinite_range_of_injective
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij' | hji'
    · have hi := (Classical.choose_spec (exists_irrational_btwn (show (i : ℝ) < i + 1 by norm_num))).2.2
      have hj := (Classical.choose_spec (exists_irrational_btwn (show (j : ℝ) < j + 1 by norm_num))).2.1
      have hs : (i : ℝ) + 1 ≤ j := by
        exact_mod_cast (Nat.succ_le_of_lt hij')
      dsimp [f] at hij
      linarith
    · have hj := (Classical.choose_spec (exists_irrational_btwn (show (j : ℝ) < j + 1 by norm_num))).2.2
      have hi := (Classical.choose_spec (exists_irrational_btwn (show (i : ℝ) < i + 1 by norm_num))).2.1
      have hs : (j : ℝ) + 1 ≤ i := by
        exact_mod_cast (Nat.succ_le_of_lt hji')
      dsimp [f] at hij
      linarith

#print axioms GroundTruth.book_of_proof_section_14_2_5_certificate
