import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem JudsonGold.judson_10_4_10_certificate :
(∀ (G : Type) [Group G] (H : Subgroup G), H.index = 2 → H.Normal) ∧
  (∀ n : ℕ, 3 ≤ n → ¬ IsSimpleGroup (Equiv.Perm (Fin n))) := by
  constructor
  · intro G _ H h
    exact H.normal_of_index_eq_two h
  · intro n hn hs
    letI := hs
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    let A := alternatingGroup (Fin n)
    have hi : A.index = 2 := alternatingGroup.index_eq_two
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal A inferInstance with ha | ha
    · have hc := two_mul_nat_card_alternatingGroup (α := Fin n)
      have hf : 6 ≤ n.factorial := by simpa using Nat.factorial_le hn
      have hca : Nat.card A = 1 := by simp [ha]
      change 2 * Nat.card A = _ at hc
      rw [hca] at hc
      simp only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at hc
      omega
    · simp [ha] at hi

#print axioms JudsonGold.judson_10_4_10_certificate
