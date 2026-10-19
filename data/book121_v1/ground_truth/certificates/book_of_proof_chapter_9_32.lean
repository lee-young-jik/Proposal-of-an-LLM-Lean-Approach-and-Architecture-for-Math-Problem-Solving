import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 600000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_chapter_9_32_certificate :
∀ n k : ℕ, 1 ≤ n → 1 ≤ k → Nat.Prime (Nat.choose n k) → k = 1 ∨ k = n-1 := by
  classical
  have hlo : ∀ n k : ℕ, 1 ≤ k → k < n → n ≤ Nat.choose n k := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro k hk hkn
      by_cases hk1 : k = 1
      · simpa [hk1]
      by_cases hkl : k = n-1
      · rw [← Nat.choose_symm (by omega : k ≤ n)]
        have he : n-k = 1 := by omega
        simp [he]
      have hn : 1 ≤ n := by omega
      have hnlt : n-1 < n := by omega
      have ha := ih (n-1) hnlt k hk (by omega)
      have hb := ih (n-1) hnlt (k-1) (by omega) (by omega)
      have he : Nat.choose n k = Nat.choose (n-1) (k-1) + Nat.choose (n-1) k := by
        have hn' : (n-1).succ = n := by omega
        have hk' : (k-1).succ = k := by omega
        simpa only [hn', hk'] using Nat.choose_succ_succ (n-1) (k-1)
      rw [he]
      omega
  intro n k hn hk hp
  by_contra h
  have hk1 : k ≠ 1 := fun he => h (Or.inl he)
  have hkl : k ≠ n-1 := fun he => h (Or.inr he)
  have hkn : k ≤ n := by
    by_contra hc
    have hz := Nat.choose_eq_zero_of_lt (by omega : n < k)
    rw [hz] at hp
    exact Nat.not_prime_zero hp
  have hklt : k < n := by
    by_contra hc
    have he : k = n := by omega
    subst k
    norm_num at hp
  have ha := hlo (n-1) k hk (by omega)
  have hb := hlo (n-1) (k-1) (by omega) (by omega)
  have he : Nat.choose n k = Nat.choose (n-1) (k-1) + Nat.choose (n-1) k := by
    have hn' : (n-1).succ = n := by omega
    have hk' : (k-1).succ = k := by omega
    simpa only [hn', hk'] using Nat.choose_succ_succ (n-1) (k-1)
  have hbig : n < Nat.choose n k := by rw [he]; omega
  have hbound := Nat.pow_factorization_choose_le (p := Nat.choose n k) (k := k) (by omega : 0 < n)
  have hf : (Nat.choose n k).factorization (Nat.choose n k) = 1 := hp.factorization_self
  rw [hf, pow_one] at hbound
  omega

#print axioms GroundTruth.book_of_proof_chapter_9_32_certificate
