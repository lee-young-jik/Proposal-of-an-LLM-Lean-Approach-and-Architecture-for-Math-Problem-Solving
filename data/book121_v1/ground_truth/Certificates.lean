import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 600000
set_option maxRecDepth 2048

theorem GroundTruth.book_of_proof_chapter_9_1_certificate :
∃ x y : ℝ, |x + y| ≠ |x| + |y| := by
  refine ⟨1, -1, ?_⟩
  norm_num

#print axioms GroundTruth.book_of_proof_chapter_9_1_certificate


theorem GroundTruth.book_of_proof_chapter_9_2_certificate :
∃ (n : ℕ), (1 : ℕ) ≤ n ∧ ¬Nat.Prime ((2 : ℤ) * ↑n ^ (2 : ℕ) - (4 : ℤ) * ↑n + (31 : ℤ)).toNat := by
  refine ⟨31, by norm_num, ?_⟩
  change ¬ Nat.Prime 1829
  intro hp
  have hd : 31 ∣ 1829 := by norm_num
  have h := (Nat.dvd_prime hp).mp hd
  omega

#print axioms GroundTruth.book_of_proof_chapter_9_2_certificate


theorem GroundTruth.book_of_proof_chapter_9_3_certificate :
∃ (n : ℤ), Even (n ^ (5 : ℕ) - n) ∧ ¬Even n := by
  refine ⟨1, ?_, ?_⟩ <;> norm_num

#print axioms GroundTruth.book_of_proof_chapter_9_3_certificate


theorem GroundTruth.book_of_proof_chapter_9_4_certificate :
∃ (n : ℕ), (1 : ℕ) ≤ n ∧ ¬Nat.Prime (n ^ (2 : ℕ) + (17 : ℕ) * n + (17 : ℕ)) := by
  refine ⟨17, ?_, ?_⟩ <;> norm_num

#print axioms GroundTruth.book_of_proof_chapter_9_4_certificate


theorem GroundTruth.book_of_proof_chapter_9_5_certificate :
∃ (α : Type) (β : Type) (A : Set α) (C : Set α) (B : Set β) (D : Set β), A ×ˢ B ∪ C ×ˢ D ≠ (A ∪ C) ×ˢ (B ∪ D) := by
  refine ⟨Fin 2, Fin 2, {0}, {1}, {0}, {1}, ?_⟩
  intro h
  have hh := congrArg (fun S : Set (Fin 2 × Fin 2) => ((0 : Fin 2), (1 : Fin 2)) ∈ S) h
  norm_num at hh

#print axioms GroundTruth.book_of_proof_chapter_9_5_certificate


theorem GroundTruth.book_of_proof_chapter_9_6_certificate :
∀ (α β : Type) (A C : Set α) (B D : Set β),
  (A ×ˢ B) ∩ (C ×ˢ D) = (A ∩ C) ×ˢ (B ∩ D) := by
  intro α β A C B D
  ext p
  simp only [Set.mem_prod, Set.mem_inter_iff]
  tauto

#print axioms GroundTruth.book_of_proof_chapter_9_6_certificate


theorem GroundTruth.book_of_proof_chapter_9_7_certificate :
∃ (α : Type) (β : Type) (A : Set α) (B : Set α) (C : Set β), A ×ˢ C = B ×ˢ C ∧ A ≠ B := by
  refine ⟨Fin 1, Fin 1, Set.univ, ∅, ∅, ?_, ?_⟩ <;> simp

#print axioms GroundTruth.book_of_proof_chapter_9_7_certificate


theorem GroundTruth.book_of_proof_chapter_9_8_certificate :
∃ (α : Type) (A : Set α) (B : Set α) (C : Set α), A \ (B ∪ C) ≠ A \ B ∪ A \ C := by
  refine ⟨Fin 2, Set.univ, {0}, {1}, ?_⟩
  intro h
  have hh := congrArg (fun S : Set (Fin 2) => (0 : Fin 2) ∈ S) h
  norm_num at hh

#print axioms GroundTruth.book_of_proof_chapter_9_8_certificate


theorem GroundTruth.book_of_proof_chapter_9_9_certificate :
∃ (α : Type) (A : Set α) (B : Set α), ¬𝒫 A \ 𝒫 B ⊆ 𝒫 (A \ B) := by
  refine ⟨Fin 2, Set.univ, {0}, ?_⟩
  intro h
  have hm : (Set.univ : Set (Fin 2)) ∈ Set.powerset Set.univ \ Set.powerset {0} := by
    constructor
    · intro x hx
      exact hx
    · intro hs
      have hh := hs (Set.mem_univ (1 : Fin 2))
      norm_num at hh
  have hh := h hm (Set.mem_univ (0 : Fin 2))
  exact hh.2 (by simp)

#print axioms GroundTruth.book_of_proof_chapter_9_9_certificate


theorem GroundTruth.book_of_proof_chapter_9_10_certificate :
∀ (α : Type) (A B : Set α), A ∩ B = ∅ →
  Set.powerset A \ Set.powerset B ⊆ Set.powerset (A \ B) := by
  intro α A B hAB S hS x hx
  constructor
  · exact hS.1 hx
  · intro hxB
    have hab : x ∈ A ∩ B := ⟨hS.1 hx, hxB⟩
    rw [hAB] at hab
    exact hab

#print axioms GroundTruth.book_of_proof_chapter_9_10_certificate


theorem GroundTruth.book_of_proof_chapter_9_11_certificate :
∃ (a : ℕ) (b : ℕ), (1 : ℕ) ≤ a ∧ (1 : ℕ) ≤ b ∧ a * b ≤ a + b := by
  refine ⟨1, 1, ?_, ?_, ?_⟩ <;> norm_num

#print axioms GroundTruth.book_of_proof_chapter_9_11_certificate


theorem GroundTruth.book_of_proof_chapter_9_12_certificate :
∃ (a : ℕ) (b : ℕ) (c : ℕ),
  (1 : ℕ) ≤ a ∧
    (1 : ℕ) ≤ b ∧
      (1 : ℕ) ≤ c ∧
        a * b % (2 : ℕ) = b * c % (2 : ℕ) ∧
          b * c % (2 : ℕ) = a * c % (2 : ℕ) ∧ (a % (2 : ℕ) = b % (2 : ℕ) → b % (2 : ℕ) ≠ c % (2 : ℕ)) := by
  refine ⟨1, 2, 2, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

#print axioms GroundTruth.book_of_proof_chapter_9_12_certificate


theorem GroundTruth.book_of_proof_chapter_9_13_certificate :
∃ X : Set (ℝ ⊕ Unit), Set.range (Sum.inl : ℝ → ℝ ⊕ Unit) ⊆ X ∧ Sum.inr () ∈ X := by
  refine ⟨Set.univ, ?_, ?_⟩ <;> simp

#print axioms GroundTruth.book_of_proof_chapter_9_13_certificate


theorem GroundTruth.book_of_proof_chapter_9_14_certificate :
∀ (α : Type) (A B : Set α), Set.powerset A ∩ Set.powerset B = Set.powerset (A ∩ B) := by
  intro α A B
  ext S
  change (S ⊆ A ∧ S ⊆ B) ↔ S ⊆ A ∩ B
  constructor
  · rintro ⟨hA,hB⟩ x hx
    exact ⟨hA hx,hB hx⟩
  · intro h
    exact ⟨fun x hx => (h hx).1, fun x hx => (h hx).2⟩

#print axioms GroundTruth.book_of_proof_chapter_9_14_certificate


theorem GroundTruth.book_of_proof_chapter_9_15_certificate :
∀ n : ℤ, Odd n → ∃ a b c : ℤ, Odd a ∧ Odd b ∧ Odd c ∧ n = a+b+c := by
  intro n hn
  refine ⟨n, 1, -1, hn, ?_, ?_, ?_⟩ <;> norm_num

#print axioms GroundTruth.book_of_proof_chapter_9_15_certificate


theorem GroundTruth.book_of_proof_chapter_9_16_certificate :
∃ (α : Type) (A : Finset α) (B : Finset α), (A ∪ B).card ≠ A.card + B.card := by
  refine ⟨Fin 1, {0}, {0}, ?_⟩
  norm_num

#print axioms GroundTruth.book_of_proof_chapter_9_16_certificate


theorem GroundTruth.book_of_proof_chapter_9_17_certificate :
∃ (α : Type) (A : Set α) (B : Set α), A \ B = ∅ ∧ B = ∅ := by
  refine ⟨Fin 1, ∅, ∅, ?_, ?_⟩ <;> simp

#print axioms GroundTruth.book_of_proof_chapter_9_17_certificate


theorem GroundTruth.book_of_proof_chapter_9_18_certificate :
∀ a b c : ℕ, 1 ≤ a → 1 ≤ b → 1 ≤ c →
  Even ((a : ℤ) - (b : ℤ)) ∨ Even ((a : ℤ) + (c : ℤ)) ∨ Even ((b : ℤ) - (c : ℤ)) := by
  intro a b c ha hb hc
  simp only [Int.even_iff]
  omega

#print axioms GroundTruth.book_of_proof_chapter_9_18_certificate


theorem GroundTruth.book_of_proof_chapter_9_19_certificate :
∀ r s : ℚ, r < s → ∃ u : ℝ, (r : ℝ) < u ∧ u < (s : ℝ) ∧ Irrational u := by
  intro r s hrs
  obtain ⟨u, hu, hru, hus⟩ := exists_irrational_btwn (show (r : ℝ) < (s : ℝ) by exact_mod_cast hrs)
  exact ⟨u, hru, hus, hu⟩

#print axioms GroundTruth.book_of_proof_chapter_9_19_certificate


theorem GroundTruth.book_of_proof_chapter_9_20_certificate :
∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ (p : ℤ) - (q : ℤ) = 1000 := by
  refine ⟨1013, 13, ?_, ?_, ?_⟩ <;> norm_num

#print axioms GroundTruth.book_of_proof_chapter_9_20_certificate


theorem GroundTruth.book_of_proof_chapter_9_21_certificate :
∀ (p q : ℕ), Nat.Prime p → Nat.Prime q → ↑p - ↑q ≠ (97 : ℤ) := by
  intro p q hp hq h
  have hpne : p ≠ 2 := by
    intro hp2
    subst p
    have hq2 := hq.two_le
    omega
  rcases hp.odd_of_ne_two hpne with ⟨k,hk⟩
  by_cases hq2 : q = 2
  · subst q
    have hp99 : p = 99 := by omega
    rw [hp99] at hp
    norm_num at hp
  · rcases hq.odd_of_ne_two hq2 with ⟨j,hj⟩
    omega

#print axioms GroundTruth.book_of_proof_chapter_9_21_certificate


theorem GroundTruth.book_of_proof_chapter_9_22_certificate :
∀ p q : ℕ, Nat.Prime p → Nat.Prime q → p < q → Odd (2*p + q^2) := by
  intro p q hp hq hpq
  have hqne : q ≠ 2 := by
    intro hq2
    subst q
    have hp2 := hp.two_le
    omega
  rcases hq.odd_of_ne_two hqne with ⟨k,hk⟩
  refine ⟨p+2*k*k+2*k, ?_⟩
  rw [hk]
  ring

#print axioms GroundTruth.book_of_proof_chapter_9_22_certificate


theorem GroundTruth.book_of_proof_chapter_9_23_certificate :
∀ x y : ℝ, x^3 < y^3 → x < y := by
  intro x y h
  exact (Odd.strictMono_pow (R := ℝ) (by decide : Odd 3)).lt_iff_lt.mp h

#print axioms GroundTruth.book_of_proof_chapter_9_23_certificate


theorem GroundTruth.book_of_proof_chapter_9_24_certificate :
∃ (x : ℝ), (0 : ℝ) < x ∧ (2 : ℝ) * x < x + (1 : ℝ) := by
  refine ⟨1/2, ?_, ?_⟩ <;> norm_num

#print axioms GroundTruth.book_of_proof_chapter_9_24_certificate


theorem GroundTruth.book_of_proof_chapter_9_25_certificate :
∃ (a : ℤ) (b : ℤ) (c : ℤ), a ∣ b * c ∧ ¬a ∣ b ∧ ¬a ∣ c := by
  refine ⟨6, 2, 3, ?_, ?_, ?_⟩ <;> norm_num

#print axioms GroundTruth.book_of_proof_chapter_9_25_certificate


theorem GroundTruth.book_of_proof_chapter_9_26_certificate :
∃ (α : Type) (A : Set α) (B : Set α) (C : Set α), A = B \ C ∧ B ≠ A ∪ C := by
  refine ⟨Fin 1, ∅, ∅, Set.univ, by simp, ?_⟩
  intro h
  have hh := congrArg (fun S : Set (Fin 1) => (0 : Fin 1) ∈ S) h
  simpa using hh

#print axioms GroundTruth.book_of_proof_chapter_9_26_certificate


theorem GroundTruth.book_of_proof_chapter_9_27_certificate :
∀ (S : Finset ℝ), S.card = (3 : ℕ) → ∃ (x : ℝ), x ∈ S ∧ x ^ (2 : ℕ) ≠ (2 : ℝ) * x ∨ x ∉ S ∧ x ^ (2 : ℕ) = (2 : ℝ) * x := by
  classical
  intro S hcard
  by_cases hbad : ∃ x : ℝ, x ∈ S ∧ x ^ 2 ≠ 2 * x
  · rcases hbad with ⟨x, hxS, hx⟩
    exact ⟨x, Or.inl ⟨hxS, hx⟩⟩
  · exfalso
    push_neg at hbad
    have hsub : S ⊆ ({0, 2} : Finset ℝ) := by
      intro x hxS
      have heq := hbad x hxS
      have hfactor : x * (x - 2) = 0 := by
        nlinarith [heq]
      rcases mul_eq_zero.mp hfactor with hx0 | hx2
      · simp [hx0]
      · have hx : x = 2 := by nlinarith
        simp [hx]
    have hc := Finset.card_le_card hsub
    rw [hcard] at hc
    norm_num at hc

#print axioms GroundTruth.book_of_proof_chapter_9_27_certificate


theorem GroundTruth.book_of_proof_chapter_9_28_certificate :
∃ (a : ℤ) (b : ℤ), a ∣ b ∧ b ∣ a ∧ a ≠ b := by
  refine ⟨1, -1, ?_, ?_, ?_⟩ <;> norm_num

#print axioms GroundTruth.book_of_proof_chapter_9_28_certificate


theorem GroundTruth.book_of_proof_chapter_9_29_certificate :
∃ (x : ℝ) (y : ℝ), |x + y| = |x - y| ∧ y ≠ (0 : ℝ) := by
  refine ⟨0, 1, ?_, ?_⟩ <;> norm_num

#print axioms GroundTruth.book_of_proof_chapter_9_29_certificate


theorem GroundTruth.book_of_proof_chapter_9_30_certificate :
∀ (a b : ℤ), (42 : ℤ) * a + (7 : ℤ) * b ≠ (1 : ℤ) := by
  intro a b h
  omega

#print axioms GroundTruth.book_of_proof_chapter_9_30_certificate


theorem GroundTruth.book_of_proof_chapter_9_31_certificate :
∃ (m : ℕ), m ≠ (1 : ℕ) ∧ ∃ (S : Finset (ℕ × ℕ)), (∀ p ∈ S, p.2 ≤ p.1 ∧ p.1.choose p.2 = m) ∧ (4 : ℕ) < S.card := by
  refine ⟨3003, ?_, {(14,6),(14,8),(15,5),(15,10),(78,2),(78,76)}, ?_, ?_⟩
  · norm_num
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with h|h|h|h|h|h <;> subst p <;> decide
  · norm_num

#print axioms GroundTruth.book_of_proof_chapter_9_31_certificate


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


theorem GroundTruth.book_of_proof_chapter_9_33_certificate :
∀ n : ℕ, 1 ≤ n → ∀ a : Fin (n+1) → ℕ, (∀ i, 1 ≤ a i) →
  ∃ k : ℕ, 1 ≤ k ∧ ¬ Nat.Prime (∑ i : Fin (n+1), a i * k^(i.val)) := by
  classical
  intro n hn a ha
  let M : ℕ := ∑ i : Fin (n+1), a i
  have hsize : n+1 ≤ M := by
    calc
      n+1 = ∑ i : Fin (n+1), (1 : ℕ) := by simp
      _ ≤ ∑ i : Fin (n+1), a i := Finset.sum_le_sum (fun i _ => ha i)
  have hM : 2 ≤ M := by omega
  let k : ℕ := M+1
  refine ⟨k, by dsimp [k]; omega, ?_⟩
  intro hp
  have hkm : Nat.ModEq M k 1 := by
    change (M+1) % M = 1 % M
    simp [Nat.add_mod]
  have hterm (i : Fin (n+1)) : Nat.ModEq M (a i*k^i.val) (a i) := by
    simpa using (Nat.ModEq.refl (a i)).mul (hkm.pow i.val)
  have hsum : Nat.ModEq M (∑ i : Fin (n+1), a i*k^i.val) M :=
    Nat.ModEq.sum (fun i _ => hterm i)
  have hzero : Nat.ModEq M M 0 := Nat.modEq_zero_iff_dvd.mpr (dvd_refl M)
  have hdvd : M ∣ ∑ i : Fin (n+1), a i*k^i.val :=
    Nat.modEq_zero_iff_dvd.mp (hsum.trans hzero)
  let j : Fin (n+1) := ⟨1, by omega⟩
  have hj : j.val = 1 := rfl
  have hs : a j*k^j.val ≤ ∑ i : Fin (n+1), a i*k^i.val :=
    Finset.single_le_sum (f := fun i : Fin (n+1) => a i*k^i.val) (fun i _ => Nat.zero_le (a i*k^i.val)) (Finset.mem_univ j)
  have hk : k ≤ a j*k := by
    simpa using Nat.mul_le_mul_right k (ha j)
  rw [hj, pow_one] at hs
  have hsmall : M < ∑ i : Fin (n+1), a i*k^i.val := by
    have hMk : M < k := by dsimp [k]; omega
    omega
  rcases (Nat.dvd_prime hp).mp hdvd with h|h <;> omega

#print axioms GroundTruth.book_of_proof_chapter_9_33_certificate


theorem GroundTruth.book_of_proof_chapter_9_34_certificate :
∃ (α : Type) (X : Set α) (A : Set α) (B : Set α), X ⊆ A ∪ B ∧ ¬X ⊆ A ∧ ¬X ⊆ B := by
  refine ⟨Fin 2, Set.univ, {0}, {1}, ?_, ?_, ?_⟩
  · intro x hx
    fin_cases x <;> simp
  · intro h
    have hh := h (Set.mem_univ (1 : Fin 2))
    norm_num at hh
  · intro h
    have hh := h (Set.mem_univ (0 : Fin 2))
    norm_num at hh

#print axioms GroundTruth.book_of_proof_chapter_9_34_certificate


theorem GroundTruth.book_of_proof_chapter_9_35_certificate :
∃ (n : ℕ), Nat.Prime n ∧ ¬Nat.Prime ((2 : ℕ) ^ n - (1 : ℕ)) := by
  refine ⟨11, ?_, ?_⟩ <;> norm_num

#print axioms GroundTruth.book_of_proof_chapter_9_35_certificate


theorem GroundTruth.book_of_proof_section_11_2_15_certificate :
∃ (α : Type) (R : α → α → Prop), Symmetric R ∧ Transitive R ∧ ¬Reflexive R := by
  refine ⟨Fin 1, (fun _ _ => False), ?_, ?_, ?_⟩
  · intro a b h; exact h.elim
  · intro a b c h; exact h.elim
  · intro h; exact h 0

#print axioms GroundTruth.book_of_proof_section_11_2_15_certificate


theorem GroundTruth.book_of_proof_section_11_3_11_certificate :
∃ (α : Type) (A : Set α) (R : ↑A → ↑A → Prop),
  A.Infinite ∧ Equivalence R ∧ (Set.range fun (a : ↑A) => {b : ↑A | R a b}).Finite := by
  classical
  refine ⟨ℕ, Set.univ, (fun _ _ => True), ?_, ?_, ?_⟩
  · exact Set.infinite_univ
  · refine ⟨?_, ?_, ?_⟩
    · intro x
      trivial
    · intro x y h
      trivial
    · intro x y z hxy hyz
      trivial
  · have heq :
        Set.range (fun a : (Set.univ : Set ℕ) =>
          {b : (Set.univ : Set ℕ) | True}) =
          ({Set.univ} : Set (Set (Set.univ : Set ℕ))) := by
      ext C
      constructor
      · rintro ⟨a, rfl⟩
        simp
      · intro hC
        have hCU : C = (Set.univ : Set (Set.univ : Set ℕ)) := by
          simpa using hC
        subst C
        refine ⟨⟨0, by simp⟩, ?_⟩
        ext b
        simp
    rw [heq]
    exact Set.finite_singleton _

#print axioms GroundTruth.book_of_proof_section_11_3_11_certificate


theorem GroundTruth.book_of_proof_section_11_3_12_certificate :
∃ (α : Type) (R : α → α → Prop) (S : α → α → Prop),
  Equivalence R ∧ Equivalence S ∧ ¬Equivalence fun (a b : α) => R a b ∨ S a b := by
  classical
  let R : Fin 3 → Fin 3 → Prop := fun a b => (a = 1 ↔ b = 1)
  let S : Fin 3 → Fin 3 → Prop := fun a b => (a = 0 ↔ b = 0)
  refine ⟨Fin 3, R, S, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro a
      exact Iff.rfl
    · intro a b hab
      exact hab.symm
    · intro a b c hab hbc
      exact hab.trans hbc
  · refine ⟨?_, ?_, ?_⟩
    · intro a
      exact Iff.rfl
    · intro a b hab
      exact hab.symm
    · intro a b c hab hbc
      exact hab.trans hbc
  · intro h
    have h02 : R (0 : Fin 3) 2 ∨ S (0 : Fin 3) 2 := by
      left
      simp [R]
    have h21 : R (2 : Fin 3) 1 ∨ S (2 : Fin 3) 1 := by
      right
      simp [S]
    have h01 : R (0 : Fin 3) 1 ∨ S (0 : Fin 3) 1 := h.3 h02 h21
    rcases h01 with hR | hS
    · simp [R] at hR
    · simp [S] at hS

#print axioms GroundTruth.book_of_proof_section_11_3_12_certificate


theorem GroundTruth.book_of_proof_section_12_3_7_certificate :
∀ (n : ℕ) (X : Finset ℕ), (∀ x ∈ X, 1 ≤ x ∧ x ≤ 2*n) →
  n < X.card → ∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧ x ∣ y := by
  classical
  intro n X hX hcard
  have hex : ∀ x : ℕ, ∃ e m : ℕ, x ≠ 0 → Odd m ∧ x = 2^e*m := by
    intro x
    by_cases hx : x = 0
    · exact ⟨0, 1, fun h => False.elim (h hx)⟩
    · obtain ⟨e,m,hm,he⟩ := Nat.exists_eq_two_pow_mul_odd hx
      exact ⟨e,m,fun _ => ⟨hm,he⟩⟩
  choose e m hm using hex
  have hbound : ∀ x ∈ X, m x / 2 < n := by
    intro x hx
    have hxpos := (hX x hx).1
    have hxm := hm x (by omega)
    have hp : 1 ≤ 2^(e x) := Nat.succ_le_iff.mpr (by positivity)
    have hmul : m x ≤ 2^(e x)*m x := by nlinarith
    have hle : m x ≤ 2*n := by have := (hX x hx).2; omega
    obtain ⟨k,hk⟩ := hxm.1
    omega
  obtain ⟨x,hx,y,hy,hne,heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := X) (t := Finset.range n) (f := fun x => m x / 2)
    (by simpa using hcard) (by intro x hx; exact Finset.mem_range.mpr (hbound x hx))
  have hxpos := (hX x hx).1
  have hypos := (hX y hy).1
  have hxm := hm x (by omega)
  have hym := hm y (by omega)
  have hmxy : m x = m y := by
    obtain ⟨a,ha⟩ := hxm.1
    obtain ⟨b,hb⟩ := hym.1
    omega
  by_cases he : e x ≤ e y
  · refine ⟨x,hx,y,hy,hne,?_⟩
    rw [hxm.2, hym.2, ← hmxy]
    exact mul_dvd_mul (pow_dvd_pow 2 he) (dvd_refl (m x))
  · refine ⟨y,hy,x,hx,hne.symm,?_⟩
    rw [hxm.2, hym.2, hmxy]
    exact mul_dvd_mul (pow_dvd_pow 2 (by omega : e y ≤ e x)) (dvd_refl (m y))

#print axioms GroundTruth.book_of_proof_section_12_3_7_certificate


theorem GroundTruth.book_of_proof_section_12_6_6_certificate :
∃ (α : Type) (β : Type) (f : α → β) (Y : Set β), f '' (f ⁻¹' Y) ≠ Y := by
  refine ⟨Fin 1, Fin 2, (fun _ => 0), Set.univ, ?_⟩
  intro h
  have hh := congrArg (fun S : Set (Fin 2) => (1 : Fin 2) ∈ S) h
  norm_num at hh

#print axioms GroundTruth.book_of_proof_section_12_6_6_certificate


theorem GroundTruth.book_of_proof_section_12_6_13_certificate :
∀ (α β : Type) (f : α → β) (X : Set α), Set.image f (Set.preimage f (Set.image f X)) = Set.image f X := by
  intro α β f X
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, ⟨x, hx, rfl⟩, rfl⟩

#print axioms GroundTruth.book_of_proof_section_12_6_13_certificate


theorem GroundTruth.book_of_proof_section_12_6_14_certificate :
∀ (α β : Type) (f : α → β) (Y : Set β), Set.preimage f (Set.image f (Set.preimage f Y)) = Set.preimage f Y := by
  intro α β f Y
  exact Set.preimage_image_preimage

#print axioms GroundTruth.book_of_proof_section_12_6_14_certificate


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


theorem GroundTruth.book_of_proof_section_14_2_6_certificate :
∀ (f : ℚ → ℝ), ¬Function.Bijective f := by
  intro f hf
  have hrange : Set.range f = (Set.univ : Set ℝ) := Set.range_eq_univ.mpr hf.2
  have hc : (Set.univ : Set ℝ).Countable := by
    rw [← hrange]
    exact Set.countable_range f
  exact Set.not_countable_univ hc

#print axioms GroundTruth.book_of_proof_section_14_2_6_certificate


theorem GroundTruth.book_of_proof_section_14_2_7_certificate :
(Set.univ : Set (Fin 100 → ℚ)).Countable ∧ (Set.univ : Set (Fin 100 → ℚ)).Infinite := by
  constructor
  · exact Set.countable_univ
  · exact Set.infinite_univ

#print axioms GroundTruth.book_of_proof_section_14_2_7_certificate


theorem GroundTruth.book_of_proof_section_14_2_8_certificate :
(Set.univ : Set (ℤ × ℚ)).Countable ∧ (Set.univ : Set (ℤ × ℚ)).Infinite := by
  constructor
  · exact Set.countable_univ
  · exact Set.infinite_univ

#print axioms GroundTruth.book_of_proof_section_14_2_8_certificate


theorem GroundTruth.book_of_proof_section_14_2_9_certificate :
(Set.univ : Set (({x : ℕ | x = 0 ∨ x = 1} × ℕ+))).Countable ∧ (Set.univ : Set (({x : ℕ | x = 0 ∨ x = 1} × ℕ+))).Infinite := by
  classical
  letI : Nonempty {x : ℕ | x = 0 ∨ x = 1} := ⟨⟨0, Or.inl rfl⟩⟩
  constructor
  · exact Set.countable_univ
  · exact Set.infinite_univ

#print axioms GroundTruth.book_of_proof_section_14_2_9_certificate


theorem GroundTruth.book_of_proof_section_14_2_10_certificate :
let A : Set ℝ := {x | ∃ n : ℕ, 1 ≤ n ∧ x = Real.sqrt 2 / (n : ℝ)};
  A.Countable ∧ A.Infinite := by
  dsimp
  constructor
  · exact (Set.countable_range (fun n : ℕ => Real.sqrt 2 / (n : ℝ))).mono (by
      rintro x ⟨n, hn, rfl⟩
      exact ⟨n, rfl⟩)
  · let f : ℕ → ℝ := fun n => Real.sqrt 2 / ((n + 1 : ℕ) : ℝ)
    have hf : Function.Injective f := by
      intro m n h
      have hs : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
      have hm : (((m + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      have hcross :
          Real.sqrt (2 : ℝ) * ((n + 1 : ℕ) : ℝ) =
            Real.sqrt (2 : ℝ) * ((m + 1 : ℕ) : ℝ) :=
        (div_eq_div_iff hm hn).mp h
      have hc : (((n + 1 : ℕ) : ℝ)) = (((m + 1 : ℕ) : ℝ)) :=
        mul_left_cancel₀ hs hcross
      have hnm : n + 1 = m + 1 := by
        exact_mod_cast hc
      exact (Nat.add_right_cancel hnm).symm
    apply (Set.infinite_range_of_injective hf).mono
    rintro x ⟨n, rfl⟩
    exact ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n), rfl⟩

#print axioms GroundTruth.book_of_proof_section_14_2_10_certificate


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


theorem GroundTruth.book_of_proof_section_14_3_4_certificate :
∀ (α : Type) (A B C : Set α), A ⊆ B → B ⊆ C →
  A.Countable → A.Infinite → C.Countable → C.Infinite → B.Countable ∧ B.Infinite := by
  intro α A B C hAB hBC hAc hAi hCc hCi
  constructor
  · exact hCc.mono hBC
  · exact hAi.mono hAB

#print axioms GroundTruth.book_of_proof_section_14_3_4_certificate


theorem GroundTruth.book_of_proof_section_14_3_5_certificate :
¬ (Set.univ : Set ({x : ℕ | x = 0 ∨ x = 1} × ℝ)).Countable := by
  classical
  intro h
  have himg :
      ((fun p : {x : ℕ | x = 0 ∨ x = 1} × ℝ => p.2) '' Set.univ).Countable :=
    h.image (fun p => p.2)
  have heq :
      (fun p : {x : ℕ | x = 0 ∨ x = 1} × ℝ => p.2) '' Set.univ =
        (Set.univ : Set ℝ) := by
    ext x
    constructor
    · intro hx
      trivial
    · intro hx
      exact ⟨(⟨0, by simp⟩, x), by simp⟩
  have hu : (Set.univ : Set ℝ).Countable := by
    rw [← heq]
    exact himg
  have hr : Countable ℝ := Set.countable_univ_iff.mp hu
  exact not_countable hr

#print axioms GroundTruth.book_of_proof_section_14_3_5_certificate


theorem GroundTruth.book_of_proof_section_14_3_6_certificate :
∃ (α : Type) (A : Set α), A.Infinite ∧ ∀ (B : Set α), A ⊆ B → B.Countable → B.Finite := by
  classical
  refine ⟨ℝ, Set.univ, Set.infinite_univ, ?_⟩
  intro B hAB hBc
  have hB : B = Set.univ := Set.eq_univ_of_univ_subset hAB
  subst B
  exact (not_countable (Set.countable_univ_iff.mp hBc)).elim

#print axioms GroundTruth.book_of_proof_section_14_3_6_certificate


theorem GroundTruth.book_of_proof_section_14_3_7_certificate :
∀ (α : Type) (A B : Set α), A ⊆ B → A.Countable → A.Infinite →
  ¬ B.Countable → ¬ (B \ A).Countable := by
  classical
  intro α A B hAB hAcount _ hBuncount hDiffCount
  apply hBuncount
  have hEq : B = A ∪ (B \ A) := by
    ext x
    constructor
    · intro hx
      by_cases hxa : x ∈ A
      · exact Or.inl hxa
      · exact Or.inr ⟨hx, hxa⟩
    · rintro (hx | hx)
      · exact hAB hx
      · exact hx.1
  rw [hEq]
  exact hAcount.union hDiffCount

#print axioms GroundTruth.book_of_proof_section_14_3_7_certificate


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


theorem GroundTruth.book_of_proof_section_14_4_7_certificate :
∀ (α β : Type), (∃ f : α → β, Function.Injective f) →
  (∃ g : α → β, Function.Surjective g) → ∃ h : α → β, Function.Bijective h := by
  classical
  intro α β ⟨f, hf⟩ ⟨g, hg⟩
  let k : β → α := fun y => Classical.choose (hg y)
  have hk : Function.Injective k := by
    intro y z h
    have hy : g (k y) = y := Classical.choose_spec (hg y)
    have hz : g (k z) = z := Classical.choose_spec (hg z)
    rw [h] at hy
    exact hy.symm.trans hz
  exact Function.Embedding.schroeder_bernstein hf hk

#print axioms GroundTruth.book_of_proof_section_14_4_7_certificate


theorem GroundTruth.basic_analysis_2_1_2_1_1_certificate :
∀ M : ℝ, ∃ n : ℕ, 1 ≤ n ∧ M < |3*(n : ℝ)| := by
  intro M
  obtain ⟨n, hn⟩ := exists_nat_gt (max M 1)
  have hM : M < (n : ℝ) := lt_of_le_of_lt (le_max_left M 1) hn
  have h1 : (1 : ℝ) < (n : ℝ) := lt_of_le_of_lt (le_max_right M 1) hn
  refine ⟨n, ?_, ?_⟩
  · exact_mod_cast h1.le
  · rw [abs_of_nonneg (by positivity)]
    nlinarith

#print axioms GroundTruth.basic_analysis_2_1_2_1_1_certificate


theorem GroundTruth.basic_analysis_2_1_2_1_15_a_certificate :
∀ M : ℝ, ∃ n : ℕ, 1 ≤ n ∧ M < |(if Odd n then (n : ℝ) else 1/(n : ℝ))| := by
  intro M
  obtain ⟨k, hk⟩ := exists_nat_gt (max M 1)
  have hM : M < (k : ℝ) := lt_of_le_of_lt (le_max_left M 1) hk
  have ho : Odd (2*k+1) := ⟨k, by omega⟩
  refine ⟨2*k+1, by omega, ?_⟩
  simp only [if_pos ho]
  rw [abs_of_nonneg (by positivity)]
  push_cast
  nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]

#print axioms GroundTruth.basic_analysis_2_1_2_1_15_a_certificate


theorem GroundTruth.basic_analysis_2_2_2_2_7_certificate :
∃ u : ℕ → ℝ,
  (∃ l : ℝ, Tendsto (fun n : ℕ => u (n^2)) atTop (nhds l)) ∧
  ∀ L : ℝ, ¬ Tendsto u atTop (nhds L) := by
  classical
  let u : ℕ → ℝ := fun n => if ∃ k : ℕ, n = k^2 then 0 else 1
  have h0 : ∀ n : ℕ, u (n^2) = 0 := by intro n; simp [u]
  have h1 : ∀ n : ℕ, 1 ≤ n → u (n^2+1) = 1 := by
    intro n hn
    have hns : ¬ ∃ k : ℕ, n^2+1 = k^2 := by
      rintro ⟨k, hk⟩
      by_cases hkn : k ≤ n
      · nlinarith [Nat.pow_le_pow_left hkn 2]
      · have hnk : n+1 ≤ k := by omega
        nlinarith [Nat.pow_le_pow_left hnk 2]
    simp [u, hns]
  have ht0 : Tendsto (fun n : ℕ => n^2) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (max b 1)] with n hn
    have hb : b ≤ n := (le_max_left b 1).trans hn
    have hn1 : 1 ≤ n := (le_max_right b 1).trans hn
    nlinarith
  have ht1 : Tendsto (fun n : ℕ => n^2+1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (max b 1)] with n hn
    have hb : b ≤ n := (le_max_left b 1).trans hn
    have hn1 : 1 ≤ n := (le_max_right b 1).trans hn
    nlinarith
  refine ⟨u, ⟨0, ?_⟩, ?_⟩
  · simpa only [h0] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  · intro L hL
    have hz : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds L) := by
      simpa only [Function.comp_def, h0] using hL.comp ht0
    have ho : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds L) := by
      apply (hL.comp ht1).congr'
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      exact h1 n hn
    have hL0 : L = 0 := tendsto_nhds_unique hz tendsto_const_nhds
    have hL1 : L = 1 := tendsto_nhds_unique ho tendsto_const_nhds
    linarith

#print axioms GroundTruth.basic_analysis_2_2_2_2_7_certificate


theorem GroundTruth.basic_analysis_2_4_2_4_8_certificate :
∃ (u : ℕ → ℝ),
  CauchySeq u ∧ ∀ (M : ℕ), (1 : ℕ) ≤ M → ∃ (n : ℕ), M ≤ n ∧ |u n - u (n - (1 : ℕ))| < |u (n + (1 : ℕ)) - u n| := by
  classical
  let u : ℕ → ℝ := fun n => if n % 3 = 0 then (1/2 : ℝ)^n else 0
  have hg : Tendsto (fun n : ℕ => (1/2 : ℝ)^n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hu : Tendsto u atTop (nhds 0) := by
    apply squeeze_zero (g := fun n : ℕ => (1/2 : ℝ)^n) ?_ ?_ hg
    · intro n; dsimp [u]; split_ifs <;> first | exact le_rfl | positivity
    · intro n; dsimp [u]; split_ifs <;> first | exact le_rfl | positivity
  have hc : CauchySeq u := hu.cauchySeq
  refine ⟨u, hc, ?_⟩
  intro M hM
  let n : ℕ := 3*(M+1)+2
  have hn : M ≤ n := by dsimp [n]; omega
  have hn0 : n % 3 ≠ 0 := by dsimp [n]; omega
  have hn1 : (n-1) % 3 ≠ 0 := by dsimp [n]; omega
  have hn2 : (n+1) % 3 = 0 := by dsimp [n]; omega
  refine ⟨n, hn, ?_⟩
  have hp : 0 < (1/2 : ℝ)^(n+1) := by positivity
  simpa only [u, if_neg hn0, if_neg hn1, if_pos hn2, sub_self, sub_zero, abs_zero] using (abs_pos.mpr (ne_of_gt hp))

#print axioms GroundTruth.basic_analysis_2_4_2_4_8_certificate


theorem GroundTruth.basic_analysis_3_3_3_3_13_certificate :
∃ (f : ℝ → ℝ), Continuous f ∧ (∃ (M : ℝ), ∀ (n : ℤ), |f ↑n| ≤ M) ∧ ∀ (M : ℝ), ∃ (x : ℝ), M < |f x| := by
  classical
  let f : ℝ → ℝ := fun x => x * Real.sin (Real.pi * x)
  refine ⟨f, ?_, ⟨0, ?_⟩, ?_⟩
  · fun_prop
  · intro n
    simp [f, mul_comm Real.pi, Real.sin_int_mul_pi]
  · intro M
    obtain ⟨n, hn⟩ := exists_nat_gt (max M 0)
    refine ⟨2 * (n : ℝ) + 1/2, ?_⟩
    have hs : Real.sin (Real.pi * (2 * (n : ℝ) + 1/2)) = 1 := by
      rw [show Real.pi * (2 * (n : ℝ) + 1/2) = Real.pi / 2 + (n : ℝ) * (2 * Real.pi) by ring]
      rw [Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two]
    have hnonneg : 0 ≤ 2 * (n : ℝ) + 1/2 := by positivity
    dsimp [f]
    rw [hs, mul_one, abs_of_nonneg hnonneg]
    have hM : M < (n : ℝ) := (le_max_left M 0).trans_lt hn
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith

#print axioms GroundTruth.basic_analysis_3_3_3_3_13_certificate


theorem GroundTruth.basic_analysis_5_1_5_1_10_certificate :
∃ (f : ℝ → ℝ),
  (∃ (M : ℝ), ∀ x ∈ Set.Icc (0 : ℝ) (1 : ℝ), |f x| ≤ M) ∧
    ¬have L := fun (n : ℕ) => ∑ i ∈ Finset.range n, sInf (f '' Set.Icc (↑i / ↑n) ((↑i + (1 : ℝ)) / ↑n)) / ↑n;
      MonotoneOn L (Set.Ici (1 : ℕ)) ∨ AntitoneOn L (Set.Ici (1 : ℕ)) := by
  classical
  let f : ℝ → ℝ := fun x => if x = 1/2 then 0 else 1
  have hnonneg : ∀ x, 0 ≤ f x := by intro x; dsimp [f]; split_ifs <;> norm_num
  have hzero (a b : ℝ) (ha : a ≤ 1/2) (hb : 1/2 ≤ b) : sInf (f '' Set.Icc a b) = 0 := by
    have hm : (0 : ℝ) ∈ f '' Set.Icc a b := ⟨1/2, ⟨ha,hb⟩, by simp [f]⟩
    have hl : ∀ y ∈ f '' Set.Icc a b, 0 ≤ y := by rintro y ⟨x,hx,rfl⟩; exact hnonneg x
    exact le_antisymm (csInf_le ⟨0,hl⟩ hm) (le_csInf ⟨0,hm⟩ hl)
  have hone (a b : ℝ) (hab : a ≤ b) (hmiss : b < 1/2 ∨ 1/2 < a) : sInf (f '' Set.Icc a b) = 1 := by
    have hf : ∀ x ∈ Set.Icc a b, f x = 1 := by
      intro x hx
      have hn : x ≠ 1/2 := by rcases hmiss with h | h <;> intro he <;> rw [he] at hx <;> linarith [hx.1,hx.2]
      simp only [f, if_neg hn]
    have hs : f '' Set.Icc a b = {1} := by
      ext y
      constructor
      · rintro ⟨x,hx,rfl⟩; exact hf x hx
      · rintro rfl
        exact ⟨a,⟨le_rfl,hab⟩,hf a ⟨le_rfl,hab⟩⟩
    rw [hs]
    simp
  let L : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, sInf (f '' Set.Icc ((i:ℝ)/(n:ℝ)) (((i:ℝ)+1)/(n:ℝ))) / (n:ℝ)
  have h01 := hzero 0 1 (by norm_num) (by norm_num)
  have h03 := hone 0 (1/3) (by norm_num) (Or.inl (by norm_num))
  have h13 := hzero (1/3) (2/3) (by norm_num) (by norm_num)
  have h23 := hone (2/3) 1 (by norm_num) (Or.inr (by norm_num))
  have h04 := hone 0 (1/4) (by norm_num) (Or.inl (by norm_num))
  have h14 := hzero (1/4) (1/2) (by norm_num) (by norm_num)
  have h24 := hzero (1/2) (3/4) (by norm_num) (by norm_num)
  have h34 := hone (3/4) 1 (by norm_num) (Or.inr (by norm_num))
  have hL1 : L 1 = 0 := by norm_num [L, Finset.sum_range_succ,h01]
  have hL3 : L 3 = 2/3 := by norm_num [L, Finset.sum_range_succ,h03,h13,h23]
  have hL4 : L 4 = 1/2 := by norm_num [L, Finset.sum_range_succ,h04,h14,h24,h34]
  refine ⟨f, ⟨1,?_⟩, ?_⟩
  · intro x hx; dsimp [f]; split_ifs <;> norm_num
  · change ¬ (MonotoneOn L (Set.Ici (1:ℕ)) ∨ AntitoneOn L (Set.Ici (1:ℕ)))
    rintro (hm | ha)
    · have he := hm (show 3 ∈ Set.Ici (1:ℕ) by norm_num) (show 4 ∈ Set.Ici (1:ℕ) by norm_num) (by norm_num : (3:ℕ) ≤ 4)
      rw [hL3,hL4] at he
      norm_num at he
    · have he := ha (show 1 ∈ Set.Ici (1:ℕ) by norm_num) (show 3 ∈ Set.Ici (1:ℕ) by norm_num) (by norm_num : (1:ℕ) ≤ 3)
      rw [hL1,hL3] at he
      norm_num at he

#print axioms GroundTruth.basic_analysis_5_1_5_1_10_certificate


theorem GroundTruth.basic_analysis_6_1_6_1_10_a_certificate :
∃ f : ℕ → ℝ → ℝ, ∃ x : ℕ → ℝ,
  (∀ n, 1 ≤ n → x n ∈ Set.Icc (0 : ℝ) 1 ∧ f n (x n) = 1) ∧
  (∀ m n, 1 ≤ m → 1 ≤ n → x m = x n → m = n) ∧
  (∀ y ∈ Set.Icc (0 : ℝ) 1, Tendsto (fun n => f n y) atTop (nhds 0)) := by
  classical
  let x : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let f : ℕ → ℝ → ℝ := fun n y => if y = x n then 1 else 0
  have hxinj : Function.Injective x := by
    intro m n hmn
    dsimp [x] at hmn
    have hm : (m : ℝ) + 1 ≠ 0 := by
      have hm0 : 0 < (m : ℝ) + 1 := by
        exact_mod_cast Nat.zero_lt_succ m
      exact ne_of_gt hm0
    have hn : (n : ℝ) + 1 ≠ 0 := by
      have hn0 : 0 < (n : ℝ) + 1 := by
        exact_mod_cast Nat.zero_lt_succ n
      exact ne_of_gt hn0
    rw [div_eq_div_iff hm hn] at hmn
    have hcast : (m : ℝ) = (n : ℝ) := by linarith
    exact_mod_cast hcast
  refine ⟨f, x, ?_, ?_, ?_⟩
  · intro n hn
    constructor
    · constructor
      · dsimp [x]
        have hd : 0 ≤ (n : ℝ) + 1 := by
          have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith
        exact div_nonneg (by norm_num) hd
      · dsimp [x]
        have hd : 0 < (n : ℝ) + 1 := by
          exact_mod_cast Nat.zero_lt_succ n
        apply (div_le_one hd).2
        have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
    · simp [f]
  · intro m n hm hn h
    exact hxinj h
  · intro y hy
    by_cases h : ∃ k, y = x k
    · obtain ⟨k, hk⟩ := h
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (k + 1)] with n hn
      have hne : y ≠ x n := by
        intro heq
        have hxn : x k = x n := hk.symm.trans heq
        have hkn : k = n := hxinj hxn
        omega
      simp [f, hne]
    · apply tendsto_const_nhds.congr'
      filter_upwards [] with n
      have hne : y ≠ x n := by
        intro heq
        exact h ⟨n, heq⟩
      simp [f, hne]

#print axioms GroundTruth.basic_analysis_6_1_6_1_10_a_certificate


theorem GroundTruth.basic_analysis_6_1_6_1_10_b_certificate :
∀ (f : ℕ → ℝ → ℝ) (x : ℕ → ℝ),
  (∀ (n : ℕ), (1 : ℕ) ≤ n → x n ∈ Set.Icc (0 : ℝ) (1 : ℝ) ∧ f n (x n) = (1 : ℝ)) →
    (∀ (m n : ℕ), (1 : ℕ) ≤ m → (1 : ℕ) ≤ n → x m = x n → m = n) →
      ∃ (ε : ℝ), (0 : ℝ) < ε ∧ ∀ (N : ℕ), ∃ (n : ℕ), N ≤ n ∧ ∃ y ∈ Set.Icc (0 : ℝ) (1 : ℝ), ε ≤ |f n y| := by
  intro f x hf hx
  refine ⟨(1 : ℝ) / 2, by norm_num, ?_⟩
  intro N
  let n : ℕ := max N 1
  have hnN : N ≤ n := le_max_left N 1
  have hn1 : 1 ≤ n := le_max_right N 1
  refine ⟨n, hnN, x n, (hf n hn1).1, ?_⟩
  rw [(hf n hn1).2]
  norm_num

#print axioms GroundTruth.basic_analysis_6_1_6_1_10_b_certificate


theorem GroundTruth.basic_analysis_6_2_6_2_6_certificate :
∃ (f : ℕ → ↑(Set.Icc (0 : ℝ) (1 : ℝ)) → ℝ) (g : ↑(Set.Icc (0 : ℝ) (1 : ℝ)) → ℝ),
  (∀ (n : ℕ), (1 : ℕ) ≤ n → ∀ (x : ↑(Set.Icc (0 : ℝ) (1 : ℝ))), ¬ContinuousAt (f n) x) ∧
    (∀ (ε : ℝ), (0 : ℝ) < ε → ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → ∀ (x : ↑(Set.Icc (0 : ℝ) (1 : ℝ))), |f n x - g x| < ε) ∧
      ∃ (x : ↑(Set.Icc (0 : ℝ) (1 : ℝ))), ContinuousAt g x := by
  classical
  let I := Set.Icc (0:ℝ) 1
  letI : Nontrivial I := ⟨⟨⟨0,by norm_num [I]⟩,⟨1,by norm_num [I]⟩,by intro he; have hh := congrArg Subtype.val he; norm_num at hh⟩⟩
  let S : Set I := {x | ∃ q : ℚ, (q:ℝ) = x.val}
  have hS : Dense S := by
    apply dense_iff_exists_between.mpr
    intro a b hab
    obtain ⟨q,haq,hqb⟩ := exists_rat_btwn (show a.val < b.val from hab)
    refine ⟨⟨(q:ℝ),⟨le_trans a.2.1 haq.le,le_trans hqb.le b.2.2⟩⟩,⟨q,rfl⟩,haq,hqb⟩
  have hSc : Dense Sᶜ := by
    apply dense_iff_exists_between.mpr
    intro a b hab
    obtain ⟨r,hirr,har,hrb⟩ := exists_irrational_btwn (show a.val < b.val from hab)
    refine ⟨⟨r,⟨le_trans a.2.1 har.le,le_trans hrb.le b.2.2⟩⟩,?_,har,hrb⟩
    rintro ⟨q,hq⟩
    exact hirr ⟨q,hq⟩
  let f : ℕ → I → ℝ := fun n x => if x ∈ S then (1/2:ℝ)^n else 0
  have hg : Tendsto (fun n : ℕ => (1/2:ℝ)^n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  refine ⟨f, (fun _ => 0), ?_, ?_, ?_⟩
  · intro n hn x hc
    have hp : 0 < (1/2:ℝ)^n := by positivity
    obtain ⟨δ,hδ,hcont⟩ := Metric.continuousAt_iff.mp hc ((1/2:ℝ)^n/2) (by positivity)
    by_cases hx : x ∈ S
    · obtain ⟨y,hy,hxy⟩ := hSc.exists_dist_lt x hδ
      have hy' : y ∉ S := hy
      have he := hcont (show dist y x < δ from by simpa only [dist_comm] using hxy)
      simp only [f,if_neg hy',if_pos hx,Real.dist_eq,zero_sub,abs_neg,abs_of_pos hp] at he
      linarith
    · obtain ⟨y,hy,hxy⟩ := hS.exists_dist_lt x hδ
      have he := hcont (show dist y x < δ from by simpa only [dist_comm] using hxy)
      simp only [f,if_pos hy,if_neg hx,Real.dist_eq,sub_zero,abs_of_pos hp] at he
      linarith
  · intro ε hε
    have he := (Metric.tendsto_nhds.mp hg) ε hε
    obtain ⟨N,hN⟩ := eventually_atTop.mp he
    refine ⟨N,?_⟩
    intro n hn x
    have hb : (1/2:ℝ)^n < ε := by
      have he := hN n hn
      simpa only [Real.dist_eq,sub_zero,abs_of_nonneg (by positivity : 0 ≤ (1/2:ℝ)^n)] using he
    dsimp [f]
    split_ifs
    · simpa only [sub_zero,abs_of_nonneg (by positivity : 0 ≤ (1/2:ℝ)^n)] using hb
    · simpa using hε
  · exact ⟨⟨0,by norm_num⟩,continuousAt_const⟩

#print axioms GroundTruth.basic_analysis_6_2_6_2_6_certificate


theorem GroundTruth.basic_analysis_7_2_7_2_11_a_certificate :
∀ (X : Type) [MetricSpace X] (A : Set X), IsConnected A → IsConnected (closure A) := by
  intro X _ A hA
  exact hA.closure

#print axioms GroundTruth.basic_analysis_7_2_7_2_11_a_certificate


theorem GroundTruth.basic_analysis_7_2_7_2_11_b_certificate :
¬ (
∀ (X : Type) [MetricSpace X] (A : Set X), IsConnected A → IsConnected (interior A)
) := by
  intro h
  have hc := h ℝ ({0} : Set ℝ) isConnected_singleton
  have hn := hc.nonempty
  simpa using hn

#print axioms GroundTruth.basic_analysis_7_2_7_2_11_b_certificate


theorem GroundTruth.basic_analysis_7_2_7_2_13_b_certificate :
¬ (
∀ (X : Type) [MetricSpace X] (x : X) (δ : ℝ), 0 < δ →
  closure (Metric.ball x δ) = Metric.closedBall x δ
) := by
  intro h
  have hb : Metric.ball (0 : ℤ) 1 = ({0} : Set ℤ) := by
    ext z
    simp only [Metric.mem_ball, Set.mem_singleton_iff]
    rw [Int.dist_eq]
    simp only [Int.cast_zero, sub_zero]
    constructor
    · intro hz
      have hz' := (abs_lt.mp hz)
      have hlo : (-1 : ℤ) < z := by exact_mod_cast hz'.1
      have hhi : z < (1 : ℤ) := by exact_mod_cast hz'.2
      omega
    · rintro rfl
      norm_num
  have heq := h ℤ (0 : ℤ) 1 (by norm_num)
  have heq' : closure ({0} : Set ℤ) = Metric.closedBall (0 : ℤ) 1 := by
    rw [← hb]
    exact heq
  have hmem : (1 : ℤ) ∈ Metric.closedBall (0 : ℤ) 1 := by
    simp [Metric.mem_closedBall]
  have hmem' : (1 : ℤ) ∈ closure ({0} : Set ℤ) := by
    rw [heq']
    exact hmem
  rw [isClosed_singleton.closure_eq] at hmem'
  norm_num at hmem'

#print axioms GroundTruth.basic_analysis_7_2_7_2_13_b_certificate


theorem GroundTruth.basic_analysis_7_3_7_3_8_certificate :
¬ (
∀ (X : Type) [MetricSpace X] (U : ℕ → Set X) (p : X) (x : ℕ → X),
  (∀ n : ℕ, 1 ≤ n → IsOpen (U n)) →
  (∀ n : ℕ, 1 ≤ n → U (n+1) ⊆ U n) →
  (⋂ n : ℕ+, U n.val) = {p} →
  (∀ n : ℕ, 1 ≤ n → x n ∈ U n) → Tendsto x atTop (nhds p)
) := by
  intro h
  let U : ℕ → Set ℕ := fun n => ({0} : Set ℕ) ∪ Set.Ici n
  let x : ℕ → ℕ := fun n => n
  have hopen : ∀ n : ℕ, 1 ≤ n → IsOpen (U n) := by
    intro n hn
    exact isOpen_discrete _
  have hdec : ∀ n : ℕ, 1 ≤ n → U (n + 1) ⊆ U n := by
    intro n hn k hk
    change k = 0 ∨ n + 1 ≤ k at hk
    change k = 0 ∨ n ≤ k
    rcases hk with hk | hk
    · exact Or.inl hk
    · exact Or.inr (by omega)
  have hinter : (⋂ n : ℕ+, U n.val) = ({0} : Set ℕ) := by
    ext k
    simp only [Set.mem_iInter, Set.mem_singleton_iff]
    constructor
    · intro hk
      change ∀ n : ℕ+, k = 0 ∨ n.val ≤ k at hk
      by_contra hk0
      have ht := hk ⟨k + 1, Nat.succ_pos k⟩
      rcases ht with ht | ht
      · exact hk0 ht
      · change k + 1 ≤ k at ht
        omega
    · intro hk n
      change k = 0 ∨ n.val ≤ k
      exact Or.inl hk
  have hx : ∀ n : ℕ, 1 ≤ n → x n ∈ U n := by
    intro n hn
    change n = 0 ∨ n ≤ n
    exact Or.inr le_rfl
  have ht := h ℕ U 0 x hopen hdec hinter hx
  have hnhds : ({0} : Set ℕ) ∈ nhds 0 :=
    IsOpen.mem_nhds (isOpen_discrete _) (by simp)
  have hev : ∀ᶠ n : ℕ in atTop, x n ∈ ({0} : Set ℕ) := ht hnhds
  rw [eventually_atTop] at hev
  rcases hev with ⟨N, hN⟩
  have hbad := hN (N + 1) (by omega)
  simp [x] at hbad

#print axioms GroundTruth.basic_analysis_7_3_7_3_8_certificate


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


theorem GroundTruth.linear_algebra_1C_19_certificate :
¬ (
∀ (F : Type) [RCLike F] (V : Type) [AddCommGroup V] [Module F V],
  ∀ V₁ V₂ U : Submodule F V, V₁ ⊔ U = V₂ ⊔ U → V₁ = V₂
) := by
  push_neg
  refine ⟨ℝ, inferInstance, ℝ, inferInstance, inferInstance, ⊥, ⊤, ⊤, ?_, ?_⟩ <;> simp

#print axioms GroundTruth.linear_algebra_1C_19_certificate


theorem GroundTruth.linear_algebra_1C_23_certificate :
¬ (
∀ (F : Type) [RCLike F] (V : Type) [AddCommGroup V] [Module F V],
  ∀ V₁ V₂ U : Submodule F V, IsCompl V₁ U → IsCompl V₂ U → V₁ = V₂
) := by
  classical
  intro h
  let U : Submodule ℝ (ℝ × ℝ) := LinearMap.ker (LinearMap.snd ℝ ℝ ℝ)
  let V₁ : Submodule ℝ (ℝ × ℝ) := LinearMap.ker (LinearMap.fst ℝ ℝ ℝ)
  let V₂ : Submodule ℝ (ℝ × ℝ) := LinearMap.ker (LinearMap.fst ℝ ℝ ℝ - LinearMap.snd ℝ ℝ ℝ)
  have h₁ : IsCompl V₁ U := by
    constructor
    · apply Submodule.disjoint_def.mpr
      intro x hx hy
      have hx' : x.1 = 0 := hx
      have hy' : x.2 = 0 := hy
      exact Prod.ext hx' hy'
    · rw [codisjoint_iff]
      apply top_unique
      intro x hx
      exact Submodule.mem_sup.mpr ⟨(0,x.2), by simp [V₁, LinearMap.mem_ker], (x.1,0), by simp [U, LinearMap.mem_ker], by ext <;> simp⟩
  have h₂ : IsCompl V₂ U := by
    constructor
    · apply Submodule.disjoint_def.mpr
      intro x hx hy
      have hx' : x.1 - x.2 = 0 := hx
      have hy' : x.2 = 0 := hy
      apply Prod.ext
      · dsimp; linarith
      · exact hy'
    · rw [codisjoint_iff]
      apply top_unique
      intro x hx
      exact Submodule.mem_sup.mpr ⟨(x.2,x.2), by simp [V₂, LinearMap.mem_ker], (x.1-x.2,0), by simp [U, LinearMap.mem_ker], by ext <;> simp⟩
  have heq := h ℝ (ℝ × ℝ) V₁ V₂ U h₁ h₂
  have hdiag : (1,1) ∈ V₂ := by simp [V₂, LinearMap.mem_ker]
  rw [← heq] at hdiag
  norm_num [V₁, LinearMap.mem_ker] at hdiag

#print axioms GroundTruth.linear_algebra_1C_23_certificate


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


theorem GroundTruth.linear_algebra_2A_10_certificate :
∀ (F : Type) [RCLike F] (V : Type) [AddCommGroup V] [Module F V],
  ∀ m : ℕ, 1 ≤ m → ∀ (v : Fin m → V) (a : F),
  LinearIndependent F v → a ≠ 0 → LinearIndependent F (fun i => a • v i) := by
  classical
  intro F _ V _ _ m hm v a hv ha
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro g hg i
  have hz : ∑ j, (g j * a) • v j = 0 := by
    simpa [smul_smul] using hg
  have hi : g i * a = 0 := hv (fun j => g j * a) hz i
  exact (mul_eq_zero.mp hi).resolve_right ha

#print axioms GroundTruth.linear_algebra_2A_10_certificate


theorem GroundTruth.linear_algebra_2A_11_certificate :
¬ (
∀ (F : Type) [RCLike F] (V : Type) [AddCommGroup V] [Module F V],
  ∀ m : ℕ, 1 ≤ m → ∀ v w : Fin m → V,
  LinearIndependent F v → LinearIndependent F w → LinearIndependent F (fun i => v i+w i)
) := by
  classical
  intro h
  have hv : LinearIndependent ℝ (fun _ : Fin 1 => (1 : ℝ)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    fin_cases i
    simpa using hg
  have hw : LinearIndependent ℝ (fun _ : Fin 1 => (-1 : ℝ)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    fin_cases i
    simpa using hg
  have ht := h ℝ ℝ 1 (by omega)
    (fun _ : Fin 1 => (1 : ℝ))
    (fun _ : Fin 1 => (-1 : ℝ)) hv hw
  have hn := ht.ne_zero (0 : Fin 1)
  norm_num at hn

#print axioms GroundTruth.linear_algebra_2A_11_certificate


theorem GroundTruth.linear_algebra_2B_6_certificate :
¬ (
∀ (F : Type) [RCLike F] (p : Fin 4 → Polynomial F),
  (∀ i, (p i).natDegree ≤ 3) → (∀ i, (p i).natDegree ≠ 2) →
  ¬ (LinearIndependent F p ∧ Submodule.span F (Set.range p) = Polynomial.degreeLE F 3)
) := by
  classical
  intro h
  let v : Fin 4 → Polynomial ℝ := fun i => Polynomial.X ^ i.val
  let p : Fin 4 → Polynomial ℝ := Function.update v 2 (v 2 + v 3)
  have hv : LinearIndependent ℝ v := by
    have hh := (Polynomial.basisMonomials ℝ).linearIndependent.comp (fun i : Fin 4 => i.val) Fin.val_injective
    simpa only [Polynomial.coe_basisMonomials, Function.comp_def, ← Polynomial.X_pow_eq_monomial] using hh
  let c : Fin 4 → ℝ := fun i => if i = 2 then 1 else 0
  have hc : c 3 = 0 := by simp [c]
  have hp : LinearIndependent ℝ p := by
    have hh := (linearIndependent_add_smul_iff (v := v) hc).mpr hv
    convert hh using 1
    funext i
    by_cases hi : i = 2 <;> simp [p,c,hi]
  have hspanv : Submodule.span ℝ (Set.range v) = Polynomial.degreeLE ℝ 3 := by
    change Submodule.span ℝ (Set.range v) = Polynomial.degreeLE ℝ ((3:ℕ):WithBot ℕ)
    rw [Polynomial.degreeLE_eq_span_X_pow]
    congr 1
    ext q
    simp only [Set.mem_range, Finset.mem_coe, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨i.val,i.isLt,rfl⟩
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,hi⟩,rfl⟩
  have hspanp : Submodule.span ℝ (Set.range p) = Polynomial.degreeLE ℝ 3 := by
    have hh := Submodule.span_range_update_add_smul (R := ℝ) (i := (3:Fin 4)) (j := (2:Fin 4)) (by norm_num [Fin.ext_iff] : (3:Fin 4) ≠ 2) v 1
    simpa only [one_smul, hspanv] using hh
  have hdeg2 : (p 2).natDegree = 3 := by
    change (Polynomial.X^2+Polynomial.X^3 : Polynomial ℝ).natDegree = 3
    compute_degree <;> norm_num
  have hle : ∀ i, (p i).natDegree ≤ 3 := by
    intro i
    fin_cases i <;> first | (change (p 2).natDegree ≤ 3; rw [hdeg2]) | (norm_num [p,v,Function.update,Fin.ext_iff])
  have hne : ∀ i, (p i).natDegree ≠ 2 := by
    intro i
    fin_cases i <;> first | (change (p 2).natDegree ≠ 2; rw [hdeg2]; norm_num) | (norm_num [p,v,Function.update,Fin.ext_iff])
  exact h ℝ p hle hne ⟨hp,hspanp⟩

#print axioms GroundTruth.linear_algebra_2B_6_certificate


theorem GroundTruth.linear_algebra_2B_8_certificate :
¬ (
∀ (F : Type) [RCLike F] (V : Type) [AddCommGroup V] [Module F V],
  ∀ (v : Fin 4 → V) (U : Submodule F V),
  LinearIndependent F v → Submodule.span F (Set.range v) = ⊤ →
  v 0 ∈ U → v 1 ∈ U → v 2 ∉ U → v 3 ∉ U →
  LinearIndependent F (fun i : Fin 2 => v (Fin.castLE (by decide) i)) ∧
  Submodule.span F (Set.range (fun i : Fin 2 => v (Fin.castLE (by decide) i))) = U
) := by
  classical
  intro h
  let v : Fin 4 → (Fin 4 → ℝ) := Pi.basisFun ℝ (Fin 4)
  let ℓ : (Fin 4 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 2 - LinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 3
  let U : Submodule ℝ (Fin 4 → ℝ) := LinearMap.ker ℓ
  have hv : LinearIndependent ℝ v := by
    simpa only [v] using (Pi.basisFun ℝ (Fin 4)).linearIndependent
  have hs : Submodule.span ℝ (Set.range v) = ⊤ := by
    simpa only [v] using (Pi.basisFun ℝ (Fin 4)).span_eq
  have h0 : v 0 ∈ U := by simp [U, ℓ, v, Pi.basisFun_apply, LinearMap.mem_ker]
  have h1 : v 1 ∈ U := by simp [U, ℓ, v, Pi.basisFun_apply, LinearMap.mem_ker]
  have h2 : v 2 ∉ U := by simp [U, ℓ, v, Pi.basisFun_apply, LinearMap.mem_ker]
  have h3 : v 3 ∉ U := by simp [U, ℓ, v, Pi.basisFun_apply, LinearMap.mem_ker]
  have heq := (h ℝ (Fin 4 → ℝ) v U hv hs h0 h1 h2 h3).2
  have hle : Submodule.span ℝ (Set.range (fun i : Fin 2 => v (Fin.castLE (by decide) i))) ≤
      LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 2) := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    fin_cases i <;> simp [v, Pi.basisFun_apply, LinearMap.mem_ker]
  have hw : v 2 + v 3 ∈ U := by simp [U, ℓ, v, Pi.basisFun_apply, LinearMap.mem_ker]
  rw [← heq] at hw
  have hz := hle hw
  norm_num [v, Pi.basisFun_apply, LinearMap.mem_ker, Pi.single_apply, Fin.ext_iff] at hz

#print axioms GroundTruth.linear_algebra_2B_8_certificate


theorem GroundTruth.linear_algebra_2C_19_certificate :
¬ (
∀ (F : Type) [RCLike F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V],
  ∀ U W Z : Submodule F V,
  (Module.finrank F ↥(U ⊔ W ⊔ Z : Submodule F V) : ℤ) = (Module.finrank F ↥(U : Submodule F V) : ℤ) + (Module.finrank F ↥(W : Submodule F V) : ℤ) + (Module.finrank F ↥(Z : Submodule F V) : ℤ) - (Module.finrank F ↥(U ⊓ W : Submodule F V) : ℤ) - (Module.finrank F ↥(U ⊓ Z : Submodule F V) : ℤ) - (Module.finrank F ↥(W ⊓ Z : Submodule F V) : ℤ) + (Module.finrank F ↥(U ⊓ W ⊓ Z : Submodule F V) : ℤ)
) := by
  classical
  intro h
  let U : Submodule ℝ ℂ := Complex.imLm.ker
  let W : Submodule ℝ ℂ := Complex.reLm.ker
  let Z : Submodule ℝ ℂ := (Complex.reLm-Complex.imLm).ker
  have hdim (L : ℂ →ₗ[ℝ] ℝ) (hL : Function.Surjective L) : Module.finrank ℝ L.ker = 1 := by
    have he := L.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hL] at he
    simp only [finrank_top, CommSemiring.finrank_self, Complex.finrank_real_complex] at he
    omega
  have hU : Module.finrank ℝ U = 1 := hdim _ (fun r => ⟨r*Complex.I, by simp⟩)
  have hW : Module.finrank ℝ W = 1 := hdim _ (fun r => ⟨r, by simp⟩)
  have hZ : Module.finrank ℝ Z = 1 := hdim _ (fun r => ⟨r, by simp⟩)
  have hUW : U ⊓ W = ⊥ := by
    apply bot_unique
    intro z hz
    have hzi : z.im = 0 := hz.1
    have hzr : z.re = 0 := hz.2
    change z = 0
    exact Complex.ext hzr hzi
  have hUZ : U ⊓ Z = ⊥ := by
    apply bot_unique
    intro z hz
    have hzi : z.im = 0 := hz.1
    have he : z.re-z.im = 0 := hz.2
    change z = 0
    apply Complex.ext
    · dsimp; linarith
    · exact hzi
  have hWZ : W ⊓ Z = ⊥ := by
    apply bot_unique
    intro z hz
    have hzr : z.re = 0 := hz.1
    have he : z.re-z.im = 0 := hz.2
    change z = 0
    apply Complex.ext
    · exact hzr
    · dsimp; linarith
  have hsup : U ⊔ W = ⊤ := by
    apply top_unique
    intro z hz
    apply Submodule.mem_sup.mpr
    refine ⟨(z.re : ℂ), by simp [U, LinearMap.mem_ker], z.im*Complex.I, by simp [W, LinearMap.mem_ker], ?_⟩
    apply Complex.ext <;> simp
  have htriple : U ⊓ W ⊓ Z = ⊥ := by rw [hUW, bot_inf_eq]
  have he := h ℝ ℂ U W Z
  rw [hsup, top_sup_eq, hUW, hUZ, hWZ, bot_inf_eq, hU, hW, hZ] at he
  norm_num [Complex.finrank_real_complex] at he

#print axioms GroundTruth.linear_algebra_2C_19_certificate


theorem GroundTruth.linear_algebra_3A_10_certificate :
¬ (
∀ q : Polynomial ℝ, ∃ T : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ, ∀ p, T p = q.comp p
) := by
  intro H
  obtain ⟨T, hT⟩ := H (1 : Polynomial ℝ)
  have h := hT (0 : Polynomial ℝ)
  simpa using h

#print axioms GroundTruth.linear_algebra_3A_10_certificate


theorem GroundTruth.linear_algebra_3D_14_certificate :
∀ (F : Type) [RCLike F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V],
  ∀ R S T : V →ₗ[F] V, Function.Surjective (R.comp (S.comp T)) → Function.Injective S := by
  intro F _ V _ _ _ R S T hsurj
  have hcomp : Function.Injective (R.comp (S.comp T)) :=
    ((R.comp (S.comp T)).injective_iff_surjective_of_finrank_eq_finrank rfl).2 hsurj
  have hTinj : Function.Injective T := by
    intro x y hxy
    apply hcomp
    simp only [LinearMap.comp_apply]
    rw [hxy]
  have hTsurj : Function.Surjective T :=
    (T.injective_iff_surjective_of_finrank_eq_finrank rfl).1 hTinj
  intro x y hxy
  obtain ⟨x', rfl⟩ := hTsurj x
  obtain ⟨y', rfl⟩ := hTsurj y
  have h' : x' = y' := by
    apply hcomp
    simp only [LinearMap.comp_apply]
    rw [hxy]
  exact congrArg T h'

#print axioms GroundTruth.linear_algebra_3D_14_certificate


theorem GroundTruth.linear_algebra_5A_4_certificate :
∀ (F : Type) [RCLike F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V],
  ∀ U : Submodule F V,
  (∀ T : V →ₗ[F] V, ∀ u ∈ U, T u ∈ U) → U = ⊥ ∨ U = ⊤ := by
  classical
  intro F _ V _ _ _ U hU
  by_cases hz : U = ⊥
  · exact Or.inl hz
  · right
    apply top_unique
    intro w hw
    obtain ⟨u, hu, hune⟩ := U.ne_bot_iff.mp hz
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one F hune
    have h := hU (φ.smulRight w) u hu
    simpa [hφ] using h

#print axioms GroundTruth.linear_algebra_5A_4_certificate


theorem GroundTruth.linear_algebra_5C_1_certificate :
¬ (
∀ (F : Type) [RCLike F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V],
  ∀ T : V →ₗ[F] V, (∃ n : ℕ, ∃ b : Module.Basis (Fin n) F V, ∀ i j : Fin n, j < i → LinearMap.toMatrix b b (T.comp T) i j = 0) → (∃ n : ℕ, ∃ b : Module.Basis (Fin n) F V, ∀ i j : Fin n, j < i → LinearMap.toMatrix b b T i j = 0)
) := by
  intro h
  let T : ℂ →ₗ[ℝ] ℂ :=
    Complex.reLm.smulRight Complex.I - Complex.imLm.smulRight (1 : ℂ)
  have hT_sq : T.comp T = -(LinearMap.id : ℂ →ₗ[ℝ] ℂ) := by
    ext z
    apply Complex.ext <;> simp [T]
  have htri_sq :
      ∃ n : ℕ, ∃ b : Module.Basis (Fin n) ℝ ℂ,
        ∀ i j : Fin n, j < i →
          LinearMap.toMatrix b b (T.comp T) i j = 0 := by
    refine ⟨2, Complex.orthonormalBasisOneI.toBasis, ?_⟩
    intro i j hij
    rw [hT_sq]
    simp only [map_neg, LinearMap.toMatrix_id, Matrix.neg_apply, Matrix.one_apply, if_neg (ne_of_gt hij), neg_zero]
  obtain ⟨n, b, hb⟩ := h ℝ ℂ T htri_sq
  have hn : n = 2 := by
    have he := Module.finrank_eq_card_basis b
    simpa only [Complex.finrank_real_complex,Fintype.card_fin] using he.symm
  subst n
  have h10 := hb (1 : Fin 2) (0 : Fin 2) (by decide)
  rw [LinearMap.toMatrix_apply] at h10
  let a : ℝ := (b.repr (T (b (0 : Fin 2)))) (0 : Fin 2)
  have heig : T (b (0 : Fin 2)) = a • b (0 : Fin 2) := by
    apply b.repr.injective
    ext i
    simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
    fin_cases i
    · norm_num [a,Fin.ext_iff]
    · norm_num [a,h10,Fin.ext_iff]
  have hcalc : T (T (b (0 : Fin 2))) = (a * a) • b (0 : Fin 2) := by
    rw [heig, map_smul, heig, smul_smul]
  have hneg : T (T (b (0 : Fin 2))) = -b (0 : Fin 2) := by
    have hz := DFunLike.congr_fun hT_sq (b (0 : Fin 2))
    simpa using hz
  have hz : (a * a + 1) • b (0 : Fin 2) = 0 := by
    rw [add_smul, one_smul, ← hcalc, hneg]
    simp
  have ha : a * a + 1 = 0 := by
    rcases smul_eq_zero.mp hz with ha | hv
    · exact ha
    · exact False.elim (b.ne_zero (0 : Fin 2) hv)
  nlinarith [sq_nonneg a]

#print axioms GroundTruth.linear_algebra_5C_1_certificate


theorem GroundTruth.linear_algebra_5D_19_certificate :
¬ (
∀ (F : Type) [RCLike F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V],
  ∀ (T : V →ₗ[F] V) (U : Submodule F V),
  ∀ h : ∀ u ∈ U, T u ∈ U,
  (∃ n : ℕ, ∃ b : Module.Basis (Fin n) F U, ∀ i j : Fin n, i ≠ j → LinearMap.toMatrix b b (T.restrict h) i j = 0) →
  (∃ n : ℕ, ∃ b : Module.Basis (Fin n) F (V ⧸ U), ∀ i j : Fin n, i ≠ j → LinearMap.toMatrix b b (U.mapQ U T h) i j = 0) → (∃ n : ℕ, ∃ b : Module.Basis (Fin n) F V, ∀ i j : Fin n, i ≠ j → LinearMap.toMatrix b b T i j = 0)
) := by
  intro H
  let T : ℂ →ₗ[ℝ] ℂ := Complex.imLm.smulRight (1 : ℂ)
  let U : Submodule ℝ ℂ := LinearMap.ker Complex.imLm
  have hTU : ∀ z : ℂ, T z ∈ U := by
    intro z
    change Complex.imLm (T z) = 0
    simp [T]
  have h : ∀ u ∈ U, T u ∈ U := by
    intro u hu
    exact hTU u
  have hres : T.restrict h = 0 := by
    ext u
    change T (u : ℂ) = 0
    have hu : Complex.imLm (u : ℂ) = 0 := u.property
    simp [T, hu]
  have hquot : U.mapQ U T h = 0 := by
    ext z
    change Submodule.Quotient.mk (T z) = 0
    exact (Submodule.Quotient.mk_eq_zero U).mpr (hTU z)
  have hdres : ∃ n : ℕ, ∃ b : Module.Basis (Fin n) ℝ U,
      ∀ i j : Fin n, i ≠ j →
        LinearMap.toMatrix b b (T.restrict h) i j = 0 := by
    let b := Module.finBasis ℝ U
    refine ⟨Module.finrank ℝ U, b, ?_⟩
    intro i j hij
    simp [hres]
  have hdquot : ∃ n : ℕ, ∃ b : Module.Basis (Fin n) ℝ (ℂ ⧸ U),
      ∀ i j : Fin n, i ≠ j →
        LinearMap.toMatrix b b (U.mapQ U T h) i j = 0 := by
    let b := Module.finBasis ℝ (ℂ ⧸ U)
    refine ⟨Module.finrank ℝ (ℂ ⧸ U), b, ?_⟩
    intro i j hij
    simp [hquot]
  obtain ⟨n, b, hd⟩ := H ℝ ℂ T U h hdres hdquot
  let M : Matrix (Fin n) (Fin n) ℝ := LinearMap.toMatrix b b T
  have heigen : ∀ j : Fin n, T (b j) = M j j • b j := by
    intro j
    apply b.repr.injective
    ext i
    have he : (b.repr (T (b j))) i = M i j := by dsimp [M]; rw [LinearMap.toMatrix_apply]
    rw [he]
    simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst i
      simp
    · have hh : M i j = 0 := hd i j hij
      rw [hh]
      simp [hij,Ne.symm hij]
  have hnil : ∀ z : ℂ, T (T z) = 0 := by
    intro z
    simp [T]
  have hdiagzero : ∀ j : Fin n, M j j = 0 := by
    intro j
    have hs : (M j j * M j j) • b j = 0 := by
      calc
        (M j j * M j j) • b j = M j j • (M j j • b j) := by
          rw [mul_smul]
        _ = M j j • T (b j) := by rw [heigen j]
        _ = T (M j j • b j) := by rw [map_smul]
        _ = T (T (b j)) := by rw [heigen j]
        _ = 0 := hnil (b j)
    have hmul : M j j * M j j = 0 := by
      exact (smul_eq_zero.mp hs).resolve_right (b.ne_zero j)
    exact (mul_self_eq_zero.mp hmul)
  have hzero : T = 0 := by
    apply b.ext
    intro j
    rw [LinearMap.zero_apply, heigen j, hdiagzero j, zero_smul]
  have hi := LinearMap.congr_fun hzero Complex.I
  simp [T] at hi

#print axioms GroundTruth.linear_algebra_5D_19_certificate


theorem GroundTruth.linear_algebra_5E_4_certificate :
¬ (
∀ (F : Type) [RCLike F] (n : ℕ) (A B : Matrix (Fin n) (Fin n) F),
  (∀ i j, i ≠ j → A i j = 0) → (∀ i j, j < i → B i j = 0) → A*B = B*A
) := by
  classical
  push_neg
  refine ⟨ℝ, inferInstance, 2, ![![0, 0], ![0, 1]], ![![0, 1], ![0, 0]], ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i j hji
    fin_cases i <;> fin_cases j <;> simp_all
  · intro h
    have h01 := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
    norm_num [Matrix.mul_apply, Fin.sum_univ_two] at h01

#print axioms GroundTruth.linear_algebra_5E_4_certificate


theorem GroundTruth.linear_algebra_6A_1_certificate :
∀ (F : Type) [RCLike F] (V : Type) [NormedAddCommGroup V] [InnerProductSpace F V] [FiniteDimensional F V],
  ∀ m : ℕ, 1 ≤ m → ∀ v : Fin m → V,
  0 ≤ RCLike.re (∑ j : Fin m, ∑ k : Fin m, inner F (v j) (v k)) ∧
  RCLike.im (∑ j : Fin m, ∑ k : Fin m, inner F (v j) (v k)) = 0 := by
  classical
  intro F _ V _ _ _ m hm v
  have h : (∑ j : Fin m, ∑ k : Fin m, inner F (v j) (v k)) = inner F (∑ j, v j) (∑ k, v k) := by
    simp only [sum_inner, inner_sum]
    exact Finset.sum_comm
  rw [h]
  exact ⟨inner_self_nonneg, inner_self_im _⟩

#print axioms GroundTruth.linear_algebra_6A_1_certificate


theorem GroundTruth.linear_algebra_6A_24_certificate :
∀ B : LinearMap.BilinForm ℝ (Fin 2 → ℝ),
  (∀ v w, B v w = B w v) → (∀ v, v ≠ 0 → 0 < B v v) →
  ∃ v : Fin 2 → ℝ, Real.sqrt (B v v) ≠ max |v 0| |v 1| := by
  classical
  intro B hsym hpos
  by_contra h
  push_neg at h
  let e0 : Fin 2 → ℝ := ![1, 0]
  let e1 : Fin 2 → ℝ := ![0, 1]
  let p : Fin 2 → ℝ := e0 + e1
  let m : Fin 2 → ℝ := e0 - e1
  have he0 : e0 ≠ 0 := by
    intro he
    have he' := congrFun he (0 : Fin 2)
    norm_num [e0] at he'
  have he1 : e1 ≠ 0 := by
    intro he
    have he' := congrFun he (1 : Fin 2)
    norm_num [e1] at he'
  have hp : p ≠ 0 := by
    intro he
    have he' := congrFun he (0 : Fin 2)
    norm_num [p, e0, e1] at he'
  have hm : m ≠ 0 := by
    intro he
    have he' := congrFun he (0 : Fin 2)
    norm_num [m, e0, e1] at he'
  have h00 : B e0 e0 = 1 := by
    have hs := h e0
    have hs' : Real.sqrt (B e0 e0) = 1 := by
      simpa [e0] using hs
    have hb : 0 ≤ B e0 e0 := le_of_lt (hpos e0 he0)
    nlinarith [Real.sq_sqrt hb]
  have h11 : B e1 e1 = 1 := by
    have hs := h e1
    have hs' : Real.sqrt (B e1 e1) = 1 := by
      simpa [e1] using hs
    have hb : 0 ≤ B e1 e1 := le_of_lt (hpos e1 he1)
    nlinarith [Real.sq_sqrt hb]
  have hpp : B p p = 1 := by
    have hs := h p
    have hs' : Real.sqrt (B p p) = 1 := by
      simpa [p, e0, e1] using hs
    have hb : 0 ≤ B p p := le_of_lt (hpos p hp)
    nlinarith [Real.sq_sqrt hb]
  have hmm : B m m = 1 := by
    have hs := h m
    have hs' : Real.sqrt (B m m) = 1 := by
      simpa [m, e0, e1] using hs
    have hb : 0 ≤ B m m := le_of_lt (hpos m hm)
    nlinarith [Real.sq_sqrt hb]
  simp [p, m] at hpp hmm
  nlinarith

#print axioms GroundTruth.linear_algebra_6A_24_certificate


theorem GroundTruth.linear_algebra_7A_29_certificate :
¬ (
∀ (F : Type) [RCLike F] (V : Type) [NormedAddCommGroup V] [InnerProductSpace F V] [FiniteDimensional F V],
  ∀ (T : V →ₗ[F] V) (n : ℕ) (b : Module.Basis (Fin n) F V),
  Orthonormal F b → (∀ k, ‖T (b k)‖ = ‖(LinearMap.adjoint T) (b k)‖) → (T.comp (LinearMap.adjoint T) = (LinearMap.adjoint T).comp T)
) := by
  classical
  intro h
  let S : ℂ →ₗ[ℝ] ℂ := (Complex.reLm+Complex.imLm).smulRight (1:ℂ) - Complex.reLm.smulRight Complex.I
  let A : ℂ →ₗ[ℝ] ℂ := (Complex.reLm-Complex.imLm).smulRight (1:ℂ) + Complex.reLm.smulRight Complex.I
  have hA : A = LinearMap.adjoint S := by
    apply (LinearMap.eq_adjoint_iff A S).mpr
    intro x y
    simp [A,S,Complex.inner,LinearMap.smulRight_apply]
    ring
  let b : Module.Basis (Fin 2) ℝ ℂ := Complex.orthonormalBasisOneI.toBasis
  have hb : Orthonormal ℝ b := Complex.orthonormalBasisOneI.orthonormal
  have hbval : (b : Fin 2 → ℂ) = ![1,Complex.I] := Complex.coe_orthonormalBasisOneI
  have hn : ∀ k, ‖S (b k)‖ = ‖(LinearMap.adjoint S) (b k)‖ := by
    intro k
    rw [← hA,hbval]
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    fin_cases k <;> norm_num [S,A,LinearMap.smulRight_apply,Complex.normSq_apply]
  have he := h ℝ ℂ S 2 b hb hn
  rw [← hA] at he
  have hc := congrArg (fun L : ℂ →ₗ[ℝ] ℂ => (L 1).im) he
  norm_num [S,A,LinearMap.smulRight_apply] at hc

#print axioms GroundTruth.linear_algebra_7A_29_certificate


theorem GroundTruth.linear_algebra_7B_5_certificate :
¬ (
∀ T : EuclideanSpace ℂ (Fin 3) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3),
  (∃ b : Module.Basis (Fin 3) ℂ (EuclideanSpace ℂ (Fin 3)), ∀ i j, i ≠ j → LinearMap.toMatrix b b T i j = 0) →
  T.comp (LinearMap.adjoint T) = (LinearMap.adjoint T).comp T
) := by
  classical
  push_neg
  let A : Matrix (Fin 3) (Fin 3) ℂ := ![![1,1,0],![0,2,0],![0,0,3]]
  let P : Matrix (Fin 3) (Fin 3) ℂ := ![![1,1,0],![0,1,0],![0,0,1]]
  let Q : Matrix (Fin 3) (Fin 3) ℂ := ![![1,-1,0],![0,1,0],![0,0,1]]
  let D : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal ![1,2,3]
  have hmul (M N : Matrix (Fin 3) (Fin 3) ℂ) : Matrix.toEuclideanLin (M*N) = (Matrix.toEuclideanLin M).comp (Matrix.toEuclideanLin N) := by
    apply LinearMap.ext
    intro x
    change WithLp.toLp 2 (Matrix.mulVec (M*N) (WithLp.ofLp x)) = WithLp.toLp 2 (Matrix.mulVec M (Matrix.mulVec N (WithLp.ofLp x)))
    rw [Matrix.mulVec_mulVec]
  have hone : Matrix.toEuclideanLin (1 : Matrix (Fin 3) (Fin 3) ℂ) = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change WithLp.toLp 2 (Matrix.mulVec (1 : Matrix (Fin 3) (Fin 3) ℂ) (WithLp.ofLp x)) = x
    simp
  have hPQ : P*Q=1 := by ext i j; fin_cases i <;> fin_cases j <;> norm_num [P,Q,Matrix.mul_apply,Fin.sum_univ_succ]
  have hQP : Q*P=1 := by ext i j; fin_cases i <;> fin_cases j <;> norm_num [P,Q,Matrix.mul_apply,Fin.sum_univ_succ]
  have hAP : A*P=P*D := by
    ext i j
    change (A*P) i j = (P*Matrix.diagonal ![1,2,3] : Matrix (Fin 3) (Fin 3) ℂ) i j
    rw [Matrix.mul_diagonal]
    fin_cases i <;> fin_cases j <;> norm_num [A,P,Matrix.mul_apply,Fin.sum_univ_succ]
  let e : EuclideanSpace ℂ (Fin 3) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin 3) := LinearEquiv.ofLinear (Matrix.toEuclideanLin P) (Matrix.toEuclideanLin Q)
    (by rw [← hmul,hPQ,hone]) (by rw [← hmul,hQP,hone])
  let E : Module.Basis (Fin 3) ℂ (EuclideanSpace ℂ (Fin 3)) := (EuclideanSpace.basisFun (Fin 3) ℂ).toBasis
  let b := E.map e
  let T := Matrix.toEuclideanLin A
  have hmat : LinearMap.toMatrix E E (Matrix.toEuclideanLin D) = D := by
    change LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 3) ℂ).toBasis (EuclideanSpace.basisFun (Fin 3) ℂ).toBasis (Matrix.toEuclideanLin D) = D
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]
  have hDb (j : Fin 3) : Matrix.toEuclideanLin D (E j) = ((j.val:ℂ)+1) • E j := by
    apply E.repr.injective
    ext i
    have hc : (E.repr (Matrix.toEuclideanLin D (E j))) i = D i j := by rw [← LinearMap.toMatrix_apply,hmat]
    rw [hc]
    simp only [map_smul,Module.Basis.repr_self,Finsupp.smul_apply,Finsupp.single_apply,smul_eq_mul]
    by_cases hi : i=j
    · subst i; fin_cases j <;> norm_num [D,Matrix.diagonal,Fin.ext_iff]
    · simp [D,Matrix.diagonal,hi,Ne.symm hi]
  have hcomp : T.comp e.toLinearMap = e.toLinearMap.comp (Matrix.toEuclideanLin D) := by
    change (Matrix.toEuclideanLin A).comp (Matrix.toEuclideanLin P) = (Matrix.toEuclideanLin P).comp (Matrix.toEuclideanLin D)
    rw [← hmul,← hmul,hAP]
  have hev (j : Fin 3) : T (b j) = ((j.val:ℂ)+1) • b j := by
    change T (e (E j)) = ((j.val:ℂ)+1) • e (E j)
    have hc := congrArg (fun L : EuclideanSpace ℂ (Fin 3) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3) => L (E j)) hcomp
    simpa only [LinearMap.comp_apply,hDb,map_smul] using hc
  refine ⟨T,⟨b,?_⟩,?_⟩
  · intro i j hij
    rw [LinearMap.toMatrix_apply,hev]
    simp only [map_smul,Module.Basis.repr_self,Finsupp.smul_apply,Finsupp.single_apply,smul_eq_mul,if_neg (Ne.symm hij),mul_zero]
  · intro hn
    have hadj : LinearMap.adjoint T = Matrix.toEuclideanLin A.conjTranspose := (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A).symm
    rw [hadj] at hn
    change (Matrix.toEuclideanLin A).comp (Matrix.toEuclideanLin A.conjTranspose) = (Matrix.toEuclideanLin A.conjTranspose).comp (Matrix.toEuclideanLin A) at hn
    rw [← hmul,← hmul] at hn
    have hm := Matrix.toEuclideanLin.injective hn
    have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 0 0) hm
    norm_num [A,Matrix.mul_apply,Fin.sum_univ_succ] at h00

#print axioms GroundTruth.linear_algebra_7B_5_certificate


theorem GroundTruth.linear_algebra_7D_8_certificate :
¬ (
∀ (F : Type) [RCLike F] (V : Type) [NormedAddCommGroup V] [InnerProductSpace F V] [FiniteDimensional F V],
  ∀ (S : V →ₗ[F] V) (n : ℕ) (b : Module.Basis (Fin n) F V),
  Orthonormal F b → (∀ k, ‖S (b k)‖ = 1) → ((LinearMap.adjoint S).comp S = LinearMap.id ∧ S.comp (LinearMap.adjoint S) = LinearMap.id)
) := by
  classical
  intro h
  let S : ℂ →ₗ[ℝ] ℂ := (Complex.reLm + Complex.imLm).smulRight (1 : ℂ)
  let b : Module.Basis (Fin 2) ℝ ℂ := Complex.orthonormalBasisOneI.toBasis
  have hb : Orthonormal ℝ b := Complex.orthonormalBasisOneI.orthonormal
  have hbval : (b : Fin 2 → ℂ) = ![1, Complex.I] := Complex.coe_orthonormalBasisOneI
  have hn : ∀ k, ‖S (b k)‖ = 1 := by
    intro k
    rw [hbval]
    fin_cases k <;> norm_num [S, LinearMap.smulRight_apply]
  have he := (h ℝ ℂ S 2 b hb hn).1
  have hc := congrArg (fun L : ℂ →ₗ[ℝ] ℂ => L Complex.I) he
  change LinearMap.adjoint S (S Complex.I) = Complex.I at hc
  have hi := LinearMap.adjoint_inner_right S (1 : ℂ) (S Complex.I)
  rw [hc] at hi
  norm_num [S, Complex.inner, LinearMap.smulRight_apply] at hi

#print axioms GroundTruth.linear_algebra_7D_8_certificate


theorem GroundTruth.linear_algebra_7D_12_certificate :
¬ (
∀ (F : Type) [RCLike F] (V : Type) [NormedAddCommGroup V] [InnerProductSpace F V] [FiniteDimensional F V],
  ∀ S : V ≃ₗ[F] V,
  (∀ v : V, ‖S.symm v‖ = ‖S v‖) →
  (LinearMap.adjoint S.toLinearMap).comp S.toLinearMap = LinearMap.id ∧
  S.toLinearMap.comp (LinearMap.adjoint S.toLinearMap) = LinearMap.id
) := by
  classical
  intro h
  let T : ℂ →ₗ[ℝ] ℂ := (Complex.reLm + Complex.imLm).smulRight (1 : ℂ) - Complex.imLm.smulRight Complex.I
  have hTT : Function.Involutive T := by
    intro z
    apply Complex.ext <;> simp [T, LinearMap.smulRight_apply] <;> ring
  let S : ℂ ≃ₗ[ℝ] ℂ := LinearEquiv.ofInvolutive T hTT
  have hnorm : ∀ v : ℂ, ‖S.symm v‖ = ‖S v‖ := by
    intro v
    rfl
  have hc := congrArg (fun L : ℂ →ₗ[ℝ] ℂ => L Complex.I) (h ℝ ℂ S hnorm).1
  change LinearMap.adjoint T (T Complex.I) = Complex.I at hc
  have hi := LinearMap.adjoint_inner_left T Complex.I (T Complex.I)
  rw [hc] at hi
  norm_num [T, Complex.inner, LinearMap.smulRight_apply] at hi
  rw [← Complex.normSq_eq_norm_sq] at hi
  norm_num [Complex.normSq_apply] at hi

#print axioms GroundTruth.linear_algebra_7D_12_certificate


theorem GroundTruth.linear_algebra_7F_6_certificate :
¬ (
∀ (F : Type) [RCLike F] (V : Type) [NormedAddCommGroup V] [InnerProductSpace F V] [FiniteDimensional F V],
  ∀ S T : V →L[F] V, ‖S.comp T‖ = ‖T.comp S‖
) := by
  classical
  intro h
  let S : ℂ →L[ℝ] ℂ := Complex.reCLM.smulRight (1 : ℂ)
  let T : ℂ →L[ℝ] ℂ := Complex.imCLM.smulRight (1 : ℂ)
  have hST : S.comp T = T := by
    ext z
    simp [S, T, ContinuousLinearMap.smulRight_apply]
  have hTS : T.comp S = 0 := by
    ext z
    simp [S, T, ContinuousLinearMap.smulRight_apply]
  have hn := h ℝ ℂ S T
  rw [hST, hTS, norm_zero] at hn
  have htzero : T = 0 := norm_eq_zero.mp hn
  have hc := congrArg (fun L : ℂ →L[ℝ] ℂ => L Complex.I) htzero
  norm_num [T, ContinuousLinearMap.smulRight_apply] at hc

#print axioms GroundTruth.linear_algebra_7F_6_certificate


theorem GroundTruth.linear_algebra_8D_8_certificate :
¬ (
∀ (F : Type) [RCLike F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V],
  ∀ S T : V →ₗ[F] V, LinearMap.trace F V (S.comp T) = LinearMap.trace F V S * LinearMap.trace F V T
) := by
  classical
  intro h
  have heq := h ℝ (Fin 2 → ℝ) (LinearMap.id : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) LinearMap.id
  norm_num [LinearMap.trace_id] at heq

#print axioms GroundTruth.linear_algebra_8D_8_certificate


theorem GroundTruth.linear_algebra_9A_6_certificate :
¬ (
∀ (F : Type) [RCLike F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V],
  ∀ r : LinearMap.BilinForm F V, (∀ v w : V, r v w = r w v) →
  ∃ U : Submodule F V, (U : Set V) = {v | r v v = 0}
) := by
  classical
  intro h
  let r : LinearMap.BilinForm ℝ (ℝ × ℝ) :=
    LinearMap.mk₂ ℝ (fun v w : ℝ × ℝ => v.1 * w.2 + v.2 * w.1)
      (by
        intro m₁ m₂ n
        simp only [Prod.fst_add, Prod.snd_add]
        ring)
      (by
        intro c m n
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        ring)
      (by
        intro m n₁ n₂
        simp only [Prod.fst_add, Prod.snd_add]
        ring)
      (by
        intro c m n
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        ring)
  have hrsym : ∀ v w : ℝ × ℝ, r v w = r w v := by
    intro v w
    simp [r]
    ring
  obtain ⟨U, hU⟩ := h ℝ (ℝ × ℝ) r hrsym
  have hmem (v : ℝ × ℝ) : v ∈ U ↔ r v v = 0 := by
    have hv := Set.ext_iff.mp hU v
    simpa using hv
  have hx : ((1 : ℝ), (0 : ℝ)) ∈ U := by
    rw [hmem]
    norm_num [r]
  have hy : ((0 : ℝ), (1 : ℝ)) ∈ U := by
    rw [hmem]
    norm_num [r]
  have hxy := U.add_mem hx hy
  rw [hmem] at hxy
  norm_num [r] at hxy

#print axioms GroundTruth.linear_algebra_9A_6_certificate


theorem GroundTruth.linear_algebra_9B_4_certificate :
¬ (
∀ (F : Type) [RCLike F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V],
  ∀ a : AlternatingMap F V F (Fin 4),
  ∃ U : Submodule F (Fin 4 → V), (U : Set (Fin 4 → V)) = {v | a v = 0}
) := by
  classical
  intro h
  let a : AlternatingMap ℝ (Fin 4 → ℝ) ℝ (Fin 4) := Matrix.detRowAlternating
  let A : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![1,1,0,0]
  let B : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![0,0,1,1]
  have haA : a A = 0 := by change Matrix.det A = 0; norm_num [A, Matrix.det_diagonal, Fin.prod_univ_succ]
  have haB : a B = 0 := by change Matrix.det B = 0; norm_num [B, Matrix.det_diagonal, Fin.prod_univ_succ]
  have hsum : A+B = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [A,B,Matrix.diagonal,Matrix.one_apply]
  obtain ⟨U,hU⟩ := h ℝ (Fin 4 → ℝ) a
  have hA : A ∈ U := by change A ∈ (U : Set (Fin 4 → Fin 4 → ℝ)); rw [hU]; exact haA
  have hB : B ∈ U := by change B ∈ (U : Set (Fin 4 → Fin 4 → ℝ)); rw [hU]; exact haB
  have hAB := U.add_mem hA hB
  change A+B ∈ (U : Set (Fin 4 → Fin 4 → ℝ)) at hAB
  rw [hU] at hAB
  change Matrix.det (A+B) = 0 at hAB
  rw [hsum, Matrix.det_one] at hAB
  norm_num at hAB

#print axioms GroundTruth.linear_algebra_9B_4_certificate


theorem GroundTruth.linear_algebra_9C_1_certificate :
¬ (
∀ (F : Type) [RCLike F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V],
  ∀ S T : V →ₗ[F] V, LinearMap.det (S+T) = LinearMap.det S + LinearMap.det T
) := by
  classical
  intro h
  let I : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := LinearMap.id
  have heq := h ℝ (Fin 2 → ℝ) I I
  have hsum : I + I = (2 : ℝ) • I := by
    module
  rw [hsum] at heq
  norm_num [I, LinearMap.det_smul] at heq

#print axioms GroundTruth.linear_algebra_9C_1_certificate


theorem GroundTruth.linear_algebra_9C_11_certificate :
¬ (
∀ (V : Type) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] (T : V →ₗ[ℝ] V),
  0 < LinearMap.det T → ∃ S : V →ₗ[ℝ] V, S.comp S = T
) := by
  classical
  intro h
  let D : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![-1,-2]
  let T : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := Matrix.toLin' D
  have hdet : 0 < LinearMap.det T := by norm_num [T,D,Matrix.det_diagonal,Fin.prod_univ_succ]
  obtain ⟨S,hS⟩ := h (Fin 2 → ℝ) T hdet
  let M : Matrix (Fin 2) (Fin 2) ℝ := LinearMap.toMatrix' S
  have hMM : M*M = D := by
    have he := congrArg (fun L : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) => LinearMap.toMatrix' L) hS
    simpa only [LinearMap.toMatrix'_comp, T, LinearMap.toMatrix'_toLin'] using he
  have h00 := congrArg (fun Q : Matrix (Fin 2) (Fin 2) ℝ => Q 0 0) hMM
  have h01 := congrArg (fun Q : Matrix (Fin 2) (Fin 2) ℝ => Q 0 1) hMM
  have h11 := congrArg (fun Q : Matrix (Fin 2) (Fin 2) ℝ => Q 1 1) hMM
  norm_num [Matrix.mul_apply,Fin.sum_univ_two,D,Matrix.diagonal,Fin.ext_iff] at h00 h01 h11
  have hsumne : M 0 0 + M 1 1 ≠ 0 := by
    intro hz
    have hd : M 1 1 = -M 0 0 := by linarith
    rw [hd] at h11
    nlinarith [h00]
  have hprod : (M 0 0 + M 1 1) * M 0 1 = 0 := by nlinarith [h01]
  have hb : M 0 1 = 0 := (mul_eq_zero.mp hprod).resolve_left hsumne
  rw [hb] at h00
  nlinarith [sq_nonneg (M 0 0)]

#print axioms GroundTruth.linear_algebra_9C_11_certificate


theorem GroundTruth.calculus_3_3_4_certificate :
∃ (f : ℝ → ℝ) (g : ℝ → ℝ) (D : Set ℝ) (E : Set ℝ), ∃ x ∈ D, f x ∈ E ∧ x ∈ E ∧ g x ∈ D ∧ g (f x) ≠ f (g x) := by
  refine ⟨(fun x : ℝ => x+1), (fun x : ℝ => x^2), Set.univ, Set.univ, 1, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

#print axioms GroundTruth.calculus_3_3_4_certificate


theorem GroundTruth.calculus_3_3_5_certificate :
∃ (f : ℝ → ℝ) (g : ℝ → ℝ) (h : ℝ → ℝ), (fun (x : ℝ) => f (g x + h x)) ≠ fun (x : ℝ) => f (g x) + f (h x) := by
  refine ⟨(fun x : ℝ => x^2), (fun _ => 1), (fun _ => 1), ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num at hh

#print axioms GroundTruth.calculus_3_3_5_certificate


theorem GroundTruth.calculus_3_3_6_certificate :
∀ f g h : ℝ → ℝ, (fun x => f (h x)+g (h x)) = (fun x => (f ∘ h) x+(g ∘ h) x) := by
  classical
  first
  | solve | norm_num
  | solve | simp [Function.comp_def]
  | solve | aesop (config := { maxRuleApplications := 30 })

#print axioms GroundTruth.calculus_3_3_6_certificate


theorem GroundTruth.calculus_23_3_1_certificate :
∃ L : ℝ, Tendsto (fun z : ℝ × ℝ => (z.1*z.2) / (Real.sqrt (z.1^2+z.2^2)))
  (nhdsWithin (0 : ℝ × ℝ) {z : ℝ × ℝ | z ≠ 0 ∧ (Real.sqrt (z.1^2+z.2^2)) ≠ 0}) (nhds L) := by
  refine ⟨0, ?_⟩
  let F := nhdsWithin (0 : ℝ × ℝ)
    {z : ℝ × ℝ | z ≠ 0 ∧ Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ≠ 0}
  have hx : Tendsto (fun z : ℝ × ℝ => z.1) F (nhds 0) :=
    (continuous_fst.tendsto (0 : ℝ × ℝ)).mono_left inf_le_left
  rw [Metric.tendsto_nhds]
  intro ε hε
  have he : ∀ᶠ z in F, dist z.1 0 < ε :=
    (Metric.tendsto_nhds.1 hx) ε hε
  filter_upwards [he, self_mem_nhdsWithin] with z hz hzd
  have hr0 : 0 < Real.sqrt (z.1 ^ 2 + z.2 ^ 2) :=
    lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hzd.2)
  have hy2 : z.2 ^ 2 ≤ z.1 ^ 2 + z.2 ^ 2 := by
    nlinarith [sq_nonneg z.1]
  have hy : |z.2| ≤ Real.sqrt (z.1 ^ 2 + z.2 ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hy2
  have hb : |z.1 * z.2 / Real.sqrt (z.1 ^ 2 + z.2 ^ 2)| ≤ |z.1| := by
    rw [abs_div, abs_mul, abs_of_pos hr0]
    apply (div_le_iff₀ hr0).2
    simpa [mul_assoc] using
      mul_le_mul_of_nonneg_left hy (abs_nonneg z.1)
  have hz' : |z.1| < ε := by
    simpa [Real.dist_eq] using hz
  rw [Real.dist_eq, sub_zero]
  exact lt_of_le_of_lt hb hz'

#print axioms GroundTruth.calculus_23_3_1_certificate


theorem GroundTruth.calculus_23_3_2_certificate :
∃ L : ℝ, Tendsto (fun z : ℝ × ℝ => (z.1^2*z.2^2) / (z.1^2+z.2^2))
  (nhdsWithin (0 : ℝ × ℝ) {z : ℝ × ℝ | z ≠ 0 ∧ (z.1^2+z.2^2) ≠ 0}) (nhds L) := by
  refine ⟨0, ?_⟩
  let F := nhdsWithin (0 : ℝ × ℝ)
    {z : ℝ × ℝ | z ≠ 0 ∧ z.1 ^ 2 + z.2 ^ 2 ≠ 0}
  have hx : Tendsto (fun z : ℝ × ℝ => z.1) F (nhds 0) :=
    (continuous_fst.tendsto (0 : ℝ × ℝ)).mono_left inf_le_left
  have hx2 : Tendsto (fun z : ℝ × ℝ => z.1 ^ 2) F (nhds 0) := by
    simpa using hx.pow 2
  rw [Metric.tendsto_nhds]
  intro ε hε
  have he : ∀ᶠ z in F, dist (z.1 ^ 2) 0 < ε :=
    (Metric.tendsto_nhds.1 hx2) ε hε
  filter_upwards [he, self_mem_nhdsWithin] with z hz hzd
  have hd : 0 < z.1 ^ 2 + z.2 ^ 2 := by
    have hn : 0 ≤ z.1 ^ 2 + z.2 ^ 2 := by positivity
    exact lt_of_le_of_ne hn (Ne.symm hzd.2)
  have hv : 0 ≤ z.1 ^ 2 * z.2 ^ 2 / (z.1 ^ 2 + z.2 ^ 2) := by
    positivity
  have hb : z.1 ^ 2 * z.2 ^ 2 / (z.1 ^ 2 + z.2 ^ 2) ≤ z.1 ^ 2 := by
    apply (div_le_iff₀ hd).2
    have hy : z.2 ^ 2 ≤ z.1 ^ 2 + z.2 ^ 2 := by
      nlinarith [sq_nonneg z.1]
    nlinarith [mul_le_mul_of_nonneg_left hy (sq_nonneg z.1)]
  have hz' : z.1 ^ 2 < ε := by
    simpa [Real.dist_eq, abs_of_nonneg (sq_nonneg z.1)] using hz
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hv]
  exact lt_of_le_of_lt hb hz'

#print axioms GroundTruth.calculus_23_3_2_certificate


theorem GroundTruth.calculus_23_3_3_certificate :
∀ L : ℝ, ¬ Tendsto (fun z : ℝ × ℝ => (z.1*z.2) / (z.1^2+z.2^2))
  (nhdsWithin (0 : ℝ × ℝ) {z : ℝ × ℝ | z ≠ 0 ∧ (z.1^2+z.2^2) ≠ 0}) (nhds L) := by
  classical
  intro L h
  let S : Set (ℝ × ℝ) := {z | z ≠ 0 ∧ (z.1^2 + z.2^2) ≠ 0}
  have hp₀ : Tendsto (fun t : ℝ => (t, 0)) (𝓝[≠] 0) (nhdsWithin (0 : ℝ × ℝ) S) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact (((continuousAt_id : ContinuousAt (fun t : ℝ => t) 0).prodMk continuousAt_const).tendsto).mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := by simpa using ht
      simp [S, ht0]
  have hp₁ : Tendsto (fun t : ℝ => (t, t)) (𝓝[≠] 0) (nhdsWithin (0 : ℝ × ℝ) S) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact (((continuousAt_id : ContinuousAt (fun t : ℝ => t) 0).prodMk continuousAt_id).tendsto).mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := by simpa using ht
      simp [S, ht0]
  have h₀ := h.comp hp₀
  have h₁ := h.comp hp₁
  have h₀' : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[≠] 0) (nhds L) := by
    apply h₀.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    simp [Function.comp_apply, ht0]
  have h₁' : Tendsto (fun _ : ℝ => (1 / 2 : ℝ)) (𝓝[≠] 0) (nhds L) := by
    apply h₁.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    simp only [Function.comp_apply, Prod.fst, Prod.snd]
    field_simp [ht0]
    ring
  have hL0 : L = 0 := tendsto_nhds_unique h₀' tendsto_const_nhds
  have hL1 : L = 1 / 2 := tendsto_nhds_unique h₁' tendsto_const_nhds
  rw [hL0] at hL1
  norm_num at hL1

#print axioms GroundTruth.calculus_23_3_3_certificate


theorem GroundTruth.calculus_23_3_4_certificate :
∀ L : ℝ, ¬ Tendsto (fun z : ℝ × ℝ => (z.1^2*z.2) / (z.1^3+z.2^3))
  (nhdsWithin (0 : ℝ × ℝ) {z : ℝ × ℝ | z ≠ 0 ∧ (z.1^3+z.2^3) ≠ 0}) (nhds L) := by
  classical
  intro L h
  let S : Set (ℝ × ℝ) := {z | z ≠ 0 ∧ (z.1^3 + z.2^3) ≠ 0}
  have hp₀ : Tendsto (fun t : ℝ => (t, 0)) (𝓝[≠] 0) (nhdsWithin (0 : ℝ × ℝ) S) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact (((continuousAt_id : ContinuousAt (fun t : ℝ => t) 0).prodMk continuousAt_const).tendsto).mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := by simpa using ht
      simp [S, ht0]
  have hp₁ : Tendsto (fun t : ℝ => (t, t)) (𝓝[≠] 0) (nhdsWithin (0 : ℝ × ℝ) S) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact (((continuousAt_id : ContinuousAt (fun t : ℝ => t) 0).prodMk continuousAt_id).tendsto).mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := by simpa using ht
      constructor
      · simp [ht0]
      · rw [show t^3 + t^3 = 2*t^3 by ring]
        exact mul_ne_zero (by norm_num) (pow_ne_zero 3 ht0)
  have h₀ := h.comp hp₀
  have h₁ := h.comp hp₁
  have h₀' : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[≠] 0) (nhds L) := by
    apply h₀.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    simp [Function.comp_apply, ht0]
  have h₁' : Tendsto (fun _ : ℝ => (1 / 2 : ℝ)) (𝓝[≠] 0) (nhds L) := by
    apply h₁.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    simp only [Function.comp_apply, Prod.fst, Prod.snd]
    field_simp [ht0]
    ring
  have hL0 : L = 0 := tendsto_nhds_unique h₀' tendsto_const_nhds
  have hL1 : L = 1 / 2 := tendsto_nhds_unique h₁' tendsto_const_nhds
  rw [hL0] at hL1
  norm_num at hL1

#print axioms GroundTruth.calculus_23_3_4_certificate


theorem GroundTruth.calculus_23_3_5_certificate :
∀ L : ℝ, ¬ Tendsto (fun z : ℝ × ℝ => (3*z.1^2*z.2^2) / (7*z.1^6+4*z.2^3))
  (nhdsWithin (0 : ℝ × ℝ) {z : ℝ × ℝ | z ≠ 0 ∧ (7*z.1^6+4*z.2^3) ≠ 0}) (nhds L) := by
  classical
  intro L h
  let S : Set (ℝ × ℝ) :=
    {z | z ≠ 0 ∧ (7 * z.1 ^ 6 + 4 * z.2 ^ 3) ≠ 0}
  have ht : Tendsto (fun t : ℝ => t) (𝓝[≠] 0) (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  have hp₀ : Tendsto (fun t : ℝ => (t, 0)) (𝓝[≠] 0)
      (nhdsWithin (0 : ℝ × ℝ) S) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hzero : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[≠] 0) (nhds 0) := tendsto_const_nhds
      simpa only [← nhds_prod_eq] using ht.prodMk hzero
    · filter_upwards [self_mem_nhdsWithin] with t ht'
      have ht0 : t ≠ 0 := by simpa using ht'
      simp [S, ht0]
  have hp₁ : Tendsto (fun t : ℝ => (t, t ^ 2)) (𝓝[≠] 0)
      (nhdsWithin (0 : ℝ × ℝ) S) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · simpa only [← nhds_prod_eq, zero_pow (by norm_num : (2:ℕ) ≠ 0)] using ht.prodMk (ht.pow 2)
    · filter_upwards [self_mem_nhdsWithin] with t ht'
      have ht0 : t ≠ 0 := by simpa using ht'
      constructor
      · intro hz
        have hz' := congrArg Prod.fst hz
        exact ht0 (by simpa using hz')
      · rw [show 7 * t ^ 6 + 4 * (t ^ 2) ^ 3 = 11 * t ^ 6 by ring]
        exact mul_ne_zero (by norm_num) (pow_ne_zero 6 ht0)
  have h₀ := h.comp hp₀
  have h₁ := h.comp hp₁
  have h₀' : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[≠] 0) (nhds L) := by
    apply h₀.congr'
    filter_upwards with t
    simp [Function.comp_apply]
  have h₁' : Tendsto (fun _ : ℝ => (3 / 11 : ℝ)) (𝓝[≠] 0) (nhds L) := by
    apply h₁.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht'
    have ht0 : t ≠ 0 := by simpa using ht'
    simp only [Function.comp_apply]
    rw [show 3 * t ^ 2 * (t ^ 2) ^ 2 = 3 * t ^ 6 by ring]
    rw [show 7 * t ^ 6 + 4 * (t ^ 2) ^ 3 = 11 * t ^ 6 by ring]
    field_simp [ht0]
  have hL0 : L = 0 := tendsto_nhds_unique h₀' tendsto_const_nhds
  have hL1 : L = 3 / 11 := tendsto_nhds_unique h₁' tendsto_const_nhds
  rw [hL0] at hL1
  norm_num at hL1

#print axioms GroundTruth.calculus_23_3_5_certificate


theorem GroundTruth.calculus_23_3_6_certificate :
∀ L : ℝ, ¬ Tendsto (fun z : ℝ × ℝ => (z.1^2*z.2^3) / (z.1^5+z.2^5))
  (nhdsWithin (0 : ℝ × ℝ) {z : ℝ × ℝ | z ≠ 0 ∧ (z.1^5+z.2^5) ≠ 0}) (nhds L) := by
  classical
  intro L h
  let S : Set (ℝ × ℝ) := {z | z ≠ 0 ∧ (z.1^5 + z.2^5) ≠ 0}
  have hp₀ : Tendsto (fun t : ℝ => (t, 0)) (𝓝[≠] 0) (nhdsWithin (0 : ℝ × ℝ) S) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact (((continuousAt_id : ContinuousAt (fun t : ℝ => t) 0).prodMk continuousAt_const).tendsto).mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := by simpa using ht
      simp [S, ht0]
  have hp₁ : Tendsto (fun t : ℝ => (t, t)) (𝓝[≠] 0) (nhdsWithin (0 : ℝ × ℝ) S) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact (((continuousAt_id : ContinuousAt (fun t : ℝ => t) 0).prodMk continuousAt_id).tendsto).mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := by simpa using ht
      constructor
      · simp [ht0]
      · rw [show t^5 + t^5 = 2*t^5 by ring]
        exact mul_ne_zero (by norm_num) (pow_ne_zero 5 ht0)
  have h₀ := h.comp hp₀
  have h₁ := h.comp hp₁
  have h₀' : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[≠] 0) (nhds L) := by
    apply h₀.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    simp [Function.comp_apply, ht0]
  have h₁' : Tendsto (fun _ : ℝ => (1 / 2 : ℝ)) (𝓝[≠] 0) (nhds L) := by
    apply h₁.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    simp only [Function.comp_apply, Prod.fst, Prod.snd]
    field_simp [ht0]
    ring
  have hL0 : L = 0 := tendsto_nhds_unique h₀' tendsto_const_nhds
  have hL1 : L = 1 / 2 := tendsto_nhds_unique h₁' tendsto_const_nhds
  rw [hL0] at hL1
  norm_num at hL1

#print axioms GroundTruth.calculus_23_3_6_certificate


theorem GroundTruth.calculus_23_3_7_certificate :
¬Continuous fun (z : ℝ × ℝ) =>
    if z = (0 : ℝ × ℝ) then (1 : ℝ) else Real.sin (z.1 * z.2) / (z.1 ^ (2 : ℕ) + z.2 ^ (2 : ℕ)) := by
  classical
  intro h
  let f : ℝ × ℝ → ℝ := fun z => if z = 0 then 1 else Real.sin (z.1*z.2) / (z.1^2 + z.2^2)
  have hp : Tendsto (fun t : ℝ => (t, 0)) (𝓝[≠] 0) (𝓝 (0 : ℝ × ℝ)) := by
    exact (((continuousAt_id : ContinuousAt (fun t : ℝ => t) 0).prodMk continuousAt_const).tendsto).mono_left inf_le_left
  have hf : Tendsto (fun t : ℝ => f (t, 0)) (𝓝[≠] 0) (𝓝 (f 0)) := by
    exact h.continuousAt.tendsto.comp hp
  have hf1 : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[≠] 0) (𝓝 (1 : ℝ)) := by
    have heq : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[≠] 0) (𝓝 (f 0)) := by
      apply hf.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := by simpa using ht
      simp [f, ht0]
    simpa [f] using heq
  have hzero : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[≠] 0) (𝓝 (0 : ℝ)) := tendsto_const_nhds
  have h10 : (1 : ℝ) = 0 := tendsto_nhds_unique hf1 hzero
  norm_num at h10

#print axioms GroundTruth.calculus_23_3_7_certificate


theorem GroundTruth.calculus_23_3_9_certificate :
∀ L : ℝ, ¬ Tendsto (fun z : ℝ × ℝ => (z.1^2) / (z.1^2+z.2^2))
  (nhdsWithin (0 : ℝ × ℝ) {z : ℝ × ℝ | z ≠ 0 ∧ (z.1^2+z.2^2) ≠ 0}) (nhds L) := by
  classical
  intro L h
  let S : Set (ℝ × ℝ) := {z | z ≠ 0 ∧ (z.1^2 + z.2^2) ≠ 0}
  have hp₁ : Tendsto (fun t : ℝ => (t, 0)) (𝓝[≠] 0) (nhdsWithin (0 : ℝ × ℝ) S) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact (((continuousAt_id : ContinuousAt (fun t : ℝ => t) 0).prodMk continuousAt_const).tendsto).mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := by simpa using ht
      simp [S, ht0]
  have hp₀ : Tendsto (fun t : ℝ => (0, t)) (𝓝[≠] 0) (nhdsWithin (0 : ℝ × ℝ) S) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact ((continuousAt_const.prodMk (continuousAt_id : ContinuousAt (fun t : ℝ => t) 0)).tendsto).mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := by simpa using ht
      simp [S, ht0]
  have h₁ := h.comp hp₁
  have h₀ := h.comp hp₀
  have h₁' : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[≠] 0) (nhds L) := by
    apply h₁.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    simp only [Function.comp_apply, Prod.fst, Prod.snd, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
    exact div_self (pow_ne_zero 2 ht0)
  have h₀' : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[≠] 0) (nhds L) := by
    apply h₀.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    simp [Function.comp_apply, ht0]
  have hL1 : L = 1 := tendsto_nhds_unique h₁' tendsto_const_nhds
  have hL0 : L = 0 := tendsto_nhds_unique h₀' tendsto_const_nhds
  rw [hL0] at hL1
  norm_num at hL1

#print axioms GroundTruth.calculus_23_3_9_certificate


theorem GroundTruth.calculus_23_3_10_certificate :
∀ L : ℝ, ¬ Tendsto (fun z : ℝ × ℝ => (z.1^4+z.2^4) / (z.1*z.2))
  (nhdsWithin (0 : ℝ × ℝ) {z : ℝ × ℝ | z ≠ 0 ∧ (z.1*z.2) ≠ 0}) (nhds L) := by
  classical
  intro L h
  let S : Set (ℝ × ℝ) := {z | z ≠ 0 ∧ (z.1 * z.2) ≠ 0}
  have hp₀ : Tendsto (fun t : ℝ => (t, t)) (𝓝[≠] 0)
      (nhdsWithin (0 : ℝ × ℝ) S) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hcont : Tendsto (fun t : ℝ => (t, t)) (𝓝 0)
          (𝓝 (0 : ℝ × ℝ)) := by
        simpa using (by fun_prop : Continuous (fun t : ℝ => (t, t))).tendsto (0 : ℝ)
      exact hcont.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := by simpa using ht
      simp [S, ht0]
  have hp₁ : Tendsto (fun t : ℝ => (t, t ^ 3)) (𝓝[≠] 0)
      (nhdsWithin (0 : ℝ × ℝ) S) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hcont : Tendsto (fun t : ℝ => (t, t ^ 3)) (𝓝 0)
          (𝓝 (0 : ℝ × ℝ)) := by
        simpa using (by fun_prop : Continuous (fun t : ℝ => (t, t ^ 3))).tendsto (0 : ℝ)
      exact hcont.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := by simpa using ht
      simp [S, ht0]
  have hpath₀ := h.comp hp₀
  have hpath₁ := h.comp hp₁
  have hcalc₀ : Tendsto (fun t : ℝ => 2 * t ^ 2) (𝓝[≠] 0) (𝓝 L) := by
    apply hpath₀.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    simp only [Function.comp_apply]
    field_simp [ht0] <;> ring
  have hcalc₁ : Tendsto (fun t : ℝ => 1 + t ^ 8) (𝓝[≠] 0) (𝓝 L) := by
    apply hpath₁.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    simp only [Function.comp_apply]
    field_simp [ht0] <;> ring
  have hlim₀ : Tendsto (fun t : ℝ => 2 * t ^ 2) (𝓝[≠] 0) (𝓝 (0 : ℝ)) := by
    have hcont : Tendsto (fun t : ℝ => 2 * t ^ 2) (𝓝 0) (𝓝 (0 : ℝ)) := by
      simpa using (by fun_prop : Continuous (fun t : ℝ => 2 * t ^ 2)).tendsto (0 : ℝ)
    exact hcont.mono_left inf_le_left
  have hlim₁ : Tendsto (fun t : ℝ => 1 + t ^ 8) (𝓝[≠] 0) (𝓝 (1 : ℝ)) := by
    have hcont : Tendsto (fun t : ℝ => 1 + t ^ 8) (𝓝 0) (𝓝 (1 : ℝ)) := by
      simpa using (by fun_prop : Continuous (fun t : ℝ => 1 + t ^ 8)).tendsto (0 : ℝ)
    exact hcont.mono_left inf_le_left
  have hL0 : L = 0 := tendsto_nhds_unique hcalc₀ hlim₀
  have hL1 : L = 1 := tendsto_nhds_unique hcalc₁ hlim₁
  linarith

#print axioms GroundTruth.calculus_23_3_10_certificate


theorem GroundTruth.calculus_23_3_11_certificate :
∀ L : ℝ, ¬ Tendsto (fun z : ℝ × ℝ => (z.1^4+z.2^8) / (z.1^2*z.2^2))
  (nhdsWithin (0 : ℝ × ℝ) {z : ℝ × ℝ | z ≠ 0 ∧ (z.1^2*z.2^2) ≠ 0}) (nhds L) := by
  classical
  intro L h
  let S : Set (ℝ × ℝ) := {z | z ≠ 0 ∧ (z.1 ^ 2 * z.2 ^ 2) ≠ 0}
  have hp₁ : Tendsto (fun t : ℝ => (t, t)) (𝓝[≠] 0)
      (nhdsWithin (0 : ℝ × ℝ) S) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hcont : Tendsto (fun t : ℝ => (t, t)) (𝓝 0)
          (𝓝 (0 : ℝ × ℝ)) := by
        simpa using (by fun_prop : Continuous (fun t : ℝ => (t, t))).tendsto (0 : ℝ)
      exact hcont.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := by simpa using ht
      simp [S, ht0]
  have hp₂ : Tendsto (fun t : ℝ => (t ^ 2, t)) (𝓝[≠] 0)
      (nhdsWithin (0 : ℝ × ℝ) S) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hcont : Tendsto (fun t : ℝ => (t ^ 2, t)) (𝓝 0)
          (𝓝 (0 : ℝ × ℝ)) := by
        simpa using (by fun_prop : Continuous (fun t : ℝ => (t ^ 2, t))).tendsto (0 : ℝ)
      exact hcont.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := by simpa using ht
      simp [S, ht0]
  have hpath₁ := h.comp hp₁
  have hpath₂ := h.comp hp₂
  have hcalc₁ : Tendsto (fun t : ℝ => 1 + t ^ 4) (𝓝[≠] 0) (𝓝 L) := by
    apply hpath₁.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    simp only [Function.comp_apply]
    field_simp [ht0] <;> ring
  have hcalc₂ : Tendsto (fun t : ℝ => 2 * t ^ 2) (𝓝[≠] 0) (𝓝 L) := by
    apply hpath₂.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    simp only [Function.comp_apply]
    field_simp [ht0] <;> ring
  have hlim₁ : Tendsto (fun t : ℝ => 1 + t ^ 4) (𝓝[≠] 0) (𝓝 (1 : ℝ)) := by
    have hcont : Tendsto (fun t : ℝ => 1 + t ^ 4) (𝓝 0) (𝓝 (1 : ℝ)) := by
      simpa using (by fun_prop : Continuous (fun t : ℝ => 1 + t ^ 4)).tendsto (0 : ℝ)
    exact hcont.mono_left inf_le_left
  have hlim₂ : Tendsto (fun t : ℝ => 2 * t ^ 2) (𝓝[≠] 0) (𝓝 (0 : ℝ)) := by
    have hcont : Tendsto (fun t : ℝ => 2 * t ^ 2) (𝓝 0) (𝓝 (0 : ℝ)) := by
      simpa using (by fun_prop : Continuous (fun t : ℝ => 2 * t ^ 2)).tendsto (0 : ℝ)
    exact hcont.mono_left inf_le_left
  have hL1 : L = 1 := tendsto_nhds_unique hcalc₁ hlim₁
  have hL0 : L = 0 := tendsto_nhds_unique hcalc₂ hlim₂
  linarith

#print axioms GroundTruth.calculus_23_3_11_certificate


theorem GroundTruth.calculus_23_3_14_certificate :
∃ (f : ℝ × ℝ → ℝ),
  (∀ (v : ℝ × ℝ), v ≠ (0 : ℝ × ℝ) → Tendsto (fun (t : ℝ) => f (t * v.1, t * v.2)) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ))) ∧
    ¬Tendsto f (𝓝[≠] (0 : ℝ × ℝ)) (𝓝 (0 : ℝ)) := by
  classical
  refine ⟨fun z : ℝ × ℝ => z.1 * z.2 ^ 3 / (z.1 ^ 2 + z.2 ^ 6), ?_, ?_⟩
  · intro v hv
    rcases v with ⟨a, b⟩
    by_cases ha : a = 0
    · simp [ha]
    · let g : ℝ → ℝ := fun t => t ^ 2 * a * b ^ 3 / (a ^ 2 + t ^ 4 * b ^ 6)
      have hden : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
      have hg : Tendsto g (𝓝[≠] 0) (𝓝 0) := by
        have hc : ContinuousAt g 0 := by
          apply ContinuousAt.div
          · fun_prop
          · fun_prop
          · simpa [g] using hden
        simpa [g] using hc.tendsto.mono_left inf_le_left
      apply hg.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht
      dsimp [g]
      have haux : a ^ 2 + t ^ 4 * b ^ 6 ≠ 0 := by
        have hpos : 0 < a ^ 2 := sq_pos_of_ne_zero ha
        positivity
      field_simp [ht, ha, haux]
      all_goals ring
  · intro h
    have hp0 : Tendsto (fun t : ℝ => (t ^ 3, t)) (𝓝[≠] 0) (𝓝 (0 : ℝ × ℝ)) := by
      have hc : Tendsto (fun t : ℝ => (t^3,t)) (nhds (0 : ℝ)) (nhds (0 : ℝ × ℝ)) := by
        simpa using ((continuous_id.pow 3).prodMk continuous_id).tendsto (0 : ℝ)
      simpa using hc.mono_left inf_le_left
    have hp : Tendsto (fun t : ℝ => (t ^ 3, t)) (𝓝[≠] 0) (𝓝[≠] (0 : ℝ × ℝ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨hp0, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht ⊢
      intro hz
      apply ht
      exact congrArg Prod.snd hz
    have hc : Tendsto
        (fun t : ℝ => (t ^ 3) * t ^ 3 / ((t ^ 3) ^ 2 + t ^ 6))
        (𝓝[≠] 0) (𝓝 0) := by
      simpa only [Function.comp_apply] using h.comp hp
    have heq :
        (fun t : ℝ => (t ^ 3) * t ^ 3 / ((t ^ 3) ^ 2 + t ^ 6)) =ᶠ[𝓝[≠] 0]
          fun _ : ℝ => (1 / 2 : ℝ) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht
      field_simp [ht]
      all_goals ring
    have hc' : Tendsto (fun _ : ℝ => (1 / 2 : ℝ)) (𝓝[≠] 0) (𝓝 0) :=
      hc.congr' heq
    have hconst : Tendsto (fun _ : ℝ => (1 / 2 : ℝ)) (𝓝[≠] 0) (𝓝 (1 / 2 : ℝ)) :=
      tendsto_const_nhds
    have hz : (0 : ℝ) = 1 / 2 := tendsto_nhds_unique hc' hconst
    norm_num at hz

#print axioms GroundTruth.calculus_23_3_14_certificate


theorem GroundTruth.calculus_30_3_1_conjecture_1_certificate :
∃ (f : ℝ × ℝ → ℝ),
  (∀ (θ : ℝ),
      ∃ (δ : ℝ), (0 : ℝ) < δ ∧ MonotoneOn (fun (t : ℝ) => f (t * Real.cos θ, t * Real.sin θ)) (Set.Icc (0 : ℝ) δ)) ∧
    ∀ (δ : ℝ), (0 : ℝ) < δ → ∃ (z : ℝ × ℝ), ‖z‖ < δ ∧ f z < f (0 : ℝ × ℝ) := by
  classical
  refine ⟨(fun z : ℝ × ℝ => (z.2 - z.1 ^ 2) * (z.2 - 2 * z.1 ^ 2)), ?_, ?_⟩
  · intro θ
    let a : ℝ := Real.cos θ
    let b : ℝ := Real.sin θ
    have hd (t : ℝ) :
        HasDerivAt
          (fun s : ℝ => (s * b - (s * a) ^ 2) *
            (s * b - 2 * (s * a) ^ 2))
          (2 * t * b ^ 2 - 9 * t ^ 2 * a ^ 2 * b +
            8 * t ^ 3 * a ^ 4) t := by
      convert
        (((hasDerivAt_id t).const_mul b).sub
            (((hasDerivAt_id t).const_mul a).pow 2)).mul
          (((hasDerivAt_id t).const_mul b).sub
            (((((hasDerivAt_id t).const_mul a).pow 2).const_mul 2)))
        using 1 <;> first | (funext s; dsimp; ring) | (dsimp; ring)
    by_cases hb : b = 0
    · refine ⟨1, by norm_num, ?_⟩
      change MonotoneOn
        (fun t : ℝ => (t * b - (t * a) ^ 2) *
          (t * b - 2 * (t * a) ^ 2)) (Set.Icc 0 1)
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1) (by fun_prop)
        (by fun_prop)
      intro t ht
      rw [interior_Icc] at ht
      have ht0 : 0 < t := ht.1
      rw [(hd t).deriv, hb]
      simp only [mul_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, sub_zero]
      positivity
    · let d : ℝ := b ^ 2 / (18 * (|a ^ 2 * b| + 1))
      have hb2 : 0 < b ^ 2 := sq_pos_of_ne_zero hb
      have hden : 0 < 18 * (|a ^ 2 * b| + 1) := by positivity
      have hdpos : 0 < d := div_pos hb2 hden
      refine ⟨d, hdpos, ?_⟩
      change MonotoneOn
        (fun t : ℝ => (t * b - (t * a) ^ 2) *
          (t * b - 2 * (t * a) ^ 2)) (Set.Icc 0 d)
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 d) (by fun_prop)
        (by fun_prop)
      intro t ht
      rw [(hd t).deriv]
      rw [interior_Icc] at ht
      have ht0 : 0 < t := ht.1
      have htd : t < b ^ 2 / (18 * (|a ^ 2 * b| + 1)) := ht.2
      have hmul : t * (18 * (|a ^ 2 * b| + 1)) < b ^ 2 :=
        (lt_div_iff₀ hden).mp htd
      have hab : a ^ 2 * b ≤ |a ^ 2 * b| := le_abs_self _
      have hcomp : t * (a ^ 2 * b) ≤ t * |a ^ 2 * b| :=
        mul_le_mul_of_nonneg_left hab ht0.le
      have hlast : 0 ≤ 8 * t ^ 3 * a ^ 4 := by positivity
      nlinarith
  · intro δ hδ
    let x : ℝ := min δ 1 / 4
    have hminpos : 0 < min δ 1 := lt_min hδ (by norm_num)
    have hxpos : 0 < x := by
      dsimp [x]
      positivity
    have hxδ : x < δ := by
      dsimp [x]
      have hle : min δ 1 ≤ δ := min_le_left _ _
      nlinarith
    have hxone : x ≤ 1 / 4 := by
      dsimp [x]
      exact div_le_div_of_nonneg_right (min_le_right δ 1) (by norm_num)
    have hypos : 0 ≤ (3 / 2 : ℝ) * x ^ 2 := by positivity
    have hyx : (3 / 2 : ℝ) * x ^ 2 < x := by
      nlinarith [sq_nonneg x]
    refine ⟨(x, (3 / 2 : ℝ) * x ^ 2), ?_, ?_⟩
    · rw [Prod.norm_def]
      simp only [Real.norm_eq_abs, max_lt_iff]
      rw [abs_of_pos hxpos, abs_of_nonneg hypos]
      exact ⟨hxδ, lt_trans hyx hxδ⟩
    · change (((3 / 2 : ℝ) * x ^ 2 - x ^ 2) *
        ((3 / 2 : ℝ) * x ^ 2 - 2 * x ^ 2)) <
        ((0 : ℝ) - 0 ^ 2) * ((0 : ℝ) - 2 * 0 ^ 2)
      have hx4 : 0 < x ^ 4 := pow_pos hxpos 4
      nlinarith

#print axioms GroundTruth.calculus_30_3_1_conjecture_1_certificate


theorem GroundTruth.calculus_30_3_1_conjecture_2_certificate :
¬ (
∀ f : (ℝ × ℝ) → ℝ, (DifferentiableAt ℝ f (0 : ℝ × ℝ) ∧ fderiv ℝ f (0 : ℝ × ℝ) = 0 ∧
  (∀ δ : ℝ, 0 < δ → ∃ x y : ℝ × ℝ, ‖x‖ < δ ∧ ‖y‖ < δ ∧ f x < f 0 ∧ f 0 < f y)) →
  ∃ θ φ : Fin 2 → ℝ,
  (0 ≤ θ 0 ∧ θ 0 < 2*Real.pi) ∧
  (∀ i, θ i < φ i) ∧
  (∀ i j, i < j → φ i < θ j) ∧
  φ (Fin.last 1) < θ 0 + 2*Real.pi ∧
  (∀ i, ∃ δ : ℝ, 0 < δ ∧ MonotoneOn (fun t : ℝ => f (t * Real.cos (θ i), t * Real.sin (θ i))) (Set.Icc 0 δ)) ∧
  (∀ i, ∃ δ : ℝ, 0 < δ ∧ AntitoneOn (fun t : ℝ => f (t * Real.cos (φ i), t * Real.sin (φ i))) (Set.Icc 0 δ))
) := by
  rintro h
  let f : (ℝ × ℝ) → ℝ := fun p => (p.2 - p.1 ^ 2) * (p.2 - 2 * p.1 ^ 2)
  have hfd : HasFDerivAt f (0 : (ℝ × ℝ) →L[ℝ] ℝ) (0 : ℝ × ℝ) := by
    dsimp [f]
    convert
      (((hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : ℝ × ℝ))).sub
          ((hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : ℝ × ℝ))).pow 2)).mul
        ((hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : ℝ × ℝ))).sub
          ((hasFDerivAt_const (𝕜 := ℝ) (x := (0 : ℝ × ℝ)) (c := (2 : ℝ))).mul
            ((hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : ℝ × ℝ))).pow 2)))) using 1 <;>
      simp
  have hsaddle :
      DifferentiableAt ℝ f (0 : ℝ × ℝ) ∧
        fderiv ℝ f (0 : ℝ × ℝ) = 0 ∧
        ∀ δ : ℝ, 0 < δ →
          ∃ x y : ℝ × ℝ,
            ‖x‖ < δ ∧ ‖y‖ < δ ∧ f x < f 0 ∧ f 0 < f y := by
    refine ⟨hfd.differentiableAt, hfd.fderiv, ?_⟩
    intro δ hδ
    let q : ℝ := min δ 1 / 4
    have hmin : 0 < min δ 1 := lt_min hδ zero_lt_one
    have hq : 0 < q := by dsimp [q]; positivity
    have hqδ : q < δ := by
      dsimp [q]
      have hm : min δ 1 ≤ δ := min_le_left _ _
      nlinarith
    have hq1 : q ≤ 1 / 4 := by
      dsimp [q]
      have hm : min δ 1 ≤ 1 := min_le_right _ _
      nlinarith
    refine ⟨(q, (3 / 2 : ℝ) * q ^ 2), (q, 0), ?_, ?_, ?_, ?_⟩
    · rw [Prod.norm_def]
      simp only [Real.norm_eq_abs, abs_of_pos hq]
      have hsecond : (3 / 2 : ℝ) * q ^ 2 < q := by nlinarith [sq_nonneg q]
      have habs : |(3 / 2 : ℝ) * q ^ 2| < δ := by
        rw [abs_of_nonneg]
        · exact lt_trans hsecond hqδ
        · positivity
      exact max_lt hqδ habs
    · rw [Prod.norm_def]
      simpa [Real.norm_eq_abs, abs_of_pos hq, hqδ] using hδ
    · dsimp [f]
      nlinarith [pow_pos hq 4]
    · dsimp [f]
      nlinarith [pow_pos hq 4]
  obtain ⟨θ, φ, hθ, hθφ, hsep, hlast, hmono, hanti⟩ := h f hsaddle
  obtain ⟨δ, hδ, ha⟩ := hanti (0 : Fin 2)
  let a : ℝ := Real.cos (φ (0 : Fin 2))
  let b : ℝ := Real.sin (φ (0 : Fin 2))
  have hab : a ^ 2 + b ^ 2 = 1 := by
    dsimp [a, b]
    nlinarith [Real.sin_sq_add_cos_sq (φ (0 : Fin 2))]
  by_cases hbpos : 0 < b
  · let t : ℝ := min (δ / 2) (b / (4 * (a ^ 2 + 1)))
    have hden : 0 < 4 * (a ^ 2 + 1) := by positivity
    have ht : 0 < t := by
      dsimp [t]
      apply lt_min
      · linarith
      · positivity
    have htδ : t ≤ δ := by
      dsimp [t]
      have hm : min (δ / 2) (b / (4 * (a ^ 2 + 1))) ≤ δ / 2 := min_le_left _ _
      linarith
    have htbound : t * a ^ 2 < b / 4 := by
      have hm : t ≤ b / (4 * (a ^ 2 + 1)) := by
        dsimp [t]
        exact min_le_right _ _
      have ha2 : a ^ 2 < a ^ 2 + 1 := by linarith
      calc
        t * a ^ 2 < t * (a ^ 2 + 1) := mul_lt_mul_of_pos_left ha2 ht
        _ ≤ (b / (4 * (a ^ 2 + 1))) * (a ^ 2 + 1) :=
          mul_le_mul_of_nonneg_right hm (by positivity)
        _ = b / 4 := by field_simp <;> ring
    have htmem : t ∈ Set.Icc (0 : ℝ) δ := ⟨le_of_lt ht, htδ⟩
    have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) δ := ⟨le_rfl, le_of_lt hδ⟩
    have hle := ha hzero htmem (le_of_lt ht)
    have hpositive : 0 < f (t * a, t * b) := by
      have hpa : 0 < b-t*a^2 := by linarith
      have hpb : 0 < b-2*t*a^2 := by linarith
      have he : f (t*a,t*b) = (t*(b-t*a^2))*(t*(b-2*t*a^2)) := by dsimp [f]; ring
      rw [he]
      exact mul_pos (mul_pos ht hpa) (mul_pos ht hpb)
    have hrewrite :
        f (t * Real.cos (φ (0 : Fin 2)), t * Real.sin (φ (0 : Fin 2))) =
          f (t * a, t * b) := by rfl
    dsimp only at hle
    rw [hrewrite] at hle
    have hfzero : f (0 * Real.cos (φ (0 : Fin 2)), 0 * Real.sin (φ (0 : Fin 2))) = 0 := by
      simp [f]
    rw [hfzero] at hle
    linarith
  · have hb : b ≤ 0 := le_of_not_gt hbpos
    let t : ℝ := δ / 2
    have ht : 0 < t := by dsimp [t]; linarith
    have htδ : t ≤ δ := by dsimp [t]; linarith
    have htmem : t ∈ Set.Icc (0 : ℝ) δ := ⟨le_of_lt ht, htδ⟩
    have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) δ := ⟨le_rfl, le_of_lt hδ⟩
    have hle := ha hzero htmem (le_of_lt ht)
    have hpositive : 0 < f (t * a, t * b) := by
      have htb : t*b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.le hb
      by_cases ha0 : a = 0
      · have hbneg : b < 0 := by rw [ha0] at hab; nlinarith
        have htbneg : t*b < 0 := mul_neg_of_pos_of_neg ht hbneg
        dsimp [f]
        rw [ha0]
        simp only [mul_zero, zero_pow, OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, sub_zero]
        exact mul_pos_of_neg_of_neg htbneg htbneg
      · have hta : 0 < (t*a)^2 := sq_pos_of_ne_zero (mul_ne_zero ht.ne' ha0)
        have h1 : t*b-(t*a)^2 < 0 := by linarith
        have h2 : t*b-2*(t*a)^2 < 0 := by linarith
        exact mul_pos_of_neg_of_neg h1 h2
    have hrewrite :
        f (t * Real.cos (φ (0 : Fin 2)), t * Real.sin (φ (0 : Fin 2))) =
          f (t * a, t * b) := by rfl
    dsimp only at hle
    rw [hrewrite] at hle
    have hfzero : f (0 * Real.cos (φ (0 : Fin 2)), 0 * Real.sin (φ (0 : Fin 2))) = 0 := by
      simp [f]
    rw [hfzero] at hle
    linarith

#print axioms GroundTruth.calculus_30_3_1_conjecture_2_certificate


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


theorem GroundTruth.calculus_37_3_1_a_certificate :
Function.Injective (fun z : ℝ × ℝ => ((3 : ℝ)*z.1+(-4 : ℝ)*z.2, (1 : ℝ)*z.1+(5 : ℝ)*z.2)) := by
  intro x y h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  apply Prod.ext <;> dsimp at * <;> linarith

#print axioms GroundTruth.calculus_37_3_1_a_certificate


theorem GroundTruth.calculus_37_3_1_b_certificate :
Function.Surjective (fun z : ℝ × ℝ => ((3 : ℝ)*z.1+(-4 : ℝ)*z.2, (1 : ℝ)*z.1+(5 : ℝ)*z.2)) := by
  intro y
  refine ⟨((5*y.1+4*y.2)/19, (-y.1+3*y.2)/19), ?_⟩
  apply Prod.ext <;> dsimp <;> ring

#print axioms GroundTruth.calculus_37_3_1_b_certificate


theorem GroundTruth.calculus_37_3_2_certificate :
∃ x y : ℝ × ℝ, x ≠ y ∧ (fun z : ℝ × ℝ => (z.1^2-z.2^2, 2*z.1*z.2)) x = (fun z : ℝ × ℝ => (z.1^2-z.2^2, 2*z.1*z.2)) y := by
  refine ⟨(0,1), (0,-1), ?_, ?_⟩ <;> norm_num

#print axioms GroundTruth.calculus_37_3_2_certificate


theorem GroundTruth.calculus_37_3_3_a_certificate :
Function.Injective (fun z : ℝ × ℝ => ((4 : ℝ)*z.1+(13 : ℝ)*z.2, (2 : ℝ)*z.1+(7 : ℝ)*z.2)) := by
  intro x y h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  apply Prod.ext <;> dsimp at * <;> linarith

#print axioms GroundTruth.calculus_37_3_3_a_certificate


theorem GroundTruth.calculus_37_3_3_b_certificate :
Function.Surjective (fun z : ℝ × ℝ => ((4 : ℝ)*z.1+(13 : ℝ)*z.2, (2 : ℝ)*z.1+(7 : ℝ)*z.2)) := by
  intro y
  refine ⟨((7*y.1-13*y.2)/2, (-2*y.1+4*y.2)/2), ?_⟩
  apply Prod.ext <;> dsimp <;> ring

#print axioms GroundTruth.calculus_37_3_3_b_certificate


theorem GroundTruth.calculus_37_3_4_a_certificate :
∃ x y : ℝ × ℝ, x ≠ y ∧ (fun z : ℝ × ℝ => ((8 : ℝ)*z.1+(12 : ℝ)*z.2, (6 : ℝ)*z.1+(9 : ℝ)*z.2)) x = (fun z : ℝ × ℝ => ((8 : ℝ)*z.1+(12 : ℝ)*z.2, (6 : ℝ)*z.1+(9 : ℝ)*z.2)) y := by
  refine ⟨(0,0), (3,-2), ?_, ?_⟩ <;> norm_num

#print axioms GroundTruth.calculus_37_3_4_a_certificate


theorem GroundTruth.calculus_37_3_4_b_certificate :
∃ y : ℝ × ℝ, ∀ x : ℝ × ℝ, (fun z : ℝ × ℝ => ((8 : ℝ)*z.1+(12 : ℝ)*z.2, (6 : ℝ)*z.1+(9 : ℝ)*z.2)) x ≠ y := by
  refine ⟨(0,1), ?_⟩
  intro x h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  dsimp at *
  linarith

#print axioms GroundTruth.calculus_37_3_4_b_certificate
