import Mathlib
open scoped Matrix
set_option autoImplicit false
noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem JudsonGold.judson_9_4_18_certificate :
let u : ℚˣ := Units.mk0 (2 : ℚ) (by norm_num);
  let v : ℚˣ := Units.mk0 (3 : ℚ) (by norm_num);
  let A := Subgroup.zpowers u;
  let B := Subgroup.zpowers v;
  ∃ H : Subgroup ℚˣ,
    (∀ x : ℚˣ, x ∈ H ↔ ∃ m n : ℤ, x = u ^ m * v ^ n) ∧
    A ≤ H ∧ B ≤ H ∧
    (∀ a : A, ∀ b : B, (a : ℚˣ) * (b : ℚˣ) = (b : ℚˣ) * (a : ℚˣ)) ∧
    (∀ x : H, ∃! p : A × B, (x : ℚˣ) = (p.1 : ℚˣ) * (p.2 : ℚˣ)) ∧
    Nonempty (Multiplicative (ℤ × ℤ) ≃* H) := by
  dsimp only
  let u : ℚˣ := Units.mk0 (2 : ℚ) (by norm_num)
  let v : ℚˣ := Units.mk0 (3 : ℚ) (by norm_num)
  let A := Subgroup.zpowers u
  let B := Subgroup.zpowers v
  change ∃ H : Subgroup ℚˣ, _
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hv : ∀ (p : ℕ) [Fact p.Prime] (q : ℚ), q ≠ 0 → ∀ k : ℤ,
      padicValRat p (q ^ k) = k * padicValRat p q := by
    intro p hp q hq k
    rcases Int.eq_nat_or_neg k with ⟨k, rfl | rfl⟩
    · simp [zpow_natCast, padicValRat.pow hq]
    · simp [zpow_neg, zpow_natCast, padicValRat.inv, padicValRat.pow hq]
  have h22 : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (by decide)
  have h33 : padicValRat 3 (3 : ℚ) = 1 := padicValRat.self (by decide)
  have h23 : padicValRat 2 (3 : ℚ) = 0 := by
    change padicValRat 2 ((3 : ℕ) : ℚ) = 0
    rw [padicValRat.of_nat, padicValNat_primes (by decide)]
    rfl
  have h32 : padicValRat 3 (2 : ℚ) = 0 := by
    change padicValRat 3 ((2 : ℕ) : ℚ) = 0
    rw [padicValRat.of_nat, padicValNat_primes (by decide)]
    rfl
  have hvp : ∀ (p : ℕ) [Fact p.Prime] (m n : ℤ),
      padicValRat p ((2 : ℚ)^m * (3 : ℚ)^n) = m * padicValRat p 2 + n * padicValRat p 3 := by
    intro p hp m n
    rw [padicValRat.mul (zpow_ne_zero m (by norm_num)) (zpow_ne_zero n (by norm_num)), hv, hv] <;> norm_num
  let f : Multiplicative (ℤ × ℤ) →* ℚˣ :=
    { toFun := fun p => u ^ p.toAdd.1 * v ^ p.toAdd.2
      map_one' := by simp
      map_mul' := by
        intro p q
        change u ^ (p.toAdd.1 + q.toAdd.1) * v ^ (p.toAdd.2 + q.toAdd.2) = _
        simp only [zpow_add]
        ac_rfl }
  have hf : Function.Injective f := by
    intro p q h
    have he : (2 : ℚ)^p.toAdd.1 * (3 : ℚ)^p.toAdd.2 =
        (2 : ℚ)^q.toAdd.1 * (3 : ℚ)^q.toAdd.2 := by
      have he := congrArg (fun w : ℚˣ => (w : ℚ)) h
      change ((u ^ p.toAdd.1 * v ^ p.toAdd.2 : ℚˣ) : ℚ) = ((u ^ q.toAdd.1 * v ^ q.toAdd.2 : ℚˣ) : ℚ) at he
      simpa only [Units.val_mul, Units.val_zpow_eq_zpow_val, u, v, Units.val_mk0] using he
    have h2 := congrArg (padicValRat 2) he
    have h3 := congrArg (padicValRat 3) he
    simp only [hvp, h22, h23, h32, h33, mul_one, mul_zero, zero_add, add_zero] at h2 h3
    exact Prod.ext h2 h3
  refine ⟨f.range, ?_, ?_, ?_, ?_, ?_, ⟨MonoidHom.ofInjective hf⟩⟩
  · intro x
    constructor
    · rintro ⟨p, hp⟩
      exact ⟨p.toAdd.1, p.toAdd.2, hp.symm⟩
    · rintro ⟨m,n,hx⟩
      exact ⟨Multiplicative.ofAdd (m,n), hx.symm⟩
  · intro x hx
    obtain ⟨m,hm⟩ := hx
    refine ⟨Multiplicative.ofAdd (m,0), ?_⟩
    change u ^ m * v ^ (0 : ℤ) = x
    simpa only [zpow_zero, mul_one] using hm
  · intro x hx
    obtain ⟨n,hn⟩ := hx
    refine ⟨Multiplicative.ofAdd (0,n), ?_⟩
    change u ^ (0 : ℤ) * v ^ n = x
    simpa only [zpow_zero, one_mul] using hn
  · intros
    exact mul_comm _ _
  · intro x
    obtain ⟨p,hp⟩ := x.property
    let a : A := ⟨u ^ p.toAdd.1, Subgroup.zpow_mem _ (Subgroup.mem_zpowers u) _⟩
    let b : B := ⟨v ^ p.toAdd.2, Subgroup.zpow_mem _ (Subgroup.mem_zpowers v) _⟩
    refine ⟨(a,b), hp.symm, ?_⟩
    intro q hq
    obtain ⟨m,hm⟩ := q.1.property
    obtain ⟨n,hn⟩ := q.2.property
    change u ^ m = (q.1 : ℚˣ) at hm
    change v ^ n = (q.2 : ℚˣ) at hn
    have hh : f (Multiplicative.ofAdd (m,n)) = f p := by
      change u ^ m * v ^ n = f p
      rw [hm,hn,hp]
      exact hq.symm
    have hc := hf hh
    apply Prod.ext
    · apply Subtype.ext
      change (q.1 : ℚˣ) = u ^ p.toAdd.1
      rw [← hm]
      exact congrArg (fun m : ℤ => u ^ m) (congrArg (fun t : Multiplicative (ℤ × ℤ) => t.toAdd.1) hc)
    · apply Subtype.ext
      change (q.2 : ℚˣ) = v ^ p.toAdd.2
      rw [← hn]
      exact congrArg (fun n : ℤ => v ^ n) (congrArg (fun t : Multiplicative (ℤ × ℤ) => t.toAdd.2) hc)

#print axioms JudsonGold.judson_9_4_18_certificate
