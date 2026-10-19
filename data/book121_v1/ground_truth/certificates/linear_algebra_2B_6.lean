import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 600000
set_option maxRecDepth 2048

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
