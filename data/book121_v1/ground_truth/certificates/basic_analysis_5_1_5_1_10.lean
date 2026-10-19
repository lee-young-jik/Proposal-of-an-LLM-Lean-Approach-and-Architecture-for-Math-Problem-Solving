import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 600000
set_option maxRecDepth 2048

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
