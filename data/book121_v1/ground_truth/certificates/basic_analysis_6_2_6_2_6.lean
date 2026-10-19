import Mathlib
open Filter
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

set_option maxHeartbeats 600000
set_option maxRecDepth 2048

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
