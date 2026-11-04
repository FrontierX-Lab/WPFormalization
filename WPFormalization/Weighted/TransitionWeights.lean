import WPFormalization.Weighted.Clipping
import WPFormalization.Weighted.LinearBudget
/-! Actual clipped-weight merger savings and nonseparating birth costs.
These are finite count/product estimates for the original clippedWeight; the
exceptional node-pair count is proved to be at most four. -/
noncomputable section
namespace WP
lemma zeros_cons_eq (p : ℕ) (d : List ℕ) : zeros (p :: d) = zeros d+if p=0 then 1 else 0 := by
  unfold zeros
  by_cases hp : p=0 <;> simp [hp]
lemma inactive_cons_eq (p : ℕ) (d : List ℕ) : inactive (p :: d) = inactive d+if p≤1 then 1 else 0 := by
  unfold inactive
  by_cases hp : p≤1 <;> simp [hp]
lemma clippedWeight_perm (c : ℝ) {d e : List ℕ} (hp : d.Perm e) : clippedWeight c d = clippedWeight c e := by
  rw [clippedWeight_phi,clippedWeight_phi,zeros_perm hp,inactive_perm hp]
lemma clippedWeight_ratio_mono_counts (c : ℝ) (parent child : List ℕ)
    (hz : zeros child ≤ zeros parent) (hi : inactive child ≤ inactive parent) :
    clippedWeight c child/clippedWeight c parent ≤ 1 := by
  apply (div_le_one (clippedWeight_pos c parent)).mpr
  rw [clippedWeight_phi,clippedWeight_phi]
  exact mul_le_mul (pow_le_pow_right₀ (by norm_num) hz) (clippedPhi_mono c hi)
    (clippedPhi_pos c _).le (by positivity)
lemma clippedPhi_delete_ratio (c : ℝ) (I : ℕ) (hI : 1 ≤ I) :
    clippedPhi c (I-1)/clippedPhi c I = 1/max 1 (c*Real.sqrt I) := by
  have hidx : I-1+1=I := by omega
  have hcast : ((I-1 : ℕ) : ℝ)+1 = I := by exact_mod_cast hidx
  have hphi := clippedPhi_succ c (I-1)
  rw [hidx,hcast] at hphi
  rw [hphi]
  field_simp [(clippedPhi_pos c (I-1)).ne']
lemma clippedWeight_ratio_delete_inactive (c : ℝ) (parent child : List ℕ)
    (hz : zeros child ≤ zeros parent) (hi : inactive child+1 ≤ inactive parent) :
    clippedWeight c child/clippedWeight c parent ≤ 1/max 1 (c*Real.sqrt (inactive parent)) := by
  have hI : 1 ≤ inactive parent := by omega
  have hraw : clippedWeight c child ≤ (4 : ℝ)^(zeros parent)*clippedPhi c (inactive parent-1) := by
    rw [clippedWeight_phi]
    exact mul_le_mul (pow_le_pow_right₀ (by norm_num) hz) (clippedPhi_mono c (by omega))
      (clippedPhi_pos c _).le (by positivity)
  calc
    _ ≤ ((4 : ℝ)^(zeros parent)*clippedPhi c (inactive parent-1))/clippedWeight c parent :=
      div_le_div_of_nonneg_right hraw (clippedWeight_pos c parent).le
    _ = clippedPhi c (inactive parent-1)/clippedPhi c (inactive parent) := by
      rw [clippedWeight_phi]
      field_simp
    _ = _ := clippedPhi_delete_ratio c _ hI
lemma clippedWeight_ratio_birth (c : ℝ) (hc : 0 ≤ c) (parent child : List ℕ)
    (hz : zeros child ≤ zeros parent+2) (hi : inactive child ≤ inactive parent+2) :
    clippedWeight c child/clippedWeight c parent ≤
      16*(1+c*Real.sqrt (inactive parent+2))^2 := by
  let I := inactive parent
  have hraw : clippedWeight c child ≤ (4 : ℝ)^(zeros parent+2)*clippedPhi c (I+2) := by
    rw [clippedWeight_phi]
    exact mul_le_mul (pow_le_pow_right₀ (by norm_num) hz) (clippedPhi_mono c hi)
      (clippedPhi_pos c _).le (by positivity)
  have hmax₁ : max 1 (c*Real.sqrt (I+1)) ≤ 1+c*Real.sqrt (I+2) := by
    apply max_le (by exact le_add_of_nonneg_right (mul_nonneg hc (Real.sqrt_nonneg _)))
    have hs : Real.sqrt ((I : ℝ)+1) ≤ Real.sqrt ((I : ℝ)+2) := Real.sqrt_le_sqrt (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hs hc]
  have hmax₂ : max 1 (c*Real.sqrt (I+2)) ≤ 1+c*Real.sqrt (I+2) := by
    apply max_le (by exact le_add_of_nonneg_right (mul_nonneg hc (Real.sqrt_nonneg _)))
    linarith
  calc
    _ ≤ ((4 : ℝ)^(zeros parent+2)*clippedPhi c (I+2))/clippedWeight c parent :=
      div_le_div_of_nonneg_right hraw (clippedWeight_pos c parent).le
    _ = 16*(max 1 (c*Real.sqrt (I+1))*max 1 (c*Real.sqrt (I+2))) := by
      rw [clippedWeight_phi,show I+2=(I+1)+1 by omega,clippedPhi_succ,clippedPhi_succ,pow_add]
      norm_num
      dsimp only [I]
      field_simp [(clippedPhi_pos c (inactive parent)).ne']
      <;> ring
    _ ≤ _ := by
      have he := mul_le_mul hmax₁ hmax₂ (le_trans (by norm_num) (le_max_left _ _)) (by positivity)
      nlinarith [he]
lemma contraction_weight_nonincrease (c : ℝ) (pivot u v : ℕ) (d : List ℕ)
    (hu : 2 ≤ u) (hv : 2 ≤ v) :
    clippedWeight c (u :: v :: d)/clippedWeight c (pivot :: d) ≤ 1 := by
  apply clippedWeight_ratio_mono_counts
  · simp only [zeros_cons_eq,show u≠0 by omega,show v≠0 by omega,ite_false,add_zero]
    omega
  · simp only [inactive_cons_eq,show ¬ u≤1 by omega,show ¬ v≤1 by omega,ite_false,add_zero]
    omega
lemma contraction_weight_birth (c : ℝ) (hc : 0 ≤ c) (pivot u v : ℕ) (d : List ℕ) :
    clippedWeight c (u :: v :: d)/clippedWeight c (pivot :: d) ≤
      16*(1+c*Real.sqrt (inactive (pivot :: d)+2))^2 := by
  apply clippedWeight_ratio_birth c hc
  · have h₁ := zeros_cons_bounds u (v :: d)
    have h₂ := zeros_cons_bounds v d
    have hp := zeros_cons_bounds pivot d
    omega
  · have h₁ := inactive_cons_bounds u (v :: d)
    have h₂ := inactive_cons_bounds v d
    have hp := inactive_cons_bounds pivot d
    omega
lemma counts_antitone_head (q k : ℕ) (d : List ℕ) (hqk : q ≤ k) :
    zeros (k :: d) ≤ zeros (q :: d) ∧ inactive (k :: d) ≤ inactive (q :: d) := by
  constructor
  · simp only [zeros_cons_eq]
    split_ifs <;> omega
  · simp only [inactive_cons_eq]
    split_ifs <;> omega
lemma merger_weight_nonincrease (c : ℝ) (pivot q l : ℕ) (d : List ℕ) (hp : 1 ≤ pivot) :
    clippedWeight c ((pivot+q+l-1) :: d)/clippedWeight c (pivot :: q :: d) ≤ 1 := by
  have he := counts_antitone_head q (pivot+q+l-1) d (by omega)
  apply clippedWeight_ratio_mono_counts
  · exact he.1.trans (zeros_cons_bounds pivot (q :: d)).1
  · exact he.2.trans (inactive_cons_bounds pivot (q :: d)).1
lemma active_inactive_merger_weight (c : ℝ) (pivot q l : ℕ) (d : List ℕ)
    (hp : 2 ≤ pivot) (hq : q ≤ 1) :
    clippedWeight c ((pivot+q+l-1) :: d)/clippedWeight c (pivot :: q :: d) ≤
      inactiveMergeRatio c (inactive (pivot :: q :: d)) := by
  by_cases hk : pivot+q+l-1 ≤ 1
  · have hp2 : pivot=2 := by omega
    have hq0 : q=0 := by omega
    have hl0 : l=0 := by omega
    subst pivot; subst q; subst l
    norm_num only [show (2+0+0-1 : ℕ)=1 by decide]
    have he : clippedWeight c (1 :: d)/clippedWeight c (2 :: 0 :: d) = 1/4 := by
      rw [clippedWeight_phi,clippedWeight_phi]
      norm_num [zeros_cons_eq,inactive_cons_eq]
      rw [pow_succ]
      field_simp [(clippedPhi_pos c (inactive d+1)).ne']
    rw [he]
    exact le_max_left _ _
  · have hk₂ : 2 ≤ pivot+q+l-1 := by omega
    have he := counts_antitone_head q (pivot+q+l-1) d (by omega)
    have hi : inactive ((pivot+q+l-1) :: d)+1 ≤ inactive (pivot :: q :: d) := by
      simp only [inactive_cons_eq,show ¬ pivot≤1 by omega,show ¬ pivot+q+l-1≤1 by omega,
        hq,ite_false,ite_true,add_zero]
      omega
    have hz := he.1.trans (zeros_cons_bounds pivot (q :: d)).1
    exact (clippedWeight_ratio_delete_inactive c _ _ hz hi).trans (le_max_right _ _)
lemma one_pivot_merger_weight (c : ℝ) (q l : ℕ) (d : List ℕ) :
    clippedWeight c ((q+l) :: d)/clippedWeight c (1 :: q :: d) ≤
      inactiveMergeRatio c (inactive (1 :: q :: d)) := by
  have he := counts_antitone_head q (q+l) d (by omega)
  have hi : inactive ((q+l) :: d)+1 ≤ inactive (1 :: q :: d) := by
    simp only [inactive_cons_eq,show (1 : ℕ)≤1 by decide,ite_true]
    have htail := he.2
    simp only [inactive_cons_eq] at htail
    omega
  have hz := he.1.trans (zeros_cons_bounds 1 (q :: d)).1
  exact (clippedWeight_ratio_delete_inactive c _ _ hz hi).trans (le_max_right _ _)
lemma zero_pivot_merger_weight (c : ℝ) (k : ℕ) (d : List ℕ) :
    clippedWeight c (k :: d)/clippedWeight c (0 :: 0 :: d) ≤
      inactiveMergeRatio c (inactive (0 :: 0 :: d)) := by
  have hi : inactive (k :: d)+1 ≤ inactive (0 :: 0 :: d) := by
    simp only [inactive_cons_eq,show (0 : ℕ)≤1 by decide,ite_true]
    split_ifs <;> omega
  have hz : zeros (k :: d) ≤ zeros (0 :: 0 :: d) := by
    simp only [zeros_cons_eq,ite_true]
    split_ifs <;> omega
  exact (clippedWeight_ratio_delete_inactive c _ _ hz hi).trans (le_max_right _ _)
def inactivePairIndices (K : ℕ) : Finset ℕ :=
  (Finset.range K).filter (fun u => u ≤ 1 ∨ K-1-u ≤ 1)
lemma inactivePairIndices_card (K : ℕ) : (inactivePairIndices K).card ≤ 4 := by
  have hsub : inactivePairIndices K ⊆ {0,1,K-2,K-1} := by
    intro u hu
    obtain ⟨hu,hcase⟩ := Finset.mem_filter.mp hu
    have hu' := Finset.mem_range.mp hu
    simp only [Finset.mem_insert,Finset.mem_singleton]
    rcases hcase with hcase | hcase
    · omega
    · omega
  have h₁ := Finset.card_insert_le (0 : ℕ) ({1,K-2,K-1} : Finset ℕ)
  have h₂ := Finset.card_insert_le (1 : ℕ) ({K-2,K-1} : Finset ℕ)
  have h₃ := Finset.card_insert_le (K-2) ({K-1} : Finset ℕ)
  simp only [Finset.card_singleton] at h₃
  have hcard := Finset.card_le_card hsub
  omega
lemma sum_contraction_weight_upper (K : ℕ) (f : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hall : ∀ u ∈ Finset.range K, f u ≤ B)
    (hactive : ∀ u ∈ Finset.range K, 2 ≤ u → 2 ≤ K-1-u → f u ≤ 1) :
    (∑ u ∈ Finset.range K, f u) ≤ (K : ℝ)+4*B := by
  have hterm : ∀ u ∈ Finset.range K,
      f u ≤ 1+(if u ≤ 1 ∨ K-1-u ≤ 1 then B else 0) := by
    intro u hu
    by_cases hbad : u ≤ 1 ∨ K-1-u ≤ 1
    · rw [if_pos hbad]
      linarith [hall u hu]
    · rw [if_neg hbad,add_zero]
      exact hactive u hu (by omega) (by omega)
  have hs := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib] at hs
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one] at hs
  have hbad : (∑ u ∈ Finset.range K, if u ≤ 1 ∨ K-1-u ≤ 1 then B else 0) ≤ 4*B := by
    rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ hB
    exact_mod_cast inactivePairIndices_card K
  linarith
end WP
