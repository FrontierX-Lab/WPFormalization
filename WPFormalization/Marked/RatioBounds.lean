import WPFormalization.Statements.Marked
import WPFormalization.Intersection.NormalizedContinuity
import WPFormalization.Analysis.QuadraticRemainder
/-! The genuine cusp and genus-exchange inequalities of Section 6.
The canonical dilaton coefficients come from the actual normalized H kernel.
Joint continuity and the proved finite-background continuity extend the
canonical identity to the critical endpoint; no physical r(y₀) branch is
used there. The uniform absolute coefficient sum follows from Cauchy on
radius two. The W inequalities then use actual nonnegativity, degree
monotonicity, and the genuine shifted dilaton/KdV identities. -/
noncomputable section
open Set
namespace WP

lemma barH_realCoeff_continuous (n : ℕ) :
    Continuous (fun Y : Icc (0:ℝ) y₀ => realCoeff (barH (Y:ℝ)) n) := by
  have hc := Analysis.parameter_coeff_continuous
    (fun Y : Icc (0:ℝ) y₀ => barH (Y:ℝ)) 1 (by norm_num)
    (fun Y => (barH_differentiable (Y:ℝ)).differentiableOn)
    (Analysis.barH_joint_continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) n
  exact Complex.continuous_re.comp hc

def canonicalDilatonCoefficient (Y : ℝ) (d : ℕ) : ℝ :=
  if 1 ≤ d then realCoeff (barH Y) (d-1)/3 else 0

lemma canonicalDilatonCoefficient_continuous (d : ℕ) :
    Continuous (fun Y : Icc (0:ℝ) y₀ => canonicalDilatonCoefficient Y d) := by
  by_cases hd : 1 ≤ d
  · simpa only [canonicalDilatonCoefficient,if_pos hd] using
      (barH_realCoeff_continuous (d-1)).div_const 3
  · simp only [canonicalDilatonCoefficient,if_neg hd]
    exact continuous_const

lemma canonical_shifted_dilaton_closed (P : PsiTheory) (g p : ℕ)
    (hs : Stable g p) (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    (complexity g p:ℝ) * normalized P g (List.replicate p 0) Y =
      ∑ d ∈ Finset.range (dimension g (p+1)+1),
        canonicalDilatonCoefficient Y d * normalized P g (d::List.replicate p 0) Y := by
  let L (Y : ℝ) := (complexity g p:ℝ) * normalized P g (List.replicate p 0) Y
  let R (Y : ℝ) := ∑ d ∈ Finset.range (dimension g (p+1)+1),
    canonicalDilatonCoefficient Y d * normalized P g (d::List.replicate p 0) Y
  have hL : ContinuousOn L (Icc 0 y₀) := by
    apply continuousOn_iff_continuous_restrict.mpr
    exact continuous_const.mul (normalized_continuous P g _)
  have hR : ContinuousOn R (Icc 0 y₀) := by
    apply continuousOn_iff_continuous_restrict.mpr
    apply continuous_finsetSum
    intro d hd
    exact (canonicalDilatonCoefficient_continuous d).mul (normalized_continuous P g _)
  have heq : Set.EqOn L R (Ico 0 y₀) := by
    intro Y hY
    have hi := shifted_dilaton P g p hs Y hY
    dsimp only [L,R]
    rw [hi]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hd1 : 1 ≤ d
    · simp only [canonicalDilatonCoefficient,hd1,ite_true]
      rw [dilaton_coefficient Y hY d hd1]
    · simp [canonicalDilatonCoefficient,hd1]
  exact heq.of_subset_closure hL hR Ico_subset_Icc_self
    (by rw [closure_Ico y₀_pos.ne]) hY

lemma barH_realCoeff_abs_sum_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ Y ∈ Icc (0:ℝ) y₀, ∀ N : ℕ, ∑ n ∈ Finset.range N, |realCoeff (barH Y) n| ≤ C := by
  have hc : Continuous (fun p : Icc (0:ℝ) y₀ × Metric.closedBall (0:ℂ) 2 => barH (p.1:ℝ) p.2) :=
    Analysis.barH_joint_continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  obtain ⟨M,hM⟩ := isCompact_univ.bddAbove_image hc.norm.continuousOn
  let B := max M 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨2*B,by positivity,?_⟩
  intro Y hY N
  have hcircle : ∀ z ∈ Metric.sphere (0:ℂ) 2, ‖barH Y z‖ ≤ B := by
    intro z hz
    have hz' := Metric.sphere_subset_closedBall hz
    exact (hM (mem_image_of_mem _
      (show (⟨Y,hY⟩,⟨z,hz'⟩) ∈ (univ : Set (Icc (0:ℝ) y₀ × Metric.closedBall (0:ℂ) 2)) from mem_univ _))).trans
      (le_max_left _ _)
  calc
    _ ≤ ∑ n ∈ Finset.range N, B/2^n := by
      apply Finset.sum_le_sum
      intro n hn
      exact (Complex.abs_re_le_norm _).trans
        (Analysis.coeff_norm_le_circle_bound (barH Y) 2 B (by norm_num)
          (barH_differentiable Y).differentiableOn hcircle n)
    _ = B * ∑ n ∈ Finset.range N, (1/2:ℝ)^n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [div_pow,one_pow]
      ring
    _ ≤ 2*B := by nlinarith [sum_geometric_two_le N]

lemma canonicalDilatonCoefficient_abs_sum_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ Y ∈ Icc (0:ℝ) y₀, ∀ N : ℕ,
      ∑ d ∈ Finset.range N, |canonicalDilatonCoefficient Y d| ≤ C := by
  obtain ⟨C,hC,hbound⟩ := barH_realCoeff_abs_sum_uniform
  refine ⟨C,hC,?_⟩
  intro Y hY N
  cases N with
  | zero => simpa using hC.le
  | succ N =>
    rw [Finset.sum_range_succ']
    simp only [canonicalDilatonCoefficient,Nat.add_sub_cancel,Nat.le_add_left,
      if_true,if_false,zero_add]
    have he : (∑ k ∈ Finset.range N, |realCoeff (barH Y) k/3|) ≤ C/3 := by
      simp only [abs_div,abs_of_pos (by norm_num : (0:ℝ)<3)]
      rw [←Finset.sum_div]
      exact div_le_div_of_nonneg_right (hbound Y hY N) (by norm_num)
    simpa using he.trans (by linarith : C/3 ≤ C)

lemma W_cusp_uniform_bound : ∃ C : ℝ, 0 < C ∧ ∀ P : PsiTheory, ∀ g p : ℕ,
    Stable g p → ∀ Y ∈ Icc (0:ℝ) y₀,
      (complexity g p:ℝ) * W P g p Y ≤ C * W P g (p+1) Y := by
  obtain ⟨C,hC,hbound⟩ := canonicalDilatonCoefficient_abs_sum_uniform
  refine ⟨C,hC,?_⟩
  intro P g p hs Y hY
  have hs' : Stable g (p+1) := by unfold Stable at *;omega
  have hz : 0 ≤ normalized P g (List.replicate (p+1) 0) Y :=
    normalized_nonneg_nonempty P g _ (by simp) Y hY
  have hterm (d : ℕ) : canonicalDilatonCoefficient Y d * normalized P g (d::List.replicate p 0) Y ≤
      |canonicalDilatonCoefficient Y d| * normalized P g (List.replicate (p+1) 0) Y := by
    have hn := normalized_nonneg_nonempty P g (d::List.replicate p 0) (by simp) Y hY
    have hl := normalized_le_all_zero P g (d::List.replicate p 0) (by simpa using hs') Y hY
    simp only [List.length_cons,List.length_replicate] at hl
    exact (mul_le_mul_of_nonneg_right (le_abs_self _) hn).trans
      (mul_le_mul_of_nonneg_left hl (abs_nonneg _))
  have hnorm : (complexity g p:ℝ) * normalized P g (List.replicate p 0) Y ≤
      C * normalized P g (List.replicate (p+1) 0) Y := by
    rw [canonical_shifted_dilaton_closed P g p hs Y hY]
    calc
      _ ≤ ∑ d ∈ Finset.range (dimension g (p+1)+1),
          |canonicalDilatonCoefficient Y d| * normalized P g (List.replicate (p+1) 0) Y :=
        Finset.sum_le_sum (fun d _ => hterm d)
      _ = (∑ d ∈ Finset.range (dimension g (p+1)+1), |canonicalDilatonCoefficient Y d|) *
          normalized P g (List.replicate (p+1) 0) Y := by rw [Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (hbound Y hY _) hz
  unfold W
  nlinarith [mul_le_mul_of_nonneg_left hnorm (show 0 ≤ (4:ℝ)^g by positivity)]

lemma W_genus_exchange_le (P : PsiTheory) (g p : ℕ) (hg : 1 ≤ g) (hp : 2 ≤ p)
    (Y : ℝ) (hY : Y ∈ Icc 0 y₀) : W P (g-1) (p+2) Y ≤ W P g p Y := by
  have hs : Stable g p := by unfold Stable;omega
  have hdlen : (1::List.replicate (p-1) 0).length=p := by simp;omega
  have hmono := normalized_le_all_zero P g (1::List.replicate (p-1) 0)
    (by rwa [hdlen]) Y hY
  rw [hdlen] at hmono
  have hsep : 0 ≤ ∑ j ∈ Finset.range (g+1), ∑ s ∈ Finset.range (p-1),
      (Nat.choose (p-2) s:ℝ)*normalized P j (List.replicate (s+2) 0) Y *
        normalized P (g-j) (List.replicate (p-s) 0) Y := by
    apply Finset.sum_nonneg
    intro j hj
    apply Finset.sum_nonneg
    intro s hs
    have hs' := Finset.mem_range.mp hs
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (normalized_nonneg_nonempty P j _ (by simp) Y hY))
      (normalized_nonneg_nonempty P (g-j) _ (by simp;omega) Y hY)
  have hk := shifted_kdv P g p hg hp Y hY
  have hnorm : normalized P (g-1) (List.replicate (p+2) 0) Y ≤
      4*normalized P g (List.replicate p 0) Y := by nlinarith
  have hpow : (4:ℝ)^(g-1)*4=(4:ℝ)^g := by rw [←pow_succ,Nat.sub_add_cancel hg]
  unfold W
  calc
    _ ≤ (4:ℝ)^(g-1)*(4*normalized P g (List.replicate p 0) Y) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := by rw [←mul_assoc,hpow]
end WP
