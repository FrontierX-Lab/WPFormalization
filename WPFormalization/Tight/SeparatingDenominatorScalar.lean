import WPFormalization.Tight.SeparatingScale
import WPFormalization.Analysis.RatioSaddleCurvature

noncomputable section
namespace WP.TightSeparating
open Set

lemma unmarked_model_derivative_identity (g : ℕ) (hg : 2 ≤ g)
    (Y : ℝ) (hY : Y ∈ Ico (0 : ℝ) y₀) :
    XR Y*markedModel g 1 Y = markedModel g 0 Y*
      ((complexity g 0 : ℝ)*Psi (XR Y))*
        Real.sqrt ((complexity g 0 : ℝ)/(complexity g 0+1 : ℕ)) := by
  have hs : Stable g 0 := by unfold Stable;omega
  rw [show 1=0+1 from rfl,Analysis.ratioModel_cusp_identity g 0 hs Y hY,
    Psi_XR_eq_kernel_ratio Y hY]
  ring

/-- The scalar in F.5 is uniformly bounded at the actual derivative saddle.
This follows from actual p=0 and p=1 model comparisons; no p=0 logarithmic
transport estimate is assumed. -/
lemma separating_derivative_saddle_scalar_bound (P : PsiTheory) :
    ∃ K : ℝ, 0 < K ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ x ∈ Ioo (0 : ℝ) xCritical,
      ∀ n : ℕ, 2 ≤ n → (complexity g 1 : ℝ)*Psi x=(n : ℝ)-1 →
      (n : ℝ)*markedF P g 0 x/(x*markedF P g 1 x) ≤ K := by
  obtain ⟨c,C,hc,hC,hfirst⟩ := marked_model_sandwich_all_stable P 1 (by omega)
  obtain ⟨G,hzero⟩ := unmarked_model_sandwich_eventually P
  refine ⟨8*(2/Real.pi)/c,by positivity,G+2,?_⟩
  intro g hg x hx n hn hmean
  let Y : ℝ := inverseY x
  have hy : Y ∈ Ico (0 : ℝ) y₀ := (inverseY_branch x ⟨hx.1.le,hx.2⟩).1
  have hxy : XR Y=x := (inverseY_branch x ⟨hx.1.le,hx.2⟩).2
  have hsg : Stable g 0 := by unfold Stable;omega
  have hs1 : Stable g 1 := by unfold Stable;omega
  have hM0 := markedModel_pos_parameter g 0 hsg Y hy
  have hM1 := markedModel_pos_parameter g 1 hs1 Y hy
  have hF1 := markedF_pos_parameter P g 1 (by omega) hs1 Y hy
  rw [hxy] at hF1
  have h0 := (hzero g (by omega) Y hy).2
  have h1 := (hfirst g hs1 Y hy).1
  rw [hxy] at h0 h1
  have hh : (1 : ℝ) ≤ (complexity g 0 : ℝ) := by
    exact_mod_cast (show 1≤complexity g 0 by unfold complexity;omega)
  have hhc : (complexity g 1 : ℝ)=(complexity g 0 : ℝ)+1 := by
    exact_mod_cast (show complexity g 1=complexity g 0+1 by unfold complexity;omega)
  have hp : 0 < Psi x := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hh' : 0 < (complexity g 1 : ℝ)*Psi x := by linarith [hmean]
    exact pos_of_mul_pos_right hh' (Nat.cast_nonneg _)
  have hfrac : (1/4 : ℝ) ≤ (complexity g 0 : ℝ)/(complexity g 0+1 : ℕ) := by
    push_cast
    apply (le_div_iff₀ (by positivity)).mpr
    linarith
  have hroot : (1/2 : ℝ) ≤ Real.sqrt ((complexity g 0 : ℝ)/(complexity g 0+1 : ℕ)) := by
    have hh' := Real.sqrt_le_sqrt hfrac
    norm_num at hh' ⊢
    exact hh'
  have hmodel := unmarked_model_derivative_identity g (by omega) Y hy
  rw [hxy] at hmodel
  have hmodelLower : markedModel g 0 Y*((complexity g 0 : ℝ)*Psi x)/2 ≤
      x*markedModel g 1 Y := by
    rw [hmodel]
    nlinarith [mul_le_mul_of_nonneg_left hroot
      (mul_pos hM0 (mul_pos (by linarith) hp)).le]
  have hden : c*(markedModel g 0 Y*((complexity g 0 : ℝ)*Psi x)/2) ≤
      x*markedF P g 1 x := by
    calc
      _ ≤ c*(x*markedModel g 1 Y) := mul_le_mul_of_nonneg_left hmodelLower hc.le
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left h1 hx.1.le]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnmean : (n : ℝ) ≤ 4*((complexity g 0 : ℝ)*Psi x) := by
    rw [hhc] at hmean
    nlinarith [mul_nonneg (by linarith : 0≤(complexity g 0 : ℝ)-1) hp.le]
  apply (div_le_iff₀ (mul_pos hx.1 hF1)).mpr
  have hnum : (n : ℝ)*markedF P g 0 x ≤
      4*(2/Real.pi)*(markedModel g 0 Y*((complexity g 0 : ℝ)*Psi x)) := by
    calc
      _ ≤ (n : ℝ)*((2/Real.pi)*markedModel g 0 Y) :=
        mul_le_mul_of_nonneg_left h0 (Nat.cast_nonneg _)
      _ ≤ _ := by
        have hnn := mul_le_mul_of_nonneg_right hnmean
          (mul_pos (by positivity : (0 : ℝ)<2/Real.pi) hM0).le
        nlinarith only [hnn]
  have hfinal := mul_le_mul_of_nonneg_left hden
    (show 0≤8*(2/Real.pi)/c by positivity)
  have hcancel : (8*(2/Real.pi)/c)*
      (c*(markedModel g 0 Y*((complexity g 0 : ℝ)*Psi x)/2)) =
      4*(2/Real.pi)*(markedModel g 0 Y*((complexity g 0 : ℝ)*Psi x)) := by
    field_simp <;> norm_num
  rw [hcancel] at hfinal
  exact hnum.trans hfinal

end WP.TightSeparating
