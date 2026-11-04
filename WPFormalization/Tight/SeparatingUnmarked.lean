import WPFormalization.Volumes.LeadingMarkedComparison
import WPFormalization.Statements.MarkedRatios
import WPFormalization.Volumes.RatioModelIdentities
import WPFormalization.Volumes.VolumeRatiosEndpoints

/-! The original unmarked prefactor without an unmarked model assumption.
Actual genus exchange at p=0, the proved p=2 leading prefactor and the exact
model genus identity yield an O(1/g) relative error, uniformly in Y. -/

noncomputable section
namespace WP.TightSeparating
open Set Filter
open scoped Topology

/-- The actual unmarked leading comparison, obtained from the already proved
p=0 genus exchange and the two-marked prefactor, with no p=0 comparison input. -/
lemma unmarked_leading_relative_error (P : PsiTheory) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Ico (0 : ℝ) y₀,
      |Real.pi*markedF P g 0 (XR Y)/markedModel g 0 Y-1| ≤ C/(g : ℝ) := by
  obtain ⟨B,H,hB,hH,hBH,hlead⟩ := marked_leading_relative_error P 2 (by omega)
  obtain ⟨D,hD,Gd,hgenus⟩ := (marked_ratios P).2 0
  obtain ⟨N,hN⟩ := exists_nat_ge H
  obtain ⟨K,hK⟩ := exists_nat_ge (2*D)
  refine ⟨2*(B+D),by positivity,N+K+Gd+2,?_⟩
  intro g hg Y hY
  have hg2 : 2 ≤ g := by omega
  have hgR : 0 < (g : ℝ) := by exact_mod_cast (show 0 < g by omega)
  have hs0 : Stable g 0 := by unfold Stable;omega
  have hsc : Stable (g-1) 2 := by unfold Stable;omega
  have hch : complexity (g-1) 2 = complexity g 0 := by unfold complexity;omega
  have hcg : g ≤ complexity (g-1) 2 := by unfold complexity;omega
  have hlarge : H ≤ (complexity (g-1) 2 : ℝ) := hN.trans
    (by exact_mod_cast (show N ≤ complexity (g-1) 2 by unfold complexity;omega))
  have hx : XR Y ∈ Ico (0 : ℝ) xCritical :=
    ⟨XR_nonneg_interior Y hY,XR_strictMonoOn hY.2.le (by simp) hY.2⟩
  have ha := hlead (g-1) hlarge (XR Y) hx
  unfold markedLeadingError at ha
  rw [Analysis.inverseY_eq_of_root (XR Y) Y hY.2.le rfl] at ha
  have ha' : |Real.pi*markedF P (g-1) 2 (XR Y)/markedModel (g-1) 2 Y-1| ≤ B/(g : ℝ) :=
    ha.trans (div_le_div_of_nonneg_left hB.le hgR (by exact_mod_cast hcg))
  have hb : |markedF P (g-1) 2 (XR Y)/(4*r Y*markedF P g 0 (XR Y))-1| ≤ D/(g : ℝ) := by
    simpa only [Nat.zero_add] using hgenus g (by omega) Y hY
  have hsmall : D/(g : ℝ) ≤ 1/2 := by
    apply (div_le_iff₀ hgR).mpr
    have hKg : (K : ℝ) ≤ g := by exact_mod_cast (show K ≤ g by omega)
    linarith
  have hq := volume_ratio_error_quotient _ _ B D (g : ℝ) hgR ha' hb hsmall
  have hf : markedF P (g-1) 2 (XR Y) ≠ 0 :=
    (markedF_pos_parameter P (g-1) 2 (by omega) hsc Y hY).ne'
  have hf0 : markedF P g 0 (XR Y) ≠ 0 := by
    intro hz
    rw [hz,mul_zero,div_zero,zero_sub,abs_neg,abs_one] at hb
    linarith
  have hm : markedModel g 0 Y ≠ 0 := (markedModel_pos_parameter g 0 hs0 Y hY).ne'
  have hr : r Y ≠ 0 := (r_pos Y hY).ne'
  have hid : (Real.pi*markedF P (g-1) 2 (XR Y)/markedModel (g-1) 2 Y) /
      (markedF P (g-1) 2 (XR Y)/(4*r Y*markedF P g 0 (XR Y))) =
      Real.pi*markedF P g 0 (XR Y)/markedModel g 0 Y := by
    rw [Analysis.ratioModel_genus_identity g 0 hg2 Y hY]
    norm_num only [Nat.zero_add]
    field_simp
  rwa [hid] at hq

lemma unmarked_model_sandwich_eventually (P : PsiTheory) :
    ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Ico (0 : ℝ) y₀,
      (1/(2*Real.pi))*markedModel g 0 Y ≤ markedF P g 0 (XR Y) ∧
      markedF P g 0 (XR Y) ≤ (2/Real.pi)*markedModel g 0 Y := by
  obtain ⟨C,hC,G,hbound⟩ := unmarked_leading_relative_error P
  obtain ⟨K,hK⟩ := exists_nat_ge (2*C)
  refine ⟨G+K+2,?_⟩
  intro g hg Y hY
  have hgR : 0 < (g : ℝ) := by exact_mod_cast (show 0 < g by omega)
  have hs : Stable g 0 := by unfold Stable;omega
  have hm := markedModel_pos_parameter g 0 hs Y hY
  have he := hbound g (by omega) Y hY
  have hsmall : C/(g : ℝ) ≤ 1/2 := by
    apply (div_le_iff₀ hgR).mpr
    have hKg : (K : ℝ) ≤ g := by exact_mod_cast (show K ≤ g by omega)
    linarith
  have hhalf := abs_le.mp (he.trans hsmall)
  have hlo : markedModel g 0 Y/2 ≤ Real.pi*markedF P g 0 (XR Y) := by
    have hh := (le_div_iff₀ hm).mp
      (by linarith : (1:ℝ)/2 ≤ Real.pi*markedF P g 0 (XR Y)/markedModel g 0 Y)
    convert hh using 1 <;> ring
  have hhi : Real.pi*markedF P g 0 (XR Y) ≤ 2*markedModel g 0 Y :=
    (div_le_iff₀ hm).mp (by linarith : Real.pi*markedF P g 0 (XR Y)/markedModel g 0 Y ≤ 2)
  constructor
  · rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ (by positivity : 0 < 2*Real.pi)).mpr (by nlinarith)
  · rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ Real.pi_pos).mpr (by nlinarith)

end WP.TightSeparating
