import WPFormalization.Tight.GeneratingFunctions
import WPFormalization.Volumes.PointMassProof
import WPFormalization.Volumes.StringFlowProof

noncomputable section
namespace WP.TightSeparating
open Set Filter PositiveConvolution
open scoped Topology BigOperators

/-- Actual analytic positive remainder for a cut product. Physical lengths are
fixed while its argument varies. -/
def cutProductR (P : PsiTheory) {Q : ℕ} (gs ps : Fin Q → ℕ)
    (L : (i : Fin Q) → Fin (ps i) → ℝ) (z : ℂ) : ℂ :=
  ∏ i, TightConvolution.tightR P (gs i) (ps i) (L i) z

def cutProductG (P : PsiTheory) {Q : ℕ} (gs ps : Fin Q → ℕ)
    (L : (i : Fin Q) → Fin (ps i) → ℝ) (z : ℂ) : ℂ :=
  ∏ i, TightMoments.momentTightG P (gs i) (ps i) (L i) z

lemma cutProductR_analyticAt (P : PsiTheory) {Q : ℕ} (gs ps : Fin Q → ℕ)
    (L : (i : Fin Q) → Fin (ps i) → ℝ) (z : ℂ) (hz : ‖z‖ < xCritical) :
    AnalyticAt ℂ (cutProductR P gs ps L) z := by
  apply Finset.analyticAt_fun_prod
  intro i hi
  exact TightConvolution.tightR_analyticAt P (gs i) (ps i) (L i) z hz

lemma cutProductR_positiveJets (P : PsiTheory) {Q : ℕ} (gs ps : Fin Q → ℕ)
    (L : (i : Fin Q) → Fin (ps i) → ℝ) : PositiveJets (cutProductR P gs ps L) := by
  have hz : ‖(0 : ℂ)‖ < xCritical := by simpa using Analysis.xCritical_pos_parameter
  exact PositiveJets.prod _ _ (fun i _ =>
    TightConvolution.tightR_analyticAt P (gs i) (ps i) (L i) 0 hz)
    (fun i _ => TightConvolution.tightR_positiveJets P (gs i) (ps i) (L i))

lemma cutProductR_taylor (P : PsiTheory) {Q : ℕ} (gs ps : Fin Q → ℕ)
    (L : (i : Fin Q) → Fin (ps i) → ℝ) (z : ℂ) (hz : ‖z‖ < xCritical) :
    HasSum (fun j => WP.coeff (cutProductR P gs ps L) j*z^j) (cutProductR P gs ps L z) :=
  analytic_ball_hasSum _ xCritical Analysis.xCritical_pos_parameter
    (cutProductR_analyticAt P gs ps L) z hz

lemma cutProductG_factor (P : PsiTheory) {Q : ℕ} (gs ps : Fin Q → ℕ)
    (hp : ∀ i, 1 ≤ ps i) (hs : ∀ i, Stable (gs i) (ps i))
    (L : (i : Fin Q) → Fin (ps i) → ℝ) (H : ℕ)
    (hH : ∑ i, complexity (gs i) (ps i) = H)
    (z : ℂ) (hz : ‖z‖ < xCritical) :
    cutProductG P gs ps L z = universalV P z^H*cutProductR P gs ps L z := by
  unfold cutProductG cutProductR
  simp_rw [TightMoments.momentTightG_eq_positive_factor P _ _ (hp _) (hs _) _ z hz]
  rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,hH]

lemma tightShiftedPolynomial_pos (P : PsiTheory) (g p : ℕ) (hp : 1 ≤ p) (hs : Stable g p)
    (Y : ℝ) (hY : Y ∈ Ico (0 : ℝ) y₀) (L : Fin p → ℝ) :
    0 < tightShiftedPolynomial P g p Y L := by
  have hf := markedF_pos_parameter P g p hp hs Y hY
  have hb := (tightShiftedPolynomial_bounds P g p hp hs Y hY L).1
  rw [string_flow_proof P g p hs Y hY] at hb
  have hh := (le_div_iff₀ hf).mp hb
  simp only [one_mul] at hh
  exact hf.trans_le hh

lemma cutProductR_real_positive (P : PsiTheory) {Q : ℕ} (gs ps : Fin Q → ℕ)
    (hp : ∀ i, 1 ≤ ps i) (hs : ∀ i, Stable (gs i) (ps i))
    (L : (i : Fin Q) → Fin (ps i) → ℝ) (x : ℝ) (hx : x ∈ Ico (0 : ℝ) xCritical) :
    0 < (cutProductR P gs ps L x).re ∧ (cutProductR P gs ps L x).im = 0 := by
  have hY := (inverseY_branch x hx).1
  have hp' (i : Fin Q) : 0 <
      a (inverseY x)^(complexity (gs i) (ps i))*
        tightShiftedPolynomial P (gs i) (ps i) (inverseY x) (L i) :=
    mul_pos (pow_pos (a_pos _ hY) _)
      (tightShiftedPolynomial_pos P _ _ (hp i) (hs i) _ hY _)
  have he : cutProductR P gs ps L x =
      (∏ i, a (inverseY x)^(complexity (gs i) (ps i))*
        tightShiftedPolynomial P (gs i) (ps i) (inverseY x) (L i) : ℝ) := by
    unfold cutProductR
    simp_rw [TightConvolution.tightR_ofReal P _ _ (hp _) (hs _) _ x hx]
    exact (map_prod Complex.ofRealHom _ _).symm
  rw [he,Complex.ofReal_re,Complex.ofReal_im]
  exact ⟨Finset.prod_pos (fun i _ => hp' i),rfl⟩

/-- Lemma 9.3 applied to the actual cut numerator. All analytic and positive
factor premises are proved for its genuine finite shifted polynomials. -/
lemma cutProduct_point_mass_bound (P : PsiTheory) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℕ, 10 ≤ g → ∀ Q : ℕ, ∀ gs ps : Fin Q → ℕ,
      (∀ i, 1 ≤ ps i) → (∀ i, Stable (gs i) (ps i)) →
      (∑ i, complexity (gs i) (ps i)) = complexity g 0 →
      ∀ L : (i : Fin Q) → Fin (ps i) → ℝ, ∀ x ∈ Ioo (0 : ℝ) xCritical,
      ∀ j : ℕ,
      realCoeff (cutProductG P gs ps L) j*x^j / (cutProductG P gs ps L x).re ≤
        C/Real.sqrt ((complexity g 1 : ℝ)*euler Psi x) := by
  obtain ⟨C,hC,hbound⟩ := point_mass_bound_proof P (1/2) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro g hg Q gs ps hp hs hH L x hx j
  have hrelation : (1/2 : ℝ)*(complexity g 1 : ℝ) ≤ complexity g 0 := by
    have he0 : complexity g 0=2*g-2 := by unfold complexity;omega
    have he1 : complexity g 1=2*g-1 := by unfold complexity;omega
    rw [he0,he1,Nat.cast_sub (by omega),Nat.cast_sub (by omega)]
    push_cast
    have hh : (10 : ℝ) ≤ g := by exact_mod_cast hg
    linarith
  have hRa : AnalyticOnNhd ℂ (cutProductR P gs ps L) (Metric.ball 0 xCritical) := by
    intro z hz
    exact cutProductR_analyticAt P gs ps L z (by simpa only [Metric.mem_ball,dist_zero_right] using hz)
  have hRp := cutProductR_real_positive P gs ps hp hs L x ⟨hx.1.le,hx.2⟩
  have hb := hbound (complexity g 1) (complexity g 0)
    (by unfold complexity;omega) (by unfold complexity;omega) hrelation
    x hx (cutProductR P gs ps L) hRa
    (cutProductR_positiveJets P gs ps L).coefficient_nonneg hRp.1 hRp.2
    (cutProductR_taylor P gs ps L) j
  have hEq : (cutProductG P gs ps L) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => universalV P z^(complexity g 0)*cutProductR P gs ps L z) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) Analysis.xCritical_pos_parameter] with z hz
    exact cutProductG_factor P gs ps hp hs L _ hH z
      (by simpa only [Metric.mem_ball,dist_zero_right] using hz)
  have hcoeff : realCoeff (cutProductG P gs ps L) j =
      realCoeff (fun z => universalV P z^(complexity g 0)*cutProductR P gs ps L z) j := by
    unfold realCoeff WP.coeff
    rw [Filter.EventuallyEq.iteratedDeriv_eq j hEq]
  rw [hcoeff,cutProductG_factor P gs ps hp hs L _ hH x
    (by simpa only [Complex.norm_of_nonneg hx.1.le] using hx.2)]
  exact hb

end WP.TightSeparating
namespace WP.TightSeparating
open Set Filter PositiveConvolution
open scoped Topology BigOperators

lemma cutProductG_analyticAt (P : PsiTheory) {Q : ℕ} (gs ps : Fin Q → ℕ)
    (L : (i : Fin Q) → Fin (ps i) → ℝ) (z : ℂ) (hz : ‖z‖ < xCritical) :
    AnalyticAt ℂ (cutProductG P gs ps L) z := by
  exact Finset.analyticAt_fun_prod _ (fun i _ =>
    TightMoments.momentTightG_analyticAt P (gs i) (ps i) (L i) z hz)

lemma cutProductG_positiveJets (P : PsiTheory) {Q : ℕ} (gs ps : Fin Q → ℕ)
    (hp : ∀ i, 1 ≤ ps i) (hs : ∀ i, Stable (gs i) (ps i))
    (L : (i : Fin Q) → Fin (ps i) → ℝ) : PositiveJets (cutProductG P gs ps L) := by
  have hz : ‖(0 : ℂ)‖ < xCritical := by simpa using Analysis.xCritical_pos_parameter
  have hT := PositiveJets.prod (Finset.univ : Finset (Fin Q))
    (fun i => TightConvolution.tightG P (gs i) (ps i) (L i))
    (fun i _ => TightConvolution.tightG_analyticAt P (gs i) (ps i) (L i) 0 hz)
    (fun i _ => TightConvolution.tightG_positiveJets P (gs i) (ps i) (L i))
  have hEq : (cutProductG P gs ps L) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => ∏ i, TightConvolution.tightG P (gs i) (ps i) (L i) z) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) Analysis.xCritical_pos_parameter] with z hz
    unfold cutProductG
    apply Finset.prod_congr rfl
    intro i hi
    exact TightMoments.momentTightG_eq_positive_factor P _ _ (hp i) (hs i) _ z
      (by simpa only [Metric.mem_ball,dist_zero_right] using hz)
  intro j
  obtain ⟨a,ha⟩ := hT j
  exact ⟨a,(Filter.EventuallyEq.iteratedDeriv_eq j hEq).trans ha⟩

lemma cutProductG_taylor (P : PsiTheory) {Q : ℕ} (gs ps : Fin Q → ℕ)
    (L : (i : Fin Q) → Fin (ps i) → ℝ) (z : ℂ) (hz : ‖z‖ < xCritical) :
    HasSum (fun j => WP.coeff (cutProductG P gs ps L) j*z^j) (cutProductG P gs ps L z) :=
  analytic_ball_hasSum _ xCritical Analysis.xCritical_pos_parameter
    (cutProductG_analyticAt P gs ps L) z hz

/-- The bounded-cusp branch only needs the elementary positive-series bound;
no diverging variance or large cusp count is silently imposed. -/
lemma cutProductG_coefficient_le_value (P : PsiTheory) {Q : ℕ} (gs ps : Fin Q → ℕ)
    (hp : ∀ i, 1 ≤ ps i) (hs : ∀ i, Stable (gs i) (ps i))
    (L : (i : Fin Q) → Fin (ps i) → ℝ) (x : ℝ) (hx : x ∈ Ico (0 : ℝ) xCritical)
    (j : ℕ) : realCoeff (cutProductG P gs ps L) j*x^j ≤ (cutProductG P gs ps L x).re := by
  have hn := (cutProductG_positiveJets P gs ps hp hs L).coefficient_nonneg
  have hnorm : ‖(x : ℂ)‖ < xCritical := by simpa only [Complex.norm_of_nonneg hx.1] using hx.2
  have ht := (cutProductG_taylor P gs ps L (x : ℂ) hnorm).mapL Complex.reCLM
  have ht' : HasSum (fun n => realCoeff (cutProductG P gs ps L) n*x^n)
      (cutProductG P gs ps L x).re := by
    simpa only [Complex.reCLM_apply,←Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,mul_zero,sub_zero,realCoeff] using ht
  have hb := ht'.summable.le_tsum j (fun n _ => mul_nonneg (hn n).1 (pow_nonneg hx.1 _))
  rw [ht'.tsum_eq] at hb
  exact hb

end WP.TightSeparating
