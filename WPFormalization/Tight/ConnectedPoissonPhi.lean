import WPFormalization.Tight.ConnectedPoissonModel
import WPFormalization.Tight.ConnectedPoissonCoefficients
import WPFormalization.Volumes.MarkedGeneratingPositivity

noncomputable section
namespace WP.TightConnected
open Set Filter
open scoped Topology

lemma connected_real_taylor_hasSum (f : ℂ → ℂ) (x : ℝ)
    (hs : HasSum (fun n=>WP.coeff f n*(x:ℂ)^n) (f (x:ℂ))) :
    HasSum (fun n=>realCoeff f n*x^n) (f (x:ℂ)).re := by
  have ht := Complex.reCLM.hasSum hs
  simpa only [←Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero,realCoeff,Complex.reCLM_apply] using ht

lemma connected_probability_data (a : ℕ → ℝ) (f : ℝ → ℝ) (x : ℝ)
    (hx : 0≤x) (ha : ∀ n,0≤a n) (hfx : 0<f x)
    (hs : ∀ z∈Icc (0:ℝ) 1,HasSum (fun n=>a n*(x*z)^n) (f (x*z))) :
    (∀ n,0≤a n*x^n/f x) ∧ HasSum (fun n=>a n*x^n/f x) 1 ∧
      ∀ z∈Icc (0:ℝ) 1, HasSum (fun n=>(a n*x^n/f x)*z^n) (f (x*z)/f x) := by
  refine ⟨fun n=>div_nonneg (mul_nonneg (ha n) (pow_nonneg hx n)) hfx.le,?_,?_⟩
  · simpa only [mul_one,div_self hfx.ne'] using (hs 1 ⟨zero_le_one,le_rfl⟩).div_const (f x)
  · intro z hz
    convert (hs z hz).div_const (f x) using 1
    funext n
    rw [mul_pow]
    ring

lemma connected_unmarked_positive_eventually (P : PsiTheory) :
    ∃ G:ℕ,∀ g≥G,∀ x∈Ico (0:ℝ) xCritical,0 < markedF P g 0 x := by
  obtain ⟨G,hG⟩ := TightSeparating.unmarked_model_sandwich_eventually P
  refine ⟨G+2,?_⟩
  intro g hg x hx
  have hy := inverseY_branch x hx
  have hlo := (hG g (by omega) _ hy.1).1
  rw [hy.2] at hlo
  exact (mul_pos (by positivity : (0:ℝ)<1/(2*Real.pi))
    (markedModel_pos_parameter g 0 (by unfold Stable;omega) _ hy.1)).trans_le hlo

lemma connected_phi_nonnegative_coefficients (P : PsiTheory) (g : ℕ) (hg : 2≤g)
    (hf0 : 0 < markedF P g 0 0) : ∀ n,0≤realCoeff (Phi P g) n := by
  intro n
  by_cases hn : n=0
  · subst n
    simpa [realCoeff,WP.coeff,markedF] using hf0.le
  have he : WP.coeff (Phi P g) n =
      ((shifted P g (List.replicate n 0) 0/(n.factorial:ℝ):ℝ):ℂ) := by
    rw [WP.coeff,show (0:ℂ)=((0:ℝ):ℂ) from rfl,
      PositiveConvolution.Phi_iteratedDeriv_ofReal P g n (by unfold Stable;omega) 0
        ⟨le_rfl,Analysis.xCritical_pos_parameter⟩,Analysis.inverseY_zero_value]
    norm_cast
  have hnon := shifted_zero_nonneg_nonempty P g n (by omega) 0 ⟨le_rfl,y₀_pos⟩
  change 0≤(WP.coeff (Phi P g) n).re
  rw [he,Complex.ofReal_re]
  exact div_nonneg hnon (Nat.cast_nonneg _)

lemma connected_poisson_probability_data (c : ℝ) (hc : 0≤c) :
    (∀ n,0≤Real.exp (-2*c)*(2*c)^n/(n.factorial:ℝ)) ∧
    HasSum (fun n=>Real.exp (-2*c)*(2*c)^n/(n.factorial:ℝ)) 1 ∧
    ∀ z∈Icc (0:ℝ) 1,
      HasSum (fun n=>(Real.exp (-2*c)*(2*c)^n/(n.factorial:ℝ))*z^n)
        (Real.exp (2*c*(z-1))) := by
  refine ⟨fun n=>by positivity,?_,?_⟩
  · convert (NormedSpace.expSeries_div_hasSum_exp (2*c)).mul_left (Real.exp (-2*c)) using 1
    · funext n
      ring
    · simp [←Real.exp_eq_exp_ℝ,←Real.exp_add]
  · intro z hz
    convert (NormedSpace.expSeries_div_hasSum_exp (2*c*z)).mul_left (Real.exp (-2*c)) using 1
    · funext n
      rw [mul_pow]
      ring
    · rw [←Real.exp_eq_exp_ℝ,←Real.exp_add]
      congr 1
      ring

lemma connected_phi_poisson_probability_limit (P : PsiTheory) (n : ℕ)
    (c : ℝ) (hc : 0<c) (gs : ℕ→ℕ) (hg : Tendsto gs atTop atTop) :
    Tendsto (fun j=>realCoeff (Phi P (gs j)) n * (c/(complexity (gs j) 0:ℝ))^n /
      markedF P (gs j) 0 (c/(complexity (gs j) 0:ℝ))) atTop
      (𝓝 (Real.exp (-2*c)*(2*c)^n/(n.factorial:ℝ))) := by
  let hs : ℕ→ℝ := fun j=>(complexity (gs j) 0:ℝ)
  have hh : Tendsto hs atTop atTop := connected_complexity_tendsto gs hg
  have hch : Tendsto (fun j=>(complexity (gs j) 0:ℝ)/hs j) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hh.eventually_gt_atTop 0] with j hj
    exact (div_self hj.ne').symm
  obtain ⟨G,hG⟩ := connected_unmarked_positive_eventually P
  apply positive_pgf_coefficients_tendsto
    (fun j n=>realCoeff (Phi P (gs j)) n*(c/hs j)^n/markedF P (gs j) 0 (c/hs j))
    (fun n=>Real.exp (-2*c)*(2*c)^n/(n.factorial:ℝ))
    (fun j z=>markedF P (gs j) 0 ((c/hs j)*z)/markedF P (gs j) 0 (c/hs j))
    (fun z=>Real.exp (2*c*(z-1))) _ (connected_poisson_probability_data c hc.le) _ n
  · filter_upwards [hg.eventually_ge_atTop (G+2),
      connected_small_weight_eventually hs hh c hc.le] with j hj hx
    apply connected_probability_data _ _ _ hx.1
      (connected_phi_nonnegative_coefficients P (gs j) (by omega)
        (hG (gs j) (by omega) 0 ⟨le_rfl,Analysis.xCritical_pos_parameter⟩))
      (hG (gs j) (by omega) _ hx)
    intro z hz
    have hxz : (c/hs j)*z∈Ico (0:ℝ) xCritical :=
      ⟨mul_nonneg hx.1 hz.1,(mul_le_of_le_one_right hx.1 hz.2).trans_lt hx.2⟩
    have hsum := marked_generating_hasSum P (gs j) 0 (((c/hs j)*z:ℝ):ℂ)
      (by rw [Complex.norm_of_nonneg hxz.1];exact hxz.2)
    simpa only [iteratedDeriv_zero,markedF] using connected_real_taylor_hasSum _ _ hsum
  · intro z hz
    exact connected_marked_poisson_pgf_limit P 0 gs hg hs hh hch c hc z hz.1.le

lemma connected_phi_poisson_probability_eventually_lower (P : PsiTheory) (n : ℕ)
    (c : ℝ) (hc : 0<c) (gs : ℕ→ℕ) (hg : Tendsto gs atTop atTop) :
    ∀ᶠ j in atTop,
      Real.exp (-2*c)*(2*c)^n/(2*(n.factorial:ℝ)) ≤
        realCoeff (Phi P (gs j)) n*(c/(complexity (gs j) 0:ℝ))^n /
          markedF P (gs j) 0 (c/(complexity (gs j) 0:ℝ)) := by
  have hp : 0<Real.exp (-2*c)*(2*c)^n/(n.factorial:ℝ) := by positivity
  have ht := connected_phi_poisson_probability_limit P n c hc gs hg
  have hhalf : Real.exp (-2*c)*(2*c)^n/(2*(n.factorial:ℝ)) <
      Real.exp (-2*c)*(2*c)^n/(n.factorial:ℝ) := by
    rw [show Real.exp (-2*c)*(2*c)^n/(2*(n.factorial:ℝ)) =
      (Real.exp (-2*c)*(2*c)^n/(n.factorial:ℝ))/2 by ring]
    linarith
  have he := ht.eventually (eventually_gt_nhds (hhalf :
    Real.exp (-2*c)*(2*c)^n/(2*(n.factorial:ℝ)) <
      Real.exp (-2*c)*(2*c)^n/(n.factorial:ℝ)))
  exact he.mono (fun _ h=>h.le)

end WP.TightConnected
