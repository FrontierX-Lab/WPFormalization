import WPFormalization.External.HigherKappa
import WPFormalization.Tight.UnmarkedMomentKernel
import WPFormalization.Tight.GeneratingFunctions
/-! The unmarked tight factor from the generic classical higher-kappa transform.

The raw-moment Schur times, all normalization powers, the positive analytic
factor and its actual real trace are proved here, rather than assumed.
-/
noncomputable section
namespace WP.TightUnmarked
open Set Filter PositiveConvolution Analysis.UnmarkedMoments
open scoped Topology
universe u
lemma kappaTimesSeries_logarithmic (Y : ℂ) :
    External.kappaTimesSeries (fun j=>logarithmicCoeff j Y)=logarithmicSeries Y := by
  ext j
  simp only [External.kappaTimesSeries,PowerSeries.coeff_mk,logarithmicSeries_coeff]
  split_ifs with hj
  · subst j; simp
  · rfl
lemma kappaSchurTime_logarithmic (Y : ℂ) (ha : deriv X Y≠0) (j : ℕ) (hj : 0<j) :
    External.kappaSchurTime (fun j=>logarithmicCoeff j Y) j=
      -iteratedDeriv (j+1) X Y/deriv X Y := by
  rw [External.kappaSchurTime,ite_eq_right (ne_of_gt hj),kappaTimesSeries_logarithmic,
    momentSeries_reconstruction Y ha,PowerSeries.coeff_C_mul,momentSeries_coeff]
  ring
lemma descendant_polynomial_normalization (P : PsiTheory) (g : ℕ) (hs : Stable g 0)
    (M : ℕ→ℂ) (ha : M 0≠0) :
    External.descendantFreeEnergyPolynomial P g (fun j=> -M j/M 0)=
      M 0^(complexity g 0)*TightMoments.complexMomentAmplitude P g [] M := by
  have hD : deficit g []=dimension g 0 := by simp [deficit]
  unfold External.descendantFreeEnergyPolynomial TightMoments.complexMomentAmplitude
  simp only [List.length_nil,List.sum_nil,List.nil_append]
  rw [ite_eq_left ⟨hs,Nat.zero_le _⟩,hD,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  have hprod : (∏ i : Fin (dimension g 0), (-M (i.val+1)/M 0)^(l i)/(l i).factorial)=
      (∏ i : Fin (dimension g 0),(-M (i.val+1))^(l i)/(l i).factorial)/
        M 0^(∑ i,l i) := by
    calc
      _=∏ i : Fin (dimension g 0),
          ((-M (i.val+1))^(l i)/(l i).factorial)/(M 0^(l i)) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [div_pow]
        ring
      _=_ := by rw [Finset.prod_div_distrib,Finset.prod_pow_eq_pow_sum]
  rw [hprod,pow_add]
  field_simp

def unmarkedR (C : External.HigherKappaRealization.{u} P) (g : ℕ) (z : ℂ) : ℂ :=
  External.kappaFreeEnergyPolynomial C.realization C.kappa g
    (fun j=>physicalLogarithmicCoeff P j z)
lemma unmarkedR_analyticAt (C : External.HigherKappaRealization.{u} P) (g : ℕ)
    (z : ℂ) (hz : ‖z‖<xCritical) : AnalyticAt ℂ (unmarkedR C g) z := by
  apply Finset.analyticAt_fun_sum
  intro e he
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_fun_prod
  intro i hi
  exact ((physicalLogarithmicCoeff_analyticAt P _ z hz).pow _).div_const
lemma unmarkedR_positiveJets (C : External.HigherKappaRealization.{u} P) (g : ℕ)
    (hs : Stable g 0) : PositiveJets (unmarkedR C g) := by
  have hx : ‖(0:ℂ)‖<xCritical := by simpa using Analysis.xCritical_pos_parameter
  apply PositiveJets.sum
  · intro e he
    apply AnalyticAt.mul analyticAt_const
    apply Finset.analyticAt_fun_prod
    intro i hi
    exact ((physicalLogarithmicCoeff_analyticAt P _ 0 hx).pow _).div_const
  · intro e he
    have hc := C.top_nonnegative g 0 (dimension g 0) e hs
      ((mem_backgrounds_iff _ _).mp he)
    apply PositiveJets.mul analyticAt_const
    · apply Finset.analyticAt_fun_prod
      intro i hi
      exact ((physicalLogarithmicCoeff_analyticAt P _ 0 hx).pow _).div_const
    · exact PositiveJets.const ⟨_,hc⟩
    · apply PositiveJets.prod
      · intro i hi
        exact ((physicalLogarithmicCoeff_analyticAt P _ 0 hx).pow _).div_const
      · intro i hi
        have hfac : 0≤((e i).factorial:ℝ)⁻¹ := by positivity
        have hmul := PositiveJets.mul ((physicalLogarithmicCoeff_analyticAt P (i.val+1) 0 hx).pow (e i))
          analyticAt_const
          (PositiveJets.pow (physicalLogarithmicCoeff_analyticAt P (i.val+1) 0 hx)
            (physicalLogarithmicCoeff_positiveJets P (i.val+1) (Nat.succ_pos i.val)) (e i))
          (PositiveJets.const ⟨_,hfac⟩)
        have hc' : nnComplexHom ⟨((e i).factorial:ℝ)⁻¹,hfac⟩=
            (((((e i).factorial:ℝ)⁻¹):ℝ):ℂ) := by
          change (↑(((e i).factorial:ℝ)⁻¹):ℂ)=_
          simp only [Complex.ofReal_inv,Complex.ofReal_natCast]
        simp only [hc',Pi.pow_apply] at hmul
        simpa only [Complex.ofReal_inv,Complex.ofReal_natCast,div_eq_mul_inv] using hmul
lemma unmarkedR_transform (C : External.HigherKappaRealization.{u} P) (g : ℕ) (hg : 2≤g)
    (Y : ℂ) (ha : deriv X Y≠0) :
    External.kappaFreeEnergyPolynomial C.realization C.kappa g
      (fun j=>logarithmicCoeff j Y)=
      deriv X Y^(complexity g 0)*TightMoments.complexMomentAmplitude P g []
        (fun j=>iteratedDeriv (j+1) X Y) := by
  rw [←C.free_energy_transform g hg]
  have hs : Stable g 0 := by unfold Stable;omega
  have hnorm:=descendant_polynomial_normalization P g hs
    (fun j=>iteratedDeriv (j+1) X Y) (by simpa only [zero_add,iteratedDeriv_one] using ha)
  simp only [zero_add,iteratedDeriv_one] at hnorm
  rw [←hnorm]
  apply Finset.sum_congr rfl
  intro l hl
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [kappaSchurTime_logarithmic Y ha _ (Nat.succ_pos _)]
lemma unmarkedR_ofReal (C : External.HigherKappaRealization.{u} P) (g : ℕ) (hg : 2≤g)
    (x : ℝ) (hx : x∈Ico (0:ℝ) xCritical) :
    unmarkedR C g (x:ℂ)=
      (a (inverseY x)^(complexity g 0)*shifted P g [] (inverseY x):ℝ) := by
  have hy:=inverseY_branch x hx
  have ha:deriv X (inverseY x:ℂ)≠0 := by
    have he:deriv X (inverseY x:ℂ)=(a (inverseY x):ℂ) := by
      apply Complex.ext
      · rfl
      · simpa only [Complex.ofReal_im,iteratedDeriv_one] using
          iteratedDeriv_X_im_ofReal 1 (inverseY x)
    rw [he]
    exact Complex.ofReal_ne_zero.mpr (a_pos _ hy.1).ne'
  unfold unmarkedR physicalLogarithmicCoeff
  rw [planarInverse_ofReal P x hx,unmarkedR_transform C g hg _ ha]
  have hm(j:ℕ):iteratedDeriv (j+1) X (inverseY x:ℂ)=
      (TightMoments.planeMoments (inverseY x) j:ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using iteratedDeriv_X_im_ofReal (j+1) (inverseY x)
  simp_rw [hm]
  rw [TightMoments.complexMomentAmplitude_ofReal,
    TightMoments.shifted_eq_momentAmplitude]
  simp only [List.map_nil,List.prod_nil,one_mul]
  have ha':deriv X (inverseY x:ℂ)=(a (inverseY x):ℂ) := by
    simpa only [zero_add,iteratedDeriv_one,TightMoments.planeMoments_zero] using hm 0
  rw [ha']
  push_cast
  rfl
lemma tightShiftedPolynomial_zero (P : PsiTheory) (g : ℕ) (Y : ℝ) (L : Fin 0→ℝ) :
    tightShiftedPolynomial P g 0 Y L=shifted P g [] Y := by
  unfold tightShiftedPolynomial
  have hmem : (0 : Fin 0→ℕ)∈degreeTuples g 0 := by
    rw [mem_degreeTuples_iff]
    simp
  rw [Finset.sum_eq_single (0:Fin 0→ℕ)]
  · simp
  · intro d hd hne
    exact False.elim (hne (Subsingleton.elim _ _))
  · exact fun hn=>False.elim (hn hmem)
lemma unmarkedG_ofReal (C : External.HigherKappaRealization.{u} P) (g : ℕ) (hg : 2≤g)
    (x : ℝ) (hx : x∈Ico (0:ℝ) xCritical) :
    universalV P (x:ℂ)^(complexity g 0)*unmarkedR C g (x:ℂ)=
      (shifted P g [] (inverseY x):ℂ) := by
  have ha:= (a_pos (inverseY x) (inverseY_branch x hx).1).ne'
  rw [show universalV P (x:ℂ)=((a (inverseY x))⁻¹:ℂ) by
    simpa only [universalV,Complex.ofReal_inv] using planarThird_ofReal P x hx,
    unmarkedR_ofReal C g hg x hx]
  push_cast
  simp only [inv_pow,←mul_assoc,inv_mul_cancel₀
    (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr ha)),one_mul]
lemma momentTightG_unmarked_factor (C : External.HigherKappaRealization.{u} P) (g : ℕ)
    (hg : 2≤g) (L : Fin 0→ℝ) (z : ℂ) (hz : ‖z‖<xCritical) :
    TightMoments.momentTightG P g 0 L z=
      universalV P z^(complexity g 0)*unmarkedR C g z := by
  have hf:AnalyticOnNhd ℂ (TightMoments.momentTightG P g 0 L) (Metric.ball 0 xCritical) := by
    intro w hw
    exact TightMoments.momentTightG_analyticAt P g 0 L w
      (by simpa only [Metric.mem_ball,dist_zero_right] using hw)
  have hq:AnalyticOnNhd ℂ (fun w=>universalV P w^(complexity g 0)*unmarkedR C g w)
      (Metric.ball 0 xCritical) := by
    intro w hw
    have hw':‖w‖<xCritical := by simpa only [Metric.mem_ball,dist_zero_right] using hw
    have hv:AnalyticAt ℂ (universalV P) w := by
      change AnalyticAt ℂ (iteratedDeriv 3 (Phi P 0)) w
      simpa only [iteratedDeriv_eq_iterate] using
        (Phi_analyticAt_open_disk P 0 w hw').iterated_deriv 3
    exact (hv.pow _).mul (unmarkedR_analyticAt C g w hw')
  have hc:xCritical/2∈Ioo (0:ℝ) xCritical :=
    ⟨half_pos Analysis.xCritical_pos_parameter,half_lt_self Analysis.xCritical_pos_parameter⟩
  have hmem:((xCritical/2:ℝ):ℂ)∈Metric.ball 0 xCritical := by
    simpa only [Metric.mem_ball,dist_zero_right,Complex.norm_of_nonneg hc.1.le] using hc.2
  have he:EqOn (TightMoments.momentTightG P g 0 L)
      (fun w=>universalV P w^(complexity g 0)*unmarkedR C g w)
      (Metric.ball 0 xCritical) := by
    apply Analysis.complex_identity_of_real_germ _ _ _ (xCritical/2) hf hq
      (convex_ball (0:ℂ) xCritical).isPreconnected hmem
    filter_upwards [isOpen_Ioo.mem_nhds hc] with x hx
    rw [TightMoments.momentTightG_ofReal P g 0 L x ⟨hx.1.le,hx.2⟩,
      unmarkedG_ofReal C g hg x ⟨hx.1.le,hx.2⟩,tightShiftedPolynomial_zero]
  exact he (by simpa only [Metric.mem_ball,dist_zero_right] using hz)
lemma shifted_unmarked_origin_positive (C : External.HigherKappaRealization.{u} P) (g : ℕ)
    (hs : Stable g 0) : 0<shifted P g [] 0 := by
  have ht:=C.realization.kappa_psi_transform g 0 (0:Fin 0→ℕ) hs (by simp)
  have hp:=C.kappa_one_top_positive g 0 hs
  have hm:=mixed_transform P g [] hs (by simp)
  have hc : (2*Real.pi^2:ℝ)^(deficit g [])≠0 := by positivity
  have he : shifted P g [] 0=External.kappaPsiSum P g [] := by
    simpa only [mixedBracket,List.sum_nil,pow_zero,one_mul,mul_div_cancel_left₀ _ hc,
      List.map_nil,List.prod_nil,List.nil_append,External.kappaPsiSum] using hm
  simp only [List.ofFn_zero] at ht
  rw [he,←ht]
  simpa [External.mixedIntegral] using
    div_pos hp (show (0:ℝ)<(dimension g 0).factorial by positivity)
lemma unmarkedR_taylor (C : External.HigherKappaRealization.{u} P) (g : ℕ)
    (z : ℂ) (hz : ‖z‖<xCritical) :
    HasSum (fun j=>WP.coeff (unmarkedR C g) j*z^j) (unmarkedR C g z) :=
  analytic_ball_hasSum _ xCritical Analysis.xCritical_pos_parameter
    (unmarkedR_analyticAt C g) z hz
lemma unmarkedR_real_positive (C : External.HigherKappaRealization.{u} P) (g : ℕ)
    (hg : 2≤g) (x : ℝ) (hx : x∈Ico (0:ℝ) xCritical) : 0<(unmarkedR C g (x:ℂ)).re := by
  have hs : Stable g 0 := by unfold Stable;omega
  have hn:‖(x:ℂ)‖<xCritical := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2
  have hsum:=Complex.reCLM.hasSum (unmarkedR_taylor C g (x:ℂ) hn)
  have hpos:= (unmarkedR_positiveJets C g hs).coefficient_nonneg
  have ht(j:ℕ):0≤(WP.coeff (unmarkedR C g) j*(x:ℂ)^j).re := by
    rw [←Complex.ofReal_pow,Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    exact mul_nonneg (hpos j).1 (pow_nonneg hx.1 j)
  have hz:=unmarkedR_ofReal C g hg 0 ⟨le_rfl,Analysis.xCritical_pos_parameter⟩
  simp only [Complex.ofReal_zero,Analysis.inverseY_zero_value,a_zero,one_pow,one_mul] at hz
  have hc:0<(WP.coeff (unmarkedR C g) 0).re := by
    simpa only [WP.coeff,Nat.factorial_zero,Nat.cast_one,div_one,iteratedDeriv_zero,
      hz,Complex.ofReal_re] using shifted_unmarked_origin_positive C g hs
  have hle:=hsum.summable.le_tsum 0 (fun j hj=>ht j)
  rw [hsum.tsum_eq] at hle
  simp only [pow_zero,mul_one] at hle
  exact hc.trans_le hle
lemma shifted_unmarked_positive (C : External.HigherKappaRealization.{u} P) (g : ℕ)
    (hg : 2≤g) (Y : ℝ) (hY : Y∈Ico (0:ℝ) y₀) : 0<shifted P g [] Y := by
  have hx:XR Y∈Ico (0:ℝ) xCritical :=
    ⟨XR_nonneg_interior Y hY,XR_strictMonoOn (show Y∈Iic y₀ from hY.2.le) (by simp) hY.2⟩
  have he:=unmarkedR_ofReal C g hg (XR Y) hx
  rw [Analysis.inverseY_eq_of_root (XR Y) Y hY.2.le rfl] at he
  have hp:=unmarkedR_real_positive C g hg (XR Y) hx
  rw [he,Complex.ofReal_re] at hp
  exact (mul_pos_iff_of_pos_left (pow_pos (a_pos Y hY) _)).mp hp
end WP.TightUnmarked
