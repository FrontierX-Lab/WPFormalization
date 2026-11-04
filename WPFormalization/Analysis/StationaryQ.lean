import WPFormalization.Analysis.JointAffineIntegral
import WPFormalization.Analysis.ActionPositivity
import WPFormalization.Analysis.BesselBranches

/-! The actual stationary equation and its strict T-monotonicity on an open
real parameter domain containing [0,y₀). The complex C¹ statement is proved
by differentiation under the displayed compact-interval integral. The sign
of X'' before 5/2 also covers negative Y; no one-sided extension is assumed.
-/
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set
open scoped Topology
/-- The two affine coefficients of the actual stationary kernel path. -/
def stationaryQLinear (s : ℝ) : ComplexPair →L[ℂ] ℂ :=
  (s : ℂ)^2 • ContinuousLinearMap.fst ℂ ℂ ℂ +
    (1-(s : ℂ)^2) • ContinuousLinearMap.snd ℂ ℂ ℂ
lemma stationaryQLinear_continuous : Continuous stationaryQLinear := by
  unfold stationaryQLinear
  fun_prop
/-- The original normalized stationary integral as a function of its two complex inputs. -/
def stationaryQProd (p : ComplexPair) : ℂ :=
  ∫ s : ℝ in (0)..1,deriv X (stationaryQLinear s p)
lemma stationaryQ_eq_K (Y T : ℂ) : stationaryQProd (Y,T) = K Y (2*(T-Y)) := by
  unfold stationaryQProd K
  apply intervalIntegral.integral_congr
  intro s hs
  congr 1
  change deriv X ((s : ℂ)^2*Y+(1-(s : ℂ)^2)*T) = _
  apply congrArg (deriv X)
  ring
lemma stationaryQ_contDiff_one : ContDiff ℂ 1 stationaryQProd := by
  have hg : Differentiable ℂ (deriv X) := X_differentiable.deriv
  change ContDiff ℂ 1 (fun w : ComplexPair => ∫ s : ℝ in (0)..1,deriv X (stationaryQLinear s w))
  simpa only [zero_add,one_mul] using
    affineIntegral_prod_contDiff_one (fun _ => 1) (fun _ => 0) stationaryQLinear
      continuous_const continuous_const stationaryQLinear_continuous (deriv X) hg
lemma stationaryQ_hasFDerivAt (p : ComplexPair) :
    HasFDerivAt stationaryQProd
      (∫ s : ℝ in (0)..1,deriv (deriv X) (stationaryQLinear s p) • stationaryQLinear s) p := by
  have hg : Differentiable ℂ (deriv X) := X_differentiable.deriv
  change HasFDerivAt (fun w : ComplexPair => ∫ s : ℝ in (0)..1,deriv X (stationaryQLinear s w)) _ p
  simpa only [zero_add,one_mul] using
    hasFDerivAt_affineIntegral_prod (fun _ => 1) (fun _ => 0) stationaryQLinear
      continuous_const continuous_const stationaryQLinear_continuous (deriv X) hg p
lemma stationaryQ_second_hasDerivAt (Y T : ℂ) :
    HasDerivAt (fun t => stationaryQProd (Y,t)) (2*deriv (K Y) (2*(T-Y))) T := by
  have he : (fun t => stationaryQProd (Y,t)) = fun t => K Y (2*(t-Y)) := by
    funext t
    exact stationaryQ_eq_K Y t
  rw [he]
  convert (K_differentiable Y _).hasDerivAt.comp T
    (((hasDerivAt_id T).sub_const Y).const_mul 2) using 1
  · rfl
  · dsimp; ring
lemma K_deriv_re_neg_before (Y z : ℝ) (hz : 0 ≤ z)
    (htop : Y+z/2 ≤ (5/2:ℝ)) : (deriv (K Y) z).re < 0 := by
  let f (s : ℝ) : ℂ := ((1-(s:ℂ)^2)/2)*deriv (deriv X) ((Y:ℂ)+(z:ℂ)/2*(1-(s:ℂ)^2))
  have hc : Continuous f := by
    have hg : Continuous (deriv (deriv X)) := by simpa only [iteratedDeriv_succ,iteratedDeriv_zero,iteratedDeriv_one] using (iteratedDeriv_X_differentiable 2).continuous
    dsimp [f]
    fun_prop
  have hf (s : ℝ) : (f s).re = ((1-s^2)/2)*(iteratedDeriv 2 X ((Y+z/2*(1-s^2):ℝ):ℂ)).re := by
    have he : f s = (((1-s^2)/2:ℝ):ℂ)*iteratedDeriv 2 X ((Y+z/2*(1-s^2):ℝ):ℂ) := by
      dsimp [f]
      push_cast
      simp only [iteratedDeriv_succ,iteratedDeriv_zero]
    rw [he,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im]
    ring
  have harg (s : ℝ) : Y+z/2*(1-s^2) ≤ (5/2:ℝ) := by
    nlinarith [mul_nonneg hz (sq_nonneg s)]
  have hh := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt (by norm_num : (0:ℝ)<1)
    (Complex.continuous_re.comp hc).continuousOn continuous_const.continuousOn
    (g := fun _ => (0:ℝ)) (fun s hs => by
      change (f s).re ≤ 0
      rw [hf]
      have hs2 : s^2≤1 := by nlinarith [hs.1,hs.2]
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith)
        (second_X_neg_before _ (harg s)).le)
    ⟨0,by norm_num,by
      change (f 0).re < 0
      rw [hf]
      have hh := second_X_neg_before _ (harg 0)
      norm_num at hh ⊢
      linarith⟩
  rw [intervalIntegral.integral_zero] at hh
  rw [K_deriv_integral]
  change (∫ s : ℝ in (0)..1, f s).re < 0
  change RCLike.re (∫ s : ℝ in (0)..1, f s) < 0
  rw [← intervalIntegral.intervalIntegral_re (hc.intervalIntegrable 0 1)]
  exact hh
lemma stationaryQ_real_integral (Y T : ℝ) :
    (stationaryQProd ((Y : ℂ),(T : ℂ))).re =
      ∫ s : ℝ in (0)..1,a (T-(T-Y)*s^2) := by
  rw [stationaryQ_eq_K]
  have he : 2*((T : ℂ)-(Y : ℂ)) = ((2*(T-Y) : ℝ) : ℂ) := by push_cast; ring
  rw [he,K_real_stationary_integral]
lemma stationaryQ_strictAntiOn_T (Y : ℝ) (hY : Y < y₀) :
    StrictAntiOn (fun t : ℝ => (stationaryQProd ((Y : ℂ),(t : ℂ))).re) (Icc y₀ (5/2 : ℝ)) := by
  have hc : Continuous (fun t : ℝ => (stationaryQProd ((Y : ℂ),(t : ℂ))).re) := by
    have hq := stationaryQ_contDiff_one.continuous
    fun_prop
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hc.continuousOn
  intro t ht
  have ht' : t ∈ Icc y₀ (5/2 : ℝ) := interior_subset ht
  have hd := (stationaryQ_second_hasDerivAt (Y : ℂ) (t : ℂ)).real_of_complex
  rw [hd.deriv]
  have hneg := K_deriv_re_neg_before Y (2*(t-Y)) (by linarith [ht'.1]) (by linarith [ht'.2])
  have he : (2*deriv (K Y) (2*((t : ℂ)-(Y : ℂ)))).re =
      2*(deriv (K Y) ((2*(t-Y) : ℝ) : ℂ)).re := by
    have hcast : 2*((t : ℂ)-(Y : ℂ)) = ((2*(t-Y) : ℝ) : ℂ) := by push_cast; ring
    rw [hcast]
    norm_num [Complex.mul_re]
  rw [he]
  linarith
lemma stationaryQ_pos_critical (Y : ℝ) (hY : Y < y₀) :
    0 < (stationaryQProd ((Y : ℂ),(y₀ : ℂ))).re := by
  rw [stationaryQ_real_integral]
  have haCont : Continuous a := a_continuous
  apply intervalIntegral.integral_pos zero_lt_one (by fun_prop)
  · intro s hs
    have harg : y₀-(y₀-Y)*s^2 < y₀ := by
      have hp := mul_pos (sub_pos.mpr hY) (sq_pos_of_pos hs.1)
      linarith
    exact (a_pos_before_y₀ _ harg).le
  · refine ⟨1,⟨zero_le_one,le_rfl⟩,?_⟩
    simpa using a_pos_before_y₀ Y hY

def stationaryQReal (Y T : ℝ) : ℝ := (stationaryQProd ((Y : ℂ),(T : ℂ))).re
lemma stationaryQReal_eq_K (Y T : ℝ) :
    stationaryQReal Y T = (K Y ((2*(T-Y) : ℝ) : ℂ)).re := by
  unfold stationaryQReal
  rw [stationaryQ_eq_K]
  congr 2
  push_cast
  ring
lemma stationaryIntegral_eq_stationaryQReal (Y T : ℝ) (hYT : Y < T) :
    (∫ v in Y..T,a v/Real.sqrt (T-v)) = 2*Real.sqrt (T-Y)*stationaryQReal Y T := by
  rw [stationary_integral_kernel Y T hYT,stationaryQReal_eq_K]
def stationaryParameterDomain : Set ℝ :=
  {Y | Y < y₀ ∧ stationaryQReal Y (5/2) < 0}
lemma stationaryQReal_joint_continuous : Continuous (fun p : ℝ × ℝ => stationaryQReal p.1 p.2) := by
  have hq := stationaryQ_contDiff_one.continuous
  change Continuous (fun p : ℝ × ℝ => (stationaryQProd ((p.1 : ℂ),(p.2 : ℂ))).re)
  fun_prop
lemma stationaryParameterDomain_isOpen : IsOpen stationaryParameterDomain := by
  have hp : Continuous (fun Y : ℝ => (Y,(5/2 : ℝ))) := continuous_id.prodMk continuous_const
  have hc : Continuous (fun Y : ℝ => stationaryQReal Y (5/2)) := by
    simpa only [Function.comp_def] using stationaryQReal_joint_continuous.comp hp
  exact (isOpen_lt continuous_id continuous_const).inter (isOpen_lt hc continuous_const)
lemma stationaryParameterDomain_contains (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    Y ∈ stationaryParameterDomain := by
  have hs := stationary_firstKernelEndpoint_unique Y hY
  have hc : Y+r Y/2 < (5/2 : ℝ) := by
    have hp : Real.pi^2/4 < (5/2 : ℝ) := by nlinarith [Real.pi_lt_d2,Real.pi_pos]
    exact lt_of_le_of_lt hs.1.2 hp
  have hanti := stationaryQ_strictAntiOn_T Y hY.2
  have hq : stationaryQReal Y (Y+r Y/2) = 0 := by
    have hi := hs.2.1
    rw [stationaryIntegral_eq_stationaryQReal Y _ (by linarith [r_pos Y hY])] at hi
    exact (mul_eq_zero.mp hi).resolve_left (ne_of_gt (mul_pos (by norm_num)
      (Real.sqrt_pos.mpr (by linarith [r_pos Y hY]))))
  refine ⟨hY.2,?_⟩
  have he := hanti ⟨hs.1.1.le,hc.le⟩ ⟨by linarith [y₀_lt_three_halves],le_rfl⟩ hc
  change stationaryQReal Y (5/2) < stationaryQReal Y (Y+r Y/2) at he
  rwa [hq] at he
lemma stationaryParameterDomain_exists_root (Y : ℝ) (hY : Y ∈ stationaryParameterDomain) :
    ∃ t : ℝ,t ∈ Ioo y₀ (5/2 : ℝ) ∧ stationaryQReal Y t = 0 := by
  have hp : Continuous (fun t : ℝ => (Y,t)) := continuous_const.prodMk continuous_id
  have hc : Continuous (stationaryQReal Y) := by
    simpa only [Function.comp_def] using stationaryQReal_joint_continuous.comp hp
  have hleft : 0 < stationaryQReal Y y₀ := stationaryQ_pos_critical Y hY.1
  have hb : y₀ ≤ (5/2 : ℝ) := by linarith [y₀_lt_three_halves]
  obtain ⟨t,ht,hzero⟩ := intermediate_value_Icc' hb hc.continuousOn
    (show (0 : ℝ) ∈ Icc (stationaryQReal Y (5/2)) (stationaryQReal Y y₀) from ⟨hY.2.le,hleft.le⟩)
  have hne₁ : t ≠ y₀ := by intro he; subst t; linarith
  have hne₂ : t ≠ (5/2 : ℝ) := by intro he; subst t; linarith [hY.2]
  exact ⟨t,⟨lt_of_le_of_ne ht.1 (Ne.symm hne₁),lt_of_le_of_ne ht.2 hne₂⟩,hzero⟩

end WP.Analysis
