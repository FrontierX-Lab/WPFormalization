import Mathlib

/-! Principal square-root bank limits and an integrable radial majorant
across the first branch point. -/
noncomputable section
namespace WP.Analysis
open Complex Filter MeasureTheory

lemma norm_one_sub_real_mul_unit_lower (t : ℝ) (ht : 0 ≤ t) (u : ℂ) (hu : ‖u‖ = 1) :
    |1-t| ≤ ‖1-(t:ℂ)*u‖ := by
  have hn : ‖(t:ℂ)*u‖=t := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht,hu,mul_one]
  simpa only [norm_one,hn] using abs_norm_sub_norm_le (1:ℂ) ((t:ℂ)*u)

lemma norm_inv_sqrt_one_sub_real_mul_unit_bound (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≠ 1)
    (u : ℂ) (hu : ‖u‖ = 1) :
    ‖(Complex.sqrt (1-(t:ℂ)*u))⁻¹‖ ≤ (Real.sqrt |1-t|)⁻¹ := by
  have ha : 0 < |1-t| := abs_pos.mpr (sub_ne_zero.mpr ht1.symm)
  have hn (z : ℂ) : ‖Complex.sqrt z‖ = Real.sqrt ‖z‖ := by
    rw [Complex.sqrt,show (2⁻¹:ℂ)=((1/2:ℝ):ℂ) by norm_num,
      Complex.norm_cpow_real,←Real.sqrt_eq_rpow]
  rw [norm_inv,hn]
  exact inv_anti₀ (Real.sqrt_pos.mpr ha)
    (Real.sqrt_le_sqrt (norm_one_sub_real_mul_unit_lower t ht u hu))

def lowerSqrtFormula (z : ℂ) : ℂ :=
  (Real.sqrt ((‖z‖+z.re)/2):ℂ)-(Real.sqrt ((‖z‖-z.re)/2):ℂ)*Complex.I

def upperSqrtFormula (z : ℂ) : ℂ :=
  (Real.sqrt ((‖z‖+z.re)/2):ℂ)+(Real.sqrt ((‖z‖-z.re)/2):ℂ)*Complex.I

lemma continuous_lowerSqrtFormula : Continuous lowerSqrtFormula := by
  unfold lowerSqrtFormula
  fun_prop
lemma continuous_upperSqrtFormula : Continuous upperSqrtFormula := by
  unfold upperSqrtFormula
  fun_prop

lemma tendsto_sqrt_neg_real_from_lower {α : Type*} {l : Filter α} (z : α → ℂ) (a : ℝ)
    (ha : 0 < a) (hz : Tendsto z l (nhds (-(a : ℂ)))) (him : ∀ᶠ x in l, (z x).im < 0) :
    Tendsto (fun x => Complex.sqrt (z x)) l (nhds (-Complex.I*(Real.sqrt a:ℂ))) := by
  have he : (fun x => Complex.sqrt (z x))=ᶠ[l](fun x => lowerSqrtFormula (z x)) := by
    filter_upwards [him] with x hx
    rw [Complex.sqrt_eq_real_add_ite,ite_eq_right (not_le_of_gt hx)]
    simp only [lowerSqrtFormula]
    ring
  have hv : lowerSqrtFormula (-(a : ℂ))=-Complex.I*(Real.sqrt a:ℂ) := by
    simp only [lowerSqrtFormula,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha,
      Complex.neg_re,Complex.ofReal_re]
    have he1 : (a+-a)/2=0 := by ring
    have he2 : (a- -a)/2=a := by ring
    rw [he1,he2,Real.sqrt_zero,Complex.ofReal_zero,zero_sub]
    ring
  rw [←hv]
  exact (continuous_lowerSqrtFormula.tendsto _ |>.comp hz).congr' he.symm

lemma tendsto_sqrt_neg_real_from_upper {α : Type*} {l : Filter α} (z : α → ℂ) (a : ℝ)
    (ha : 0 < a) (hz : Tendsto z l (nhds (-(a : ℂ)))) (him : ∀ᶠ x in l, 0 ≤ (z x).im) :
    Tendsto (fun x => Complex.sqrt (z x)) l (nhds (Complex.I*(Real.sqrt a:ℂ))) := by
  have he : (fun x => Complex.sqrt (z x))=ᶠ[l](fun x => upperSqrtFormula (z x)) := by
    filter_upwards [him] with x hx
    rw [Complex.sqrt_eq_real_add_ite,ite_eq_left hx]
    simp only [upperSqrtFormula,one_mul]
  have hv : upperSqrtFormula (-(a : ℂ))=Complex.I*(Real.sqrt a:ℂ) := by
    simp only [upperSqrtFormula,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha,
      Complex.neg_re,Complex.ofReal_re]
    have he1 : (a+-a)/2=0 := by ring
    have he2 : (a- -a)/2=a := by ring
    rw [he1,he2,Real.sqrt_zero,Complex.ofReal_zero,zero_add]
    ring
  rw [←hv]
  exact (continuous_upperSqrtFormula.tendsto _ |>.comp hz).congr' he.symm
lemma tendsto_inv_sqrt_upper_bank (t : ℝ) (ht : 1 < t) :
    Tendsto (fun θ:ℝ => (Complex.sqrt (1-(t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)))⁻¹)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((-Complex.I*(Real.sqrt (t-1):ℂ))⁻¹)) := by
  have hz : Tendsto (fun θ:ℝ => 1-(t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-((t-1:ℝ):ℂ))) := by
    have hc : Continuous (fun θ:ℝ => 1-(t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)) := by fun_prop
    convert hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1; simp
  have him : ∀ᶠ θ:ℝ in nhdsWithin 0 (Set.Ioi 0),
      (1-(t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)).im < 0 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0:ℝ) < Real.pi from Real.pi_pos)).filter_mono nhdsWithin_le_nhds]
      with θ hθ hθπ
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ hθπ
    simp [Complex.exp_im]
    nlinarith
  apply (tendsto_sqrt_neg_real_from_lower _ (t-1) (sub_pos.mpr ht) hz him).inv₀
  exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (sub_pos.mpr ht)).ne')

lemma tendsto_inv_sqrt_lower_bank (t : ℝ) (ht : 1 < t) :
    Tendsto (fun θ:ℝ => (Complex.sqrt (1-(t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)))⁻¹)
      (nhdsWithin 0 (Set.Iio 0))
      (nhds ((Complex.I*(Real.sqrt (t-1):ℂ))⁻¹)) := by
  have hz : Tendsto (fun θ:ℝ => 1-(t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))
      (nhdsWithin 0 (Set.Iio 0)) (nhds (-((t-1:ℝ):ℂ))) := by
    have hc : Continuous (fun θ:ℝ => 1-(t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)) := by fun_prop
    convert hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1; simp
  have him : ∀ᶠ θ:ℝ in nhdsWithin 0 (Set.Iio 0),
      0 ≤ (1-(t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)).im := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds (show -Real.pi < (0:ℝ) by linarith [Real.pi_pos])).filter_mono
        nhdsWithin_le_nhds]
      with θ hθ hθπ
    have hs : Real.sin θ < 0 := Real.sin_neg_of_neg_of_neg_pi_lt hθ hθπ
    simp [Complex.exp_im]
    nlinarith
  apply (tendsto_sqrt_neg_real_from_upper _ (t-1) (sub_pos.mpr ht) hz him).inv₀
  exact mul_ne_zero Complex.I_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (sub_pos.mpr ht)).ne')

lemma intervalIntegrable_inv_sqrt_abs_one_sub (A : ℝ) (hA : 1 ≤ A) :
    IntervalIntegrable (fun t:ℝ => (Real.sqrt |1-t|)⁻¹) volume 0 A := by
  have he (x : ℝ) (hx : 0 ≤ x) : (Real.sqrt x)⁻¹=x^(-1/2:ℝ) := by
    rw [Real.sqrt_eq_rpow,show (-1/2:ℝ)=-(1/2:ℝ) by ring,Real.rpow_neg hx]
  have hleft0 := (intervalIntegral.intervalIntegrable_rpow' (a:=0) (b:=1)
    (r:=(-1/2:ℝ)) (by norm_num)).comp_sub_left 1
  have hleft : IntervalIntegrable (fun t:ℝ => (1-t)^(-1/2:ℝ)) volume 0 1 := by
    simpa using hleft0.symm
  have hright0 := (intervalIntegral.intervalIntegrable_rpow' (a:=0) (b:=A-1)
    (r:=(-1/2:ℝ)) (by norm_num)).comp_sub_right 1
  have hright : IntervalIntegrable (fun t:ℝ => (t-1)^(-1/2:ℝ)) volume 1 A := by
    simpa using hright0
  apply IntervalIntegrable.trans (b:=1)
  · apply hleft.congr
    intro t ht
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    have ht' : t≤1 := ht.2
    dsimp only
    rw [abs_of_nonneg (sub_nonneg.mpr ht'),he _ (sub_nonneg.mpr ht')]
  · apply hright.congr
    intro t ht
    rw [Set.uIoc_of_le hA] at ht
    have ht' : 1≤t := ht.1.le
    dsimp only
    rw [abs_of_nonpos (sub_nonpos.mpr ht'),neg_sub,he _ (sub_nonneg.mpr ht')]

end WP.Analysis
