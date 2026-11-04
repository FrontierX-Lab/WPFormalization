import WPFormalization.RandomGeometry.GeneralPlanarDensityWeights

noncomputable section
namespace WP.RandomGeometry
open Set Filter
open scoped Topology

lemma general_planar_type_coefficient (P : PsiTheory) (k : ℕ) :
    2*realCoeff (iteratedDeriv 1 (Phi P 0)) k =
      generalPlanarTypeWeight P k 1 := by
  by_cases hk : 2 ≤ k
  · have hd : dimension 0 (k+1) = k-2 := by unfold dimension;omega
    rw [marked_realCoeff_volume,hd]
    simp only [generalPlanarTypeWeight,ite_eq_left hk,one_pow,mul_one,primitivePlanarWeight]
    ring
  · have hk0 : k=0 ∨ k=1 := by omega
    rcases hk0 with rfl|rfl
    all_goals
      simp only [realCoeff,coeff,Analysis.iteratedDeriv_iteratedDeriv_eq,
        PositiveConvolution.Phi_iteratedDeriv_zero]
      norm_num [shifted,Stable,generalPlanarTypeWeight]

lemma general_planar_phi_first_hasSum (P : PsiTheory) (x : ℝ)
    (hx : x ∈ Ico (0:ℝ) xCritical) :
    HasSum (fun k:ℕ => realCoeff (iteratedDeriv 1 (Phi P 0)) k*x^k) (markedF P 0 1 x) := by
  have hn : ‖(x:ℂ)‖ < xCritical := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2
  have ha (z:ℂ) (hz:‖z‖<xCritical) : AnalyticAt ℂ (iteratedDeriv 1 (Phi P 0)) z := by
    simpa only [iteratedDeriv_eq_iterate] using (Phi_analyticAt_open_disk P 0 z hz).iterated_deriv 1
  have hs := Complex.reCLM.hasSum (PositiveConvolution.analytic_ball_hasSum _ xCritical
    Analysis.xCritical_pos_parameter ha (x:ℂ) hn)
  change HasSum (fun k => (coeff (iteratedDeriv 1 (Phi P 0)) k*(x:ℂ)^k).re)
    (markedF P 0 1 x) at hs
  convert hs using 1
  funext k
  rw [←Complex.ofReal_pow]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,realCoeff]

theorem general_planar_total_weight_eq_phi_first (P : PsiTheory) (x : ℝ)
    (hx : x ∈ Ioo (0:ℝ) xCritical) :
    generalPlanarTotalWeight P x = 2*markedF P 0 1 x/x^2 := by
  have ht := (general_planar_phi_first_hasSum P x ⟨hx.1.le,hx.2⟩).mul_left 2
  have hterm (k:ℕ) : 2*(realCoeff (iteratedDeriv 1 (Phi P 0)) k*x^k) =
      generalPlanarTypeWeight P k x*x^2 := by
    rw [←mul_assoc,general_planar_type_coefficient]
    by_cases hk : 2 ≤ k
    · simp only [generalPlanarTypeWeight,ite_eq_left hk,one_pow,mul_one]
      have hpow : x^k = x^(k-2)*x^2 := by rw [←pow_add,Nat.sub_add_cancel hk]
      rw [hpow]
      ring
    · simp [generalPlanarTypeWeight,hk]
  simp_rw [hterm] at ht
  have he := ht.tsum_eq
  rw [tsum_mul_right] at he
  change generalPlanarTotalWeight P x*x^2 = _ at he
  exact (eq_div_iff (pow_ne_zero _ hx.1.ne')).mpr he

lemma general_planar_total_weight_one_le (P : PsiTheory) (x : ℝ)
    (hx : x ∈ Icc (0:ℝ) xCritical) :
    1 ≤ generalPlanarTotalWeight P x := by
  have hh := (general_planar_type_weight_summable P x hx).le_tsum 2
    (fun k _ => general_planar_type_weight_nonneg P k x hx.1)
  simpa only [general_planar_type_weight_two,generalPlanarTotalWeight] using hh

end WP.RandomGeometry
