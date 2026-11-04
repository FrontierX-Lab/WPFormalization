import WPFormalization.Analysis.QuadraticRemainder
import WPFormalization.Analysis.TaylorReality
import WPFormalization.Analysis.CoefficientScaling
noncomputable section
namespace WP.Analysis.PositiveProduct
open MeasureTheory Filter Set Complex
open scoped Topology

def factor (a : ℝ) (z : ℂ) : ℂ := 1-z/(a : ℂ)
def inverseFactor (a : ℝ) (z : ℂ) : ℂ := (factor a z)⁻¹
def finiteInverse (a : ℕ → ℝ) (s : Finset ℕ) (z : ℂ) : ℂ := ∏ i ∈ s, inverseFactor (a i) z

def NonnegativeCoefficients (f : ℂ → ℂ) : Prop :=
  RealCoefficients f ∧ ∀ n : ℕ, 0 ≤ WP.realCoeff f n

lemma real_const (c : ℝ) : RealCoefficients (fun _ : ℂ => (c : ℂ)) := by
  intro n
  rw [←taylor_coeff,taylor_const]
  simp only [PowerSeries.coeff_C]
  split_ifs <;> simp
lemma real_id : RealCoefficients (fun z : ℂ => z) := by
  intro n
  rw [←taylor_coeff,taylor_id]
  simp only [PowerSeries.coeff_X]
  split_ifs <;> simp
lemma factor_as_scaled (a : ℝ) : factor a = fun z : ℂ => 1-((a⁻¹ : ℝ) : ℂ)*z := by
  funext z
  simp only [factor,Complex.ofReal_inv,div_eq_mul_inv]
  ring
lemma factor_analytic (a : ℝ) : AnalyticAt ℂ (factor a) 0 := by
  rw [factor_as_scaled]
  exact analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
lemma factor_zero (a : ℝ) : factor a 0 = 1 := by simp [factor]
lemma factor_real (a : ℝ) : RealCoefficients (factor a) := by
  rw [factor_as_scaled]
  exact realCoefficients_sub analyticAt_const (analyticAt_const.mul analyticAt_id)
    (by simpa only [Complex.ofReal_one] using real_const 1)
    (realCoefficients_const_mul _ real_id)
lemma inverseFactor_analytic (a : ℝ) : AnalyticAt ℂ (inverseFactor a) 0 :=
  (factor_analytic a).inv (by rw [factor_zero]; exact one_ne_zero)
lemma inverseFactor_nonnegative (a : ℝ) (ha : 0 < a) : NonnegativeCoefficients (inverseFactor a) := by
  refine ⟨realCoefficients_inv (factor_analytic a) (by rw [factor_zero]; exact one_ne_zero) (factor_real a),?_⟩
  intro n
  have he : inverseFactor a = fun z : ℂ => (1-((a⁻¹ : ℝ) : ℂ)*z)⁻¹ := by
    funext z
    rw [inverseFactor,factor_as_scaled]
  rw [he,realCoeff_comp_mul_left (fun z : ℂ => (1-z)⁻¹) a⁻¹ n]
  apply mul_nonneg (pow_nonneg (inv_nonneg.mpr ha.le) n)
  have hp : 0<WP.realCoeff (fun z:ℂ=>(1-z)⁻¹) n := by simpa only [pow_one] using inverseLinear_coeff_pos 1 n zero_lt_one
  exact hp.le
lemma nonnegative_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hcf : NonnegativeCoefficients f) (hcg : NonnegativeCoefficients g) :
    NonnegativeCoefficients (fun z => f z*g z) := by
  refine ⟨realCoefficients_mul hf hg hcf.1 hcg.1,?_⟩
  intro n
  have he : WP.realCoeff (fun z => f z*g z) n =
      ∑ i ∈ Finset.range (n+1), WP.realCoeff f i*WP.realCoeff g (n-i) := by
    rw [←realTaylor_coeff (fun z => f z*g z) n]
    rw [realTaylor_mul hf hg hcf.1 hcg.1,PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [realTaylor_coeff]
  rw [he]
  exact Finset.sum_nonneg (fun i hi => mul_nonneg (hcf.2 i) (hcg.2 (n-i)))
lemma finiteInverse_nonnegative (a : ℕ → ℝ) (ha : ∀ i, 0 < a i) (s : Finset ℕ) :
    AnalyticAt ℂ (finiteInverse a s) 0 ∧ NonnegativeCoefficients (finiteInverse a s) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have he : finiteInverse a ∅ = fun _ : ℂ => 1 := by funext z; simp [finiteInverse]
      rw [he]
      refine ⟨analyticAt_const,by simpa only [Complex.ofReal_one] using real_const 1,?_⟩
      intro n
      change 0 ≤ (WP.coeff (fun _ : ℂ => 1) n).re
      rw [←taylor_coeff,taylor_const]
      simp only [PowerSeries.coeff_C]
      split_ifs <;> norm_num
  | @insert i s his ih =>
      have he : finiteInverse a (insert i s) = fun z => inverseFactor (a i) z*finiteInverse a s z := by
        funext z
        simp only [finiteInverse,Finset.prod_insert his]
      rw [he]
      exact ⟨(inverseFactor_analytic _).mul ih.1,
        nonnegative_mul (inverseFactor_analytic _) ih.1 (inverseFactor_nonnegative _ (ha i)) ih.2⟩
lemma ratio_norm (a : ℝ) (ha : 0 < a) (z : ℂ) : ‖z/(a : ℂ)‖=‖z‖/a := by
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha]
lemma factor_ne_zero_on_disk (a δ : ℝ) (ha : 0 < a) (hδa : δ ≤ a/2)
    (z : ℂ) (hz : ‖z‖ ≤ δ) : factor a z ≠ 0 := by
  have hw : ‖z/(a : ℂ)‖ ≤ 1/2 := by rw [ratio_norm a ha]; apply (div_le_iff₀ ha).mpr; linarith
  intro he
  have heq : z/(a : ℂ)=1 := by dsimp [factor] at he; linear_combination -he
  rw [heq,norm_one] at hw
  norm_num at hw
lemma inverseFactor_majorant (a δ : ℝ) (ha : 0 < a) (hδa : δ ≤ a/2)
    (z : ℂ) (hz : ‖z‖ ≤ δ) : ‖inverseFactor a z-1‖ ≤ 2*δ/a := by
  have hne := factor_ne_zero_on_disk a δ ha hδa z hz
  have hw : ‖z/(a : ℂ)‖ ≤ δ/a := by rw [ratio_norm a ha]; exact div_le_div_of_nonneg_right hz ha.le
  have hhalf : ‖z/(a : ℂ)‖ ≤ 1/2 := hw.trans ((div_le_iff₀ ha).mpr (by linarith))
  have hden : 1/2 ≤ ‖factor a z‖ := by
    have hd := norm_sub_norm_le (1 : ℂ) (z/(a : ℂ))
    rw [norm_one] at hd
    dsimp [factor]
    linarith
  have he : inverseFactor a z-1 = (z/(a : ℂ))/(factor a z) := by
    dsimp [inverseFactor,factor] at *
    field_simp
    <;> ring
  rw [he,norm_div]
  calc ‖z/(a : ℂ)‖/‖factor a z‖ ≤ ‖z/(a : ℂ)‖/(1/2) :=
        div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) hden
       _ ≤ (δ/a)/(1/2) := div_le_div_of_nonneg_right hw (by norm_num)
       _ = 2*δ/a := by ring
end WP.Analysis.PositiveProduct
namespace WP.Analysis.PositiveProduct
open MeasureTheory Filter Set Complex
open scoped Topology
lemma locally_uniform_inverse_product (f : ℂ → ℂ) (a : ℕ → ℝ) (a₀ ρ : ℝ)
    (ha₀ : 0 < a₀) (hρ : 0 < ρ) (ha : ∀ i, a₀ ≤ a i)
    (hSum : Summable (fun i : ℕ => 1/a i))
    (hProd : ∀ z : ℂ, ‖z‖ < ρ → HasProd (fun i : ℕ => factor (a i) z) (f z)) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ρ ∧ (∀ i, δ ≤ a i/2) ∧ (∀ z : ℂ, ‖z‖ ≤ δ → f z ≠ 0) ∧
      HasProdUniformlyOn (fun i z => inverseFactor (a i) z) (fun z => (f z)⁻¹) (Metric.closedBall 0 δ) := by
  let δ : ℝ := min a₀ ρ/2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδρ : δ < ρ := by dsimp [δ]; linarith [min_le_right a₀ ρ]
  have hai (i : ℕ) : 0 < a i := lt_of_lt_of_le ha₀ (ha i)
  have hδa (i : ℕ) : δ ≤ a i/2 := by dsimp [δ]; linarith [min_le_left a₀ ρ,ha i]
  have hu : Summable (fun i : ℕ => 2*δ/a i) := by
    simpa only [div_eq_mul_inv,one_mul] using hSum.mul_left (2*δ)
  have hMajor : ∀ᶠ i : ℕ in cofinite, ∀ z ∈ Metric.closedBall (0 : ℂ) δ,
      ‖inverseFactor (a i) z-1‖ ≤ 2*δ/a i := Eventually.of_forall (fun i z hz =>
    inverseFactor_majorant (a i) δ (hai i) (hδa i) z (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz))
  have hCont (i : ℕ) : ContinuousOn (fun z => inverseFactor (a i) z-1) (Metric.closedBall (0 : ℂ) δ) := by
    intro z hz
    have hn := factor_ne_zero_on_disk (a i) δ (hai i) (hδa i) z (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz)
    have hc : ContinuousAt (factor (a i)) z := by unfold factor; fun_prop
    have hi : ContinuousAt (fun w=>inverseFactor (a i) w-1) z := (hc.inv₀ hn).sub_const 1
    exact hi.continuousWithinAt
  have hU := Summable.hasProdUniformlyOn_one_add (f := fun (i : ℕ) (z : ℂ) => inverseFactor (a i) z-1)
    (u := fun i : ℕ => 2*δ/a i) (isCompact_closedBall (0 : ℂ) δ) hu hMajor hCont
  have hterm (i : ℕ) (z : ℂ) : 1+(inverseFactor (a i) z-1) = inverseFactor (a i) z := by ring
  simp only [hterm] at hU
  have hPoint (z : ℂ) (hz : ‖z‖ ≤ δ) : f z ≠ 0 ∧ (∏' i : ℕ, inverseFactor (a i) z) = (f z)⁻¹ := by
    have hzK : z ∈ Metric.closedBall (0 : ℂ) δ := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
    have hOriginal := hProd z (lt_of_le_of_lt hz hδρ)
    have hInverse := hU.hasProd hzK
    have hMult := hOriginal.mul hInverse
    have hOne : HasProd (fun i : ℕ => factor (a i) z*inverseFactor (a i) z) (1 : ℂ) := by
      convert (hasProd_one : HasProd (fun _ : ℕ => (1 : ℂ)) 1) using 1
      funext i
      simp only [inverseFactor,mul_inv_cancel₀ (factor_ne_zero_on_disk (a i) δ (hai i) (hδa i) z hz)]
    have he := hMult.unique hOne
    have hfz : f z ≠ 0 := by
      intro hzero
      rw [hzero,zero_mul] at he
      exact zero_ne_one he
    refine ⟨hfz,?_⟩
    apply mul_left_cancel₀ hfz
    rw [he,mul_inv_cancel₀ hfz]
  refine ⟨δ,hδ,hδρ,hδa,fun z hz => (hPoint z hz).1,?_⟩
  exact hU.congr_right (fun z hz => (hPoint z (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz)).2)
end WP.Analysis.PositiveProduct
namespace WP.Analysis.PositiveProduct
open MeasureTheory Filter Set Complex
open scoped Topology
lemma inverseFactor_analyticAt (a : ℝ) (z : ℂ) (hne : factor a z ≠ 0) :
    AnalyticAt ℂ (inverseFactor a) z := by
  have hf : AnalyticAt ℂ (factor a) z := by
    rw [factor_as_scaled]
    exact analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
  exact hf.inv hne
lemma finiteInverse_analyticAt (a : ℕ → ℝ) (s : Finset ℕ) (z : ℂ)
    (hne : ∀ i ∈ s, factor (a i) z ≠ 0) : AnalyticAt ℂ (finiteInverse a s) z := by
  exact s.analyticAt_fun_prod (fun i hi => inverseFactor_analyticAt _ _ (hne i hi))
end WP.Analysis.PositiveProduct
namespace WP.Analysis.PositiveProduct
open MeasureTheory Filter Set Complex
open scoped Topology
lemma coefficients_tendsto_inverse (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (a : ℕ → ℝ) (ha : ∀ i, 0 < a i) (δ : ℝ) (hδ : 0 < δ) (hδa : ∀ i, δ ≤ a i/2)
    (hNZ : ∀ z : ℂ, ‖z‖ ≤ δ → f z ≠ 0)
    (hU : HasProdUniformlyOn (fun i z => inverseFactor (a i) z) (fun z => (f z)⁻¹) (Metric.closedBall 0 δ))
    (n : ℕ) : Tendsto (fun s : Finset ℕ => WP.coeff (finiteInverse a s) n) atTop
      (𝓝 (WP.coeff (fun z => (f z)⁻¹) n)) := by
  have hInvA : AnalyticAt ℂ (fun z => (f z)⁻¹) 0 := (hf.analyticAt 0).inv hf0
  have hInvD : DifferentiableOn ℂ (fun z => (f z)⁻¹) (Metric.closedBall 0 δ) := by
    intro z hz
    exact ((hf.analyticAt z).inv (hNZ z (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz))).differentiableAt.differentiableWithinAt
  have hFD (s : Finset ℕ) : DifferentiableOn ℂ (finiteInverse a s) (Metric.closedBall 0 δ) := by
    intro z hz
    exact (finiteInverse_analyticAt a s z (fun i hi => factor_ne_zero_on_disk (a i) δ (ha i) (hδa i) z
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz))).differentiableAt.differentiableWithinAt
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hε' : 0 < (ε/2)*δ^n := by positivity
  have hUniform := Metric.tendstoUniformlyOn_iff.mp hU.tendstoUniformlyOn ((ε/2)*δ^n) hε'
  filter_upwards [hUniform] with s hs
  have hSub : WP.coeff (fun z => finiteInverse a s z-(f z)⁻¹) n =
      WP.coeff (finiteInverse a s) n-WP.coeff (fun z => (f z)⁻¹) n := by
    have he := congrArg (fun p : PowerSeries ℂ => PowerSeries.coeff n p)
      (taylor_sub (finiteInverse_nonnegative a ha s).1 hInvA)
    simpa only [map_sub,taylor_coeff] using he
  have hCircle : ∀ z ∈ Metric.sphere (0 : ℂ) δ,
      ‖finiteInverse a s z-(f z)⁻¹‖ ≤ (ε/2)*δ^n := by
    intro z hz
    have hb := hs z (Metric.sphere_subset_closedBall hz)
    change dist ((f z)⁻¹) (finiteInverse a s z) < (ε/2)*δ^n at hb
    rw [dist_comm,dist_eq_norm] at hb
    exact hb.le
  have hCauchy := coeff_norm_le_circle_bound (fun z => finiteInverse a s z-(f z)⁻¹) δ ((ε/2)*δ^n)
    hδ ((hFD s).sub hInvD) hCircle n
  rw [dist_eq_norm,←hSub]
  calc ‖WP.coeff (fun z => finiteInverse a s z-(f z)⁻¹) n‖ ≤ ((ε/2)*δ^n)/δ^n := hCauchy
       _ = ε/2 := by field_simp
       _ < ε := by linarith
end WP.Analysis.PositiveProduct
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology
lemma inverse_coeff_nonnegative_of_positive_product (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hf0 : f 0 = 1)
    (a : ℕ → ℝ) (a₀ ρ : ℝ) (ha₀ : 0 < a₀) (hρ : 0 < ρ) (ha : ∀ i, a₀ ≤ a i)
    (hSum : Summable (fun i : ℕ => (a i)⁻¹))
    (hProd : ∀ z : ℂ, ‖z‖ < ρ → HasProd (fun i : ℕ => 1-z/(a i : ℂ)) (f z)) :
    ∀ n : ℕ, (WP.coeff (fun z => (f z)⁻¹) n).im = 0 ∧ 0 ≤ (WP.coeff (fun z => (f z)⁻¹) n).re := by
  have hai (i : ℕ) : 0 < a i := lt_of_lt_of_le ha₀ (ha i)
  have hSum' : Summable (fun i : ℕ => 1/a i) := by simpa only [one_div] using hSum
  obtain ⟨δ,hδ,hδρ,hδa,hNZ,hU⟩ := PositiveProduct.locally_uniform_inverse_product f a a₀ ρ ha₀ hρ ha hSum' hProd
  intro n
  have ht := PositiveProduct.coefficients_tendsto_inverse f hf (by rw [hf0]; exact one_ne_zero) a hai δ hδ hδa hNZ hU n
  have hIm : Tendsto (fun s : Finset ℕ => (WP.coeff (PositiveProduct.finiteInverse a s) n).im) atTop
      (𝓝 (WP.coeff (fun z => (f z)⁻¹) n).im) := Complex.continuous_im.continuousAt.tendsto.comp ht
  have he : (fun s : Finset ℕ => (WP.coeff (PositiveProduct.finiteInverse a s) n).im) = fun _ => (0 : ℝ) := by
    funext s
    exact (PositiveProduct.finiteInverse_nonnegative a hai s).2.1 n
  rw [he] at hIm
  have hRe : Tendsto (fun s : Finset ℕ => (WP.coeff (PositiveProduct.finiteInverse a s) n).re) atTop
      (𝓝 (WP.coeff (fun z => (f z)⁻¹) n).re) := Complex.continuous_re.continuousAt.tendsto.comp ht
  refine ⟨tendsto_nhds_unique hIm tendsto_const_nhds,?_⟩
  exact (isClosed_Ici : IsClosed (Ici (0 : ℝ))).mem_of_tendsto hRe
    (Eventually.of_forall (fun s => (PositiveProduct.finiteInverse_nonnegative a hai s).2.2 n))
end WP.Analysis
