import WPFormalization.Analysis.KernelMomentComplexification
/-! Every actual polynomial weight moment has a holomorphic extension on one
convex complex neighborhood of the physical interval. Taylor expansion at
w=1 identifies the first-root deflation with shifted normalized K jets;
formal inversion and the finite Stirling identity recover the true sums.
No uniform complex geometric bound or high-order asymptotic is assumed. -/
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace WP.Analysis

lemma iteratedDeriv_analyticAt_of_analyticAt (f : ℂ → ℂ) (k : ℕ) (z : ℂ) (hf : AnalyticAt ℂ f z) :
    AnalyticAt ℂ (iteratedDeriv k f) z := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ k ih => simpa only [iteratedDeriv_succ] using ih.deriv

lemma monomial_iteratedDeriv_coeff_of_analytic (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (k n : ℕ) :
    WP.coeff (fun z => z^k*iteratedDeriv k f z) n=(n.descFactorial k:ℂ)*WP.coeff f n := by
  have ht := congrArg (fun p : PowerSeries ℂ => PowerSeries.coeff n p)
    (taylor_mul (f:=fun z : ℂ => z^k) (g:=iteratedDeriv k f)
      (analyticAt_id.pow k) (iteratedDeriv_analyticAt_of_analyticAt f k 0 hf))
  rw [taylor_pow (f:=fun z : ℂ => z) analyticAt_id,taylor_id,WP.HigherOrder.taylor_iteratedDeriv,
    PowerSeries.coeff_X_pow_mul'] at ht
  simp only [taylor_coeff] at ht
  rw [ht]
  split_ifs with h
  · rw [PowerSeries.coeff_iterate_derivative,taylor_coeff,Nat.sub_add_cancel h]
    rw [←Nat.add_descFactorial_eq_ascFactorial,Nat.sub_add_cancel h]
  · rw [Nat.descFactorial_of_lt (by omega)]
    simp

lemma monomial_iteratedDeriv_coeff_hasSum_on_ball (f : ℂ → ℂ) (R : ℝ) (hR : 1<R)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 R)) (k : ℕ) :
    HasSum (fun n : ℕ => (n.descFactorial k:ℂ)*WP.coeff f n) (iteratedDeriv k f 1) := by
  have hA : ∀ z∈Metric.ball (0:ℂ) R,AnalyticAt ℂ f z :=
    fun z hz => hf.analyticAt (Metric.isOpen_ball.mem_nhds hz)
  have h0 : (0:ℂ)∈Metric.ball 0 R := by simpa only [Metric.mem_ball,dist_self] using zero_lt_one.trans hR
  have hD : DifferentiableOn ℂ (fun z => z^k*iteratedDeriv k f z) (Metric.ball 0 R) := by
    intro z hz
    exact ((analyticAt_id.pow k).mul (iteratedDeriv_analyticAt_of_analyticAt f k z (hA z hz))).differentiableAt.differentiableWithinAt
  have hs := hasSum_coeff_on_ball _ R hD 1 (by simpa using hR)
  simp only [one_pow,one_mul] at hs
  convert! hs using 1
  ext n
  rw [monomial_iteratedDeriv_coeff_of_analytic f (hA 0 h0) k n]
  simp only [one_pow,mul_one]

lemma weight_moment_eq_stirling_jets (j : ℕ) (Y : ℝ) (hY : Y∈Icc (0:ℝ) y₀) :
    WP.HigherOrder.kernelMoment j Y=(∑ k∈Finset.range (j+1),
      (Nat.stirlingSecond j k:ℂ)*iteratedDeriv k (weightGenerating Y) 1).re := by
  obtain ⟨R,M,hR,hM,hdata⟩ := weightGenerating_uniform_analytic
  have hf := ((hdata Y hY).1.mono Metric.ball_subset_closedBall)
  have hs : HasSum (fun n : ℕ => ∑ k∈Finset.range (j+1),
      (Nat.stirlingSecond j k:ℂ)*((n.descFactorial k:ℂ)*WP.coeff (weightGenerating Y) n))
      (∑ k∈Finset.range (j+1),(Nat.stirlingSecond j k:ℂ)*iteratedDeriv k (weightGenerating Y) 1) := by
    apply hasSum_sum
    intro k hk
    exact (monomial_iteratedDeriv_coeff_hasSum_on_ball _ R hR hf k).mul_left _
  have hp (n : ℕ) : (n:ℂ)^j=∑ k∈Finset.range (j+1),
      (Nat.stirlingSecond j k:ℂ)*(n.descFactorial k:ℂ) := by
    exact_mod_cast Nat.pow_eq_sum_stirlingSecond_mul_descFactorial n j
  have he : (fun n : ℕ => ∑ k∈Finset.range (j+1),
      (Nat.stirlingSecond j k:ℂ)*((n.descFactorial k:ℂ)*WP.coeff (weightGenerating Y) n))=
      (fun n : ℕ => (n:ℂ)^j*WP.coeff (weightGenerating Y) n) := by
    funext n
    simp_rw [←mul_assoc]
    rw [←Finset.sum_mul,←hp n]
  rw [he] at hs
  have hr := Complex.hasSum_re hs
  have hr' : HasSum (fun n : ℕ => (n:ℝ)^j*weight Y n)
      (∑ k∈Finset.range (j+1),(Nat.stirlingSecond j k:ℂ)*iteratedDeriv k (weightGenerating Y) 1).re := by
    convert! hr using 1
    ext n
    rw [show (n:ℂ)^j=(((n:ℝ)^j:ℝ):ℂ) by push_cast;rfl]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rw [←weightGenerating_coeff Y hY n]
    rfl
  exact hr'.tsum_eq
lemma deflatedBarK_shift_coeff (Y : ℝ) (hY : Y∈Icc (0:ℝ) y₀) (n : ℕ) :
    WP.coeff (fun v : ℂ => deflatedBarK Y (1+v)) n=
      -WP.coeff (fun v : ℂ => barK Y (1+v)) (n+1) := by
  have hmul : (fun v : ℂ => v*deflatedBarK Y (1+v))=(fun v => (-1:ℂ)*barK Y (1+v)) := by
    funext v
    have h := deflatedBarK_identity Y hY (1+v)
    have hv : 1-(1+v)=-v := by ring
    rw [hv] at h
    linear_combination -h
  have ha : AnalyticAt ℂ (fun v : ℂ => deflatedBarK Y (1+v)) 0 :=
    by
      have hi : AnalyticAt ℂ (fun v : ℂ => 1+v) 0 := analyticAt_const.add analyticAt_id
      simpa only [Function.comp_def] using ((deflatedBarK_differentiable Y).analyticAt (1+(0:ℂ))).comp hi
  have ht := congrArg (fun p : PowerSeries ℂ => PowerSeries.coeff (n+1) p)
    (taylor_mul (f:=fun v : ℂ => v) (g:=fun v => deflatedBarK Y (1+v)) analyticAt_id ha)
  rw [hmul,taylor_const_mul,taylor_id,PowerSeries.coeff_C_mul,PowerSeries.coeff_succ_X_mul] at ht
  simp only [taylor_coeff] at ht
  linear_combination -ht

def complexDeflatedCoeff (R : ℂ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  -regularizedKernelJet K R (n+1) 1 z/((n+1).factorial:ℂ)

def complexDeflatedSeries (R : ℂ → ℂ) (z : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun n => complexDeflatedCoeff R n z)

def complexWeightShiftCoeff (R : ℂ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  PowerSeries.coeff n ((complexDeflatedSeries R z)⁻¹)

lemma complexDeflatedCoeff_analyticOnNhd (Ω : Set ℂ) (R : ℂ → ℂ)
    (hjet : ∀ j : ℕ,AnalyticOnNhd ℂ (regularizedKernelJet K R j 1) Ω) (n : ℕ) :
    AnalyticOnNhd ℂ (complexDeflatedCoeff R n) Ω := by
  intro z hz
  exact (hjet (n+1) z hz).neg.div_const

lemma complexDeflatedCoeff_restrict_closed (R : ℂ → ℂ)
    (hjet : ∀ j : ℕ,∀ Y∈Icc (0:ℝ) y₀,regularizedKernelJet K R j 1 (Y:ℂ)=iteratedDeriv j (barK Y) 1)
    (n : ℕ) (Y : ℝ) (hY : Y∈Icc (0:ℝ) y₀) :
    complexDeflatedCoeff R n (Y:ℂ)=WP.coeff (fun v : ℂ => deflatedBarK Y (1+v)) n := by
  rw [deflatedBarK_shift_coeff Y hY n]
  unfold complexDeflatedCoeff WP.coeff
  rw [hjet (n+1) Y hY,iteratedDeriv_comp_const_add]
  simp only [add_zero,neg_div]

lemma complexWeightShiftCoeff_restrict_closed (R : ℂ → ℂ)
    (hjet : ∀ j : ℕ,∀ Y∈Icc (0:ℝ) y₀,regularizedKernelJet K R j 1 (Y:ℂ)=iteratedDeriv j (barK Y) 1)
    (n : ℕ) (Y : ℝ) (hY : Y∈Icc (0:ℝ) y₀) :
    complexWeightShiftCoeff R n (Y:ℂ)=WP.coeff (fun v : ℂ => weightGenerating Y (1+v)) n := by
  have he : complexDeflatedSeries R (Y:ℂ)=taylor (fun v : ℂ => deflatedBarK Y (1+v)) := by
    ext m
    simp only [complexDeflatedSeries,PowerSeries.coeff_mk,taylor_coeff]
    exact complexDeflatedCoeff_restrict_closed R hjet m Y hY
  have ha : AnalyticAt ℂ (fun v : ℂ => deflatedBarK Y (1+v)) 0 :=
    by
      have hi : AnalyticAt ℂ (fun v : ℂ => 1+v) 0 := analyticAt_const.add analyticAt_id
      simpa only [Function.comp_def] using ((deflatedBarK_differentiable Y).analyticAt (1+(0:ℂ))).comp hi
  have h0 : deflatedBarK Y (1+(0:ℂ))≠0 := by
    rw [add_zero]
    exact deflatedBarK_zero_free_unit Y hY 1 (by norm_num)
  rw [complexWeightShiftCoeff,he,←taylor_inv ha h0,taylor_coeff]
  rfl
lemma complexWeightShiftCoeff_recursion (R : ℂ → ℂ) (n : ℕ) (z : ℂ) :
    complexWeightShiftCoeff R n z=if n=0 then (complexDeflatedCoeff R 0 z)⁻¹ else
      -(complexDeflatedCoeff R 0 z)⁻¹*∑ i∈Finset.HasAntidiagonal.antidiagonal n,
        if i.2<n then complexDeflatedCoeff R i.1 z*complexWeightShiftCoeff R i.2 z else 0 := by
  rw [complexWeightShiftCoeff,PowerSeries.coeff_inv]
  simp only [complexDeflatedSeries,PowerSeries.constantCoeff_mk,PowerSeries.coeff_mk,complexWeightShiftCoeff]

lemma complexWeightShiftCoeff_analyticOnNhd (Ω : Set ℂ) (R : ℂ → ℂ)
    (hD : ∀ n : ℕ,AnalyticOnNhd ℂ (complexDeflatedCoeff R n) Ω)
    (hD0 : ∀ z∈Ω,complexDeflatedCoeff R 0 z≠0) :
    ∀ n : ℕ,AnalyticOnNhd ℂ (complexWeightShiftCoeff R n) Ω := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · subst n
      have he : complexWeightShiftCoeff R 0=(fun z => (complexDeflatedCoeff R 0 z)⁻¹) := by
        funext z
        simpa only [ite_true] using complexWeightShiftCoeff_recursion R 0 z
      rw [he]
      exact fun z hz => (hD 0 z hz).inv (hD0 z hz)
    · have he : complexWeightShiftCoeff R n=(fun z =>
          -(complexDeflatedCoeff R 0 z)⁻¹*∑ i∈Finset.HasAntidiagonal.antidiagonal n,
            if i.2<n then complexDeflatedCoeff R i.1 z*complexWeightShiftCoeff R i.2 z else 0) := by
        funext z
        simpa only [ite_eq_right hn] using complexWeightShiftCoeff_recursion R n z
      rw [he]
      intro z hz
      apply ((hD 0 z hz).inv (hD0 z hz)).neg.mul
      apply Finset.analyticAt_fun_sum
      intro i hi
      by_cases hlt : i.2<n
      · simp only [ite_eq_left hlt]
        exact (hD i.1 z hz).mul (ih i.2 hlt z hz)
      · simp only [ite_eq_right hlt]
        exact analyticAt_const

lemma weightGenerating_realCoefficients (Y : ℝ) (hY : Y∈Icc (0:ℝ) y₀) : RealCoefficients (weightGenerating Y) := by
  have hb := (barK_differentiable Y).analyticAt 0
  have h0 : barK Y 0≠0 := by rw [barK_zero_closed Y hY];norm_num
  have hr := realCoefficients_inv hb h0 (barK_realCoefficients Y)
  intro n
  have h := congrArg (fun p : PowerSeries ℂ => (PowerSeries.coeff n p).im) (weightGenerating_taylor Y hY)
  rw [sub_mul] at h
  simp only [taylor_coeff,map_sub,PowerSeries.coeff_C_mul,one_mul,Complex.sub_im] at h
  cases n with
  | zero => simpa only [PowerSeries.coeff_zero_X_mul,Complex.zero_im,hr 0,sub_zero] using h
  | succ n => simpa only [PowerSeries.coeff_succ_X_mul,taylor_coeff,hr (n+1),hr n,sub_self] using h

lemma weightGenerating_jet_one_im_zero (Y : ℝ) (hY : Y∈Icc (0:ℝ) y₀) (k : ℕ) :
    (iteratedDeriv k (weightGenerating Y) 1).im=0 := by
  obtain ⟨R,M,hR,hM,hdata⟩ := weightGenerating_uniform_analytic
  have hs := Complex.hasSum_im (monomial_iteratedDeriv_coeff_hasSum_on_ball (weightGenerating Y) R hR
    ((hdata Y hY).1.mono Metric.ball_subset_closedBall) k)
  have he : (fun n : ℕ => ((n.descFactorial k:ℂ)*WP.coeff (weightGenerating Y) n).im)=(fun _ => (0:ℝ)) := by
    funext n
    simp only [Complex.mul_im,Complex.natCast_re,Complex.natCast_im,weightGenerating_realCoefficients Y hY n,
      mul_zero,zero_mul,add_zero]
  rw [he] at hs
  exact hs.unique hasSum_zero

def complexKernelMoment (R : ℂ → ℂ) (j : ℕ) (z : ℂ) : ℂ :=
  ∑ k∈Finset.range (j+1),(Nat.stirlingSecond j k:ℂ)*(k.factorial:ℂ)*complexWeightShiftCoeff R k z

lemma complexKernelMoment_analyticOnNhd (Ω : Set ℂ) (R : ℂ → ℂ)
    (hW : ∀ n : ℕ,AnalyticOnNhd ℂ (complexWeightShiftCoeff R n) Ω) (j : ℕ) :
    AnalyticOnNhd ℂ (complexKernelMoment R j) Ω := by
  intro z hz
  apply Finset.analyticAt_fun_sum
  intro k hk
  exact analyticAt_const.mul (hW k z hz)

lemma complexKernelMoment_restrict_closed (R : ℂ → ℂ)
    (hjet : ∀ j : ℕ,∀ Y∈Icc (0:ℝ) y₀,regularizedKernelJet K R j 1 (Y:ℂ)=iteratedDeriv j (barK Y) 1)
    (j : ℕ) (Y : ℝ) (hY : Y∈Icc (0:ℝ) y₀) :
    complexKernelMoment R j (Y:ℂ)=(WP.HigherOrder.kernelMoment j Y:ℂ) := by
  have hsum : complexKernelMoment R j (Y:ℂ)=
      ∑ k∈Finset.range (j+1),(Nat.stirlingSecond j k:ℂ)*iteratedDeriv k (weightGenerating Y) 1 := by
    unfold complexKernelMoment
    apply Finset.sum_congr rfl
    intro k hk
    rw [complexWeightShiftCoeff_restrict_closed R hjet k Y hY,jet_eq_factorial_coeff_shift (weightGenerating Y) k 1]
    ring
  rw [hsum,weight_moment_eq_stirling_jets j Y hY]
  apply Complex.ext
  · simp
  · simp only [Complex.ofReal_im]
    change Complex.imCLM (∑ k∈Finset.range (j+1),(Nat.stirlingSecond j k:ℂ)*iteratedDeriv k (weightGenerating Y) 1)=0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro k hk
    simp only [Complex.imCLM_apply,Complex.mul_im,Complex.natCast_re,Complex.natCast_im,weightGenerating_jet_one_im_zero Y hY k,
      mul_zero,zero_mul,add_zero]
lemma common_holomorphic_all_kernel_moments :
    ∃ Ω : Set ℂ,IsOpen Ω ∧ Convex ℝ Ω ∧ (∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) ∧
      ∃ R Q Ahat : ℂ → ℂ,AnalyticOnNhd ℂ R Ω ∧ AnalyticOnNhd ℂ Q Ω ∧ AnalyticOnNhd ℂ Ahat Ω ∧
        (∀ Y∈Icc (0:ℝ) y₀,Q (Y:ℂ)=(((∑'l : ℕ,weight Y l):ℝ):ℂ) ∧ Ahat (Y:ℂ)=(A Y:ℂ)) ∧
        (∀ j : ℕ,AnalyticOnNhd ℂ (complexBMoment R j) Ω ∧
          AnalyticOnNhd ℂ (complexKernelMoment R j) Ω ∧
          ∀ Y∈Icc (0:ℝ) y₀,complexBMoment R j (Y:ℂ)=(WP.HigherOrder.bMoment j Y:ℂ) ∧
            complexKernelMoment R j (Y:ℂ)=(WP.HigherOrder.kernelMoment j Y:ℂ)) ∧
        (∀ n : ℕ,AnalyticOnNhd ℂ (complexThetaCoeff R n) Ω ∧ AnalyticOnNhd ℂ (complexWeightCoeff R n) Ω ∧
          ∀ Y∈Icc (0:ℝ) y₀,complexThetaCoeff R n (Y:ℂ)=(theta Y n:ℂ) ∧ complexWeightCoeff R n (Y:ℂ)=(weight Y n:ℂ)) ∧
        (∀ z∈Ω,Q z≠0 ∧ Ahat z≠0 ∧ complexAUnit z≠0 ∧ complexDeflatedCoeff R 0 z≠0) ∧
        (∀ Y∈Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ)) ∧ R y₀=0 ∧ deriv R y₀=-3 := by
  obtain ⟨U,hU,hconv,hcover,R,Q,Ahat,hR,hQ,hA,hmatch,hb,hcoeff,hunit,hraw,hR0,hR'⟩ :=
    common_holomorphic_kernel_moments
  have hjet := normalized_kernel_jets_holomorphic_on_common_domain U hU hcover R hR hR0 hraw
    (fun z hz => (hunit z hz).2.2)
  have hD := complexDeflatedCoeff_analyticOnNhd U R (fun j => (hjet j 1).1)
  have hDclosed : ∀ j : ℕ,∀ Y∈Icc (0:ℝ) y₀,complexDeflatedCoeff R j (Y:ℂ)=
      WP.coeff (fun v : ℂ => deflatedBarK Y (1+v)) j :=
    complexDeflatedCoeff_restrict_closed R (fun j Y hY => ((hjet j 1).2.2 Y hY).1)
  let V : Set ℂ := {z | z∈U ∧ complexDeflatedCoeff R 0 z≠0}
  have hVU : V⊆U := fun z hz => hz.1
  have hV : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    filter_upwards [hU.mem_nhds hz.1,(hD 0 z hz.1).continuousAt.eventually_ne hz.2] with ζ hζ hDζ
    exact ⟨hζ,hDζ⟩
  have hVcover : ∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈V := by
    intro Y hY
    refine ⟨hcover Y hY,?_⟩
    rw [hDclosed 0 Y hY]
    simp only [WP.coeff,iteratedDeriv_zero,Nat.factorial_zero,Nat.cast_one,div_one,add_zero]
    exact deflatedBarK_zero_free_unit Y hY 1 (by norm_num)
  obtain ⟨Ω,hΩ,hΩconv,hΩcover,hΩV⟩ := exists_convex_physical_neighborhood V hV hVcover
  have hΩU : Ω⊆U := hΩV.trans hVU
  have hW := complexWeightShiftCoeff_analyticOnNhd Ω R (fun n => (hD n).mono hΩU)
    (fun z hz => (hΩV hz).2)
  refine ⟨Ω,hΩ,hΩconv,hΩcover,R,Q,Ahat,hR.mono hΩU,hQ.mono hΩU,hA.mono hΩU,hmatch,?_,?_,?_,hraw,hR0,hR'⟩
  · intro j
    refine ⟨(hb j).1.mono hΩU,complexKernelMoment_analyticOnNhd Ω R hW j,?_⟩
    intro Y hY
    exact ⟨(hb j).2 Y hY,complexKernelMoment_restrict_closed R (fun k Y hY => ((hjet k 1).2.2 Y hY).1) j Y hY⟩
  · exact fun n => ⟨(hcoeff n).1.mono hΩU,(hcoeff n).2.1.mono hΩU,(hcoeff n).2.2⟩
  · intro z hz
    exact ⟨(hunit z (hΩU hz)).1,(hunit z (hΩU hz)).2.1,(hunit z (hΩU hz)).2.2,(hΩV hz).2⟩
end WP.Analysis
