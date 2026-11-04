import WPFormalization.Analysis.StationaryPolynomialIntegral
import WPFormalization.Analysis.GaussianModelRemainder
import WPFormalization.Analysis.FiniteWatson
import WPFormalization.HigherOrder.FiniteAsymptoticUniqueness
/-! Exact rescaling, finite amplitude integration and uniqueness for the same genuine stationary model. All proofs use standard axioms; no stationary-phase expansion or coefficient identity is assumed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace WP.Analysis
lemma stationary_joint_cauchy_family_below (β:ℂ→ℂ) (A:ℂ × ℂ→ℂ)
    (R0:ℝ) (hR0:0<R0) (hβ:AnalyticAt ℂ β 0) (hA:AnalyticAt ℂ A (0,0)) (hβ0:β 0=0) :
    ∃R M:ℝ,0<R ∧ R≤R0 ∧ 0<M ∧
      (∀τ u:ℂ,‖τ‖≤R→‖u‖≤R→AnalyticAt ℂ β u ∧ AnalyticAt ℂ A (τ,u) ∧ ‖β u‖≤1/4 ∧ ‖A (τ,u)‖≤M) ∧
      (∀w:ℝ,DifferentiableOn ℂ
        (fun τ:ℂ=>Complex.exp ((w:ℂ)^2*β (τ*(w:ℂ)))*A (τ,τ*(w:ℂ)))
          (Metric.closedBall 0 (R/(1+|w|)))) ∧
      ∀w:ℝ,∀z∈Metric.sphere (0:ℂ) (R/(1+|w|)),
        ‖Complex.exp ((w:ℂ)^2*β (z*(w:ℂ)))*A (z,z*(w:ℂ))‖≤M*Real.exp (w^2/4) := by
  let M:ℝ:=‖A (0,0)‖+1
  have hM:0<M:=by dsimp[M];positivity
  have hβn:‖β 0‖<(1/4:ℝ):=by simp[hβ0]
  have hAn:‖A (0,0)‖<M:=by dsimp[M];linarith
  have hp0:∀ᶠz:ℂ × ℂ in 𝓝 (0,0),AnalyticAt ℂ β z.2 ∧ AnalyticAt ℂ A z ∧ ‖β z.2‖≤1/4 ∧ ‖A z‖≤M := by
    have ht:Tendsto (fun z:ℂ × ℂ=>z.2) (𝓝 (0,0)) (𝓝 (0:ℂ)):=continuous_snd.continuousAt.tendsto
    filter_upwards [ht.eventually hβ.eventually_analyticAt,hA.eventually_analyticAt,
      ht.eventually (hβ.continuousAt.norm.tendsto.eventually (eventually_lt_nhds hβn)),
      hA.continuousAt.norm.tendsto.eventually (eventually_lt_nhds hAn)] with z h1 h2 h3 h4
    exact ⟨h1,h2,h3.le,h4.le⟩
  obtain ⟨ρ,hρ,hball⟩:=Metric.eventually_nhds_iff.mp hp0
  let R:ℝ:=min (ρ/2) R0
  have hR:0<R:=lt_min (half_pos hρ) hR0
  have hRρ:R<ρ:=(min_le_left _ _).trans_lt (by linarith)
  have hRR0:R≤R0:=min_le_right _ _
  have hstate(τ u:ℂ)(hτ:‖τ‖≤R)(hu:‖u‖≤R):
      AnalyticAt ℂ β u ∧ AnalyticAt ℂ A (τ,u) ∧ ‖β u‖≤1/4 ∧ ‖A (τ,u)‖≤M := by
    apply hball (y:=(τ,u))
    simpa only[Prod.dist_eq,dist_zero_right,max_lt_iff] using And.intro (hτ.trans_lt hRρ) (hu.trans_lt hRρ)
  have hpoint(w:ℝ)(z:ℂ)(hz:‖z‖≤R/(1+|w|)):
      AnalyticAt ℂ β (z*(w:ℂ)) ∧ AnalyticAt ℂ A (z,z*(w:ℂ)) ∧ ‖β (z*(w:ℂ))‖≤1/4 ∧ ‖A (z,z*(w:ℂ))‖≤M := by
    have hs:0<1+|w|:=by positivity
    have hzR:‖z‖≤R := hz.trans ((div_le_iff₀ hs).mpr (by nlinarith[abs_nonneg w]))
    have huR:‖z*(w:ℂ)‖≤R := by
      rw[norm_mul,Complex.norm_real,Real.norm_eq_abs]
      apply (mul_le_mul_of_nonneg_right hz (abs_nonneg w)).trans
      rw[div_mul_eq_mul_div]
      apply (div_le_iff₀ hs).mpr
      nlinarith
    exact hstate z (z*(w:ℂ)) hzR huR
  refine ⟨R,M,hR,hRR0,hM,hstate,?_,?_⟩
  · intro w z hz
    have ht:=hpoint w z (by simpa only[Metric.mem_closedBall,dist_zero_right] using hz)
    have hm:AnalyticAt ℂ (fun τ:ℂ=>τ*(w:ℂ)) z:=analyticAt_id.mul analyticAt_const
    have hc:AnalyticAt ℂ (fun τ:ℂ=>(τ,τ*(w:ℂ))) z:=analyticAt_id.prod hm
    exact (((analyticAt_const.mul (ht.1.comp (f:=fun τ:ℂ=>τ*(w:ℂ)) hm)).cexp).mul
      (ht.2.1.comp (f:=fun τ:ℂ=>(τ,τ*(w:ℂ))) hc)).differentiableAt.differentiableWithinAt
  · intro w z hz
    have ht:=hpoint w z (by simpa only[Metric.mem_sphere,dist_zero_right] using le_of_eq hz)
    have he:(((w:ℂ)^2*β (z*(w:ℂ))).re)≤w^2/4 := by
      calc _ ≤ ‖(w:ℂ)^2*β (z*(w:ℂ))‖:=Complex.re_le_norm _
           _ = w^2*‖β (z*(w:ℂ))‖:=by rw[norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
           _ ≤ _:=by nlinarith[ht.2.2.1,sq_nonneg w]
    rw[norm_mul,Complex.norm_exp]
    exact (mul_le_mul (Real.exp_le_exp.mpr he) ht.2.2.2 (norm_nonneg _) (Real.exp_pos _).le).trans_eq (by ring)

lemma real_interval_integral_pos_rescale (f:ℝ→ℂ) (τ r:ℝ) (hτ:0<τ) (hr:0≤r) :
    (∫w:ℝ in Icc (-(r/τ)) (r/τ),f (τ*w))=
      τ⁻¹ • ∫u:ℝ in Icc (-r) r,f u := by
  have h1:-(r/τ)≤r/τ:=by linarith[div_nonneg hr hτ.le]
  have h2:-r≤r:=by linarith
  rw[integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le h1,
    intervalIntegral.integral_comp_mul_left f hτ.ne']
  have he1:τ* -(r/τ)= -r:=by field_simp
  have he2:τ*(r/τ)=r:=by field_simp
  rw[he1,he2,intervalIntegral.integral_of_le h2,←integral_Icc_eq_integral_Ioc]

lemma stationary_real_integral_rescale (β:ℂ→ℂ) (A:ℂ × ℂ→ℂ) (τ r:ℝ) (hτ:0<τ) (hr:0≤r) :
    (∫w:ℝ in Icc (-(r/τ)) (r/τ),Real.exp (-(1/2:ℝ)*w^2) •
      (Complex.exp ((w:ℂ)^2*β ((τ:ℂ)*(w:ℂ)))*A ((τ:ℂ),(τ:ℂ)*(w:ℂ))))=
      τ⁻¹ • ∫u:ℝ in Icc (-r) r,
        Complex.exp (((u:ℂ)/(τ:ℂ))^2*(β (u:ℂ)-(1/2:ℂ)))*A ((τ:ℂ),(u:ℂ)) := by
  let f:ℝ→ℂ:=fun u=>Complex.exp (((u:ℂ)/(τ:ℂ))^2*(β (u:ℂ)-(1/2:ℂ)))*A ((τ:ℂ),(u:ℂ))
  rw[←real_interval_integral_pos_rescale f τ r hτ hr]
  apply setIntegral_congr_fun measurableSet_Icc
  intro w hw
  dsimp only[f]
  rw[Complex.ofReal_mul,mul_div_cancel_left₀ _ (by exact_mod_cast hτ.ne')]
  simp only[Complex.real_smul]
  rw[Complex.ofReal_exp,←mul_assoc,←Complex.exp_add]
  congr 2
  push_cast
  ring

lemma stationary_inverse_sqrt_rescale (β:ℂ→ℂ) (A:ℂ × ℂ→ℂ) (R h:ℝ) (hR:0≤R) (hh:0<h) :
    (∫w:ℝ in Icc (-(R/(4*(1/Real.sqrt h)))) (R/(4*(1/Real.sqrt h))),Real.exp (-(1/2:ℝ)*w^2) •
      (Complex.exp ((w:ℂ)^2*β (((1/Real.sqrt h:ℝ):ℂ)*(w:ℂ)))*
        A (((1/Real.sqrt h:ℝ):ℂ),((1/Real.sqrt h:ℝ):ℂ)*(w:ℂ))))=
      (Real.sqrt h:ℂ)*(∫u:ℝ in Icc (-(R/4)) (R/4),
        Complex.exp ((h:ℂ)*((u:ℂ)^2*(β (u:ℂ)-(1/2:ℂ))))*
          A (((1/Real.sqrt h:ℝ):ℂ),(u:ℂ))) := by
  have hτ:0<1/Real.sqrt h:=by positivity
  have he:=stationary_real_integral_rescale β A (1/Real.sqrt h) (R/4) hτ (by positivity)
  have hr:R/4/(1/Real.sqrt h)=R/(4*(1/Real.sqrt h)):=by ring
  rw[hr] at he
  rw[he]
  simp only[one_div,inv_inv,Complex.real_smul]
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro u hu
  dsimp only
  apply congrArg (fun z:ℂ=>Complex.exp z*A (((Real.sqrt h)⁻¹:ℝ),(u:ℂ)))
  have hs:((Real.sqrt h:ℂ))^2=(h:ℂ):=by exact_mod_cast Real.sq_sqrt hh.le
  push_cast
  rw[div_pow,inv_pow,hs,div_inv_eq_mul]
  ring

lemma symmetric_set_integral_eq_interval (f:ℝ→ℂ) (r:ℝ) (hr:0≤r) :
    (∫u:ℝ in Icc (-r) r,f u)=∫u:ℝ in (-r)..r,f u := by
  rw[integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le (by linarith:-r≤r)]

lemma finite_stationary_amplitude_integral (φ:ℂ→ℂ) (a:ℕ→ℂ→ℂ) (N:ℕ) (h r R:ℝ) (t:ℂ)
    (hr:0≤r) (hrR:r<R) (hφ:DifferentiableOn ℂ φ (Metric.ball 0 R))
    (ha:∀s≤N,DifferentiableOn ℂ (a s) (Metric.ball 0 R)) :
    (∫u:ℝ in Icc (-r) r,Complex.exp ((h:ℂ)*φ (u:ℂ))*
      (∑s∈Finset.range (N+1),t^(2*s)*a s (u:ℂ)))=
      ∑s∈Finset.range (N+1),t^(2*s)*(∫u:ℝ in (-r)..r,Complex.exp ((h:ℂ)*φ (u:ℂ))*a s (u:ℂ)) := by
  have hmap:MapsTo (fun u:ℝ=>(u:ℂ)) (Icc (-r) r) (Metric.ball 0 R) := by
    intro u hu
    rw[Metric.mem_ball,dist_zero_right,Complex.norm_real,Real.norm_eq_abs]
    exact (abs_le.mpr ⟨by linarith[hu.1],hu.2⟩).trans_lt hrR
  have hφc:ContinuousOn (fun u:ℝ=>φ (u:ℂ)) (Icc (-r) r):=
    hφ.continuousOn.comp Complex.continuous_ofReal.continuousOn hmap
  have hac(s:ℕ)(hs:s≤N):ContinuousOn (fun u:ℝ=>a s (u:ℂ)) (Icc (-r) r):=
    (ha s hs).continuousOn.comp Complex.continuous_ofReal.continuousOn hmap
  have hec:ContinuousOn (fun u:ℝ=>Complex.exp ((h:ℂ)*φ (u:ℂ))) (Icc (-r) r):=
    Complex.continuous_exp.comp_continuousOn (hφc.const_mul _)
  have hi(s:ℕ)(hs:s∈Finset.range (N+1)):IntegrableOn
      (fun u:ℝ=>t^(2*s)*(Complex.exp ((h:ℂ)*φ (u:ℂ))*a s (u:ℂ))) (Icc (-r) r) :=
    ((hec.mul (hac s (Nat.le_of_lt_succ (Finset.mem_range.mp hs)))).const_mul _).integrableOn_Icc
  have he:(fun u:ℝ=>Complex.exp ((h:ℂ)*φ (u:ℂ))*(∑s∈Finset.range (N+1),t^(2*s)*a s (u:ℂ)))=
      (fun u:ℝ=>∑s∈Finset.range (N+1),t^(2*s)*(Complex.exp ((h:ℂ)*φ (u:ℂ))*a s (u:ℂ))) := by
    funext u
    rw[Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  rw[he,integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro s hs
    rw[integral_const_mul,symmetric_set_integral_eq_interval _ r hr]
  · exact hi

lemma inverse_sqrt_stationary_threshold (R:ℝ) (hR:0<R) :
    ∃H:ℝ,0<H ∧ ∀h:ℝ,H≤h→0<1/Real.sqrt h ∧ 1/Real.sqrt h≤ min 1 (R/4) := by
  let H:ℝ:=max 1 (16/R^2)
  have hH:0<H:=zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨H,hH,?_⟩
  intro h hHh
  have hh1:1≤h:=(le_max_left _ _).trans hHh
  have hh:0<h:=zero_lt_one.trans_le hh1
  have hs:0<Real.sqrt h:=Real.sqrt_pos.mpr hh
  have hs1:1≤Real.sqrt h:=by nlinarith[Real.sq_sqrt hh.le]
  have hhR:16/R^2≤h:=(le_max_right _ _).trans hHh
  have hprod:4≤R*Real.sqrt h := by
    have hR2:0<R^2:=by positivity
    have he:16≤h*R^2:=(div_le_iff₀ hR2).mp hhR
    have hsq:=Real.sq_sqrt hh.le
    have hnon:0≤R*Real.sqrt h:=by positivity
    nlinarith[sq_nonneg (R*Real.sqrt h)]
  refine ⟨by positivity,le_min ?_ ?_⟩
  · exact (div_le_iff₀ hs).mpr (by simpa using hs1)
  · apply (div_le_iff₀ hs).mpr
    nlinarith

lemma inverse_sqrt_even_power (h:ℝ) (hh:0<h) (n:ℕ) :
    (((1/Real.sqrt h:ℝ):ℂ))^(2*n)=1/(h:ℂ)^n ∧
      (1/Real.sqrt h:ℝ)^(2*n)=1/h^n := by
  have hs:((1/Real.sqrt h:ℝ):ℂ)^2=1/(h:ℂ) := by
    push_cast
    rw[div_pow,one_pow]
    congr 1
    exact_mod_cast Real.sq_sqrt hh.le
  have hsR:(1/Real.sqrt h:ℝ)^2=1/h:=by rw[div_pow,one_pow,Real.sq_sqrt hh.le]
  constructor
  · rw[pow_mul,hs,div_pow,one_pow]
  · rw[pow_mul,hsR,div_pow,one_pow]

lemma stationary_finite_model_rescaling (φ β:ℂ→ℂ) (A:ℂ × ℂ→ℂ) (a:ℕ→ℂ→ℂ)
    (N:ℕ) (R h S:ℝ) (hR:0<R) (hh:0<h) (hRS:R/4<S)
    (hφ:DifferentiableOn ℂ φ (Metric.ball 0 S))
    (ha:∀s≤N,DifferentiableOn ℂ (a s) (Metric.ball 0 S))
    (hA:∀τ u:ℂ,A (τ,u)=∑s∈Finset.range (N+1),τ^(2*s)*a s u)
    (hfac:∀u∈Icc (-(R/4)) (R/4),φ (u:ℂ)=(u:ℂ)^2*(β (u:ℂ)-(1/2:ℂ))) :
    (∫w:ℝ in Icc (-(R/(4*(1/Real.sqrt h)))) (R/(4*(1/Real.sqrt h))),Real.exp (-(1/2:ℝ)*w^2) •
      (Complex.exp ((w:ℂ)^2*β (((1/Real.sqrt h:ℝ):ℂ)*(w:ℂ)))*
        A (((1/Real.sqrt h:ℝ):ℂ),((1/Real.sqrt h:ℝ):ℂ)*(w:ℂ))))=
      (Real.sqrt h:ℂ)*∑s∈Finset.range (N+1),
        (∫u:ℝ in (-(R/4))..(R/4),Complex.exp ((h:ℂ)*φ (u:ℂ))*a s (u:ℂ))/(h:ℂ)^s := by
  rw[stationary_inverse_sqrt_rescale β A R h hR.le hh]
  congr 1
  calc (∫u:ℝ in Icc (-(R/4)) (R/4),Complex.exp ((h:ℂ)*((u:ℂ)^2*(β (u:ℂ)-(1/2:ℂ))))*
          A (((1/Real.sqrt h:ℝ):ℂ),(u:ℂ)))=
        ∫u:ℝ in Icc (-(R/4)) (R/4),Complex.exp ((h:ℂ)*φ (u:ℂ))*
          (∑s∈Finset.range (N+1),((1/Real.sqrt h:ℝ):ℂ)^(2*s)*a s (u:ℂ)) := by
          apply setIntegral_congr_fun measurableSet_Icc
          intro u hu
          dsimp only
          rw[←hfac u hu,hA]
       _ = ∑s∈Finset.range (N+1),((1/Real.sqrt h:ℝ):ℂ)^(2*s)*
         (∫u:ℝ in (-(R/4))..(R/4),Complex.exp ((h:ℂ)*φ (u:ℂ))*a s (u:ℂ)):=
          finite_stationary_amplitude_integral φ a N h (R/4) S _ (by positivity) hRS hφ ha
       _ = _ := by
         apply Finset.sum_congr rfl
         intro s hs
         rw[(inverse_sqrt_even_power h hh s).1]
         ring

lemma fixed_gaussian_model_inverse_power_error (f:ℕ→ℂ→ℂ) (C B R r:ℝ)
    (hC:0≤C) (hB:0≤B) (hR:0<R) (hr:0<r) (hrR:r≤R/2)
    (hf:∀s,DifferentiableOn ℂ (f s) (Metric.closedBall 0 R))
    (hbound:∀s z,z∈Metric.closedBall (0:ℂ) R→‖f s z‖≤C*B^s*(s.factorial:ℝ)^2)
    (J K:ℕ) (hKJ:K≤J) :
    ∃D H:ℝ,0<D ∧ 0<H ∧ ∀h:ℝ,H≤h→
      ‖(∑s∈Finset.range (J+1),gaussianAmplitudeIntegral f h r s)-
        (Real.sqrt (2*Real.pi):ℂ)*∑j∈Finset.range (K+1),gaussianModelCoefficient f j/(h:ℂ)^j‖≤D/h^(K+1) := by
  let H:ℝ:=max 1 (max (2*B*((J:ℝ)+1)^2) (8*((K:ℝ)+1)))
  have hH:0<H:=zero_lt_one.trans_le (le_max_left _ _)
  let E:ℝ:=r^2/4
  have hE:0<E:=by dsimp[E];positivity
  let A:ℝ:=(2*C*(Real.sqrt (4*Real.pi)+Real.sqrt (2*Real.pi)))*
    (2*max B (4/R^2))^(K+1)*((K+1).factorial:ℝ)^2
  let T:ℝ:=4*C*Real.sqrt (8*Real.pi)*(2*max 1 R⁻¹)^(2*(K+1))
  let D:ℝ:=A+T*(E⁻¹)^(K+1)*((K+1).factorial:ℝ)+1
  have hA:0≤A:=by dsimp[A];positivity
  have hT:0≤T:=by dsimp[T];positivity
  have hD:0<D:=by dsimp[D];positivity
  refine ⟨D,H,hD,hH,?_⟩
  intro h hHh
  have hh1:1≤h:=(le_max_left _ _).trans hHh
  have hh:0<h:=zero_lt_one.trans_le hh1
  have hbig:2*B*((J:ℝ)+1)^2≤h:=(le_max_left _ _).trans ((le_max_right _ _).trans hHh)
  have hsmall:8*((K:ℝ)+1)≤h:=(le_max_right _ _).trans ((le_max_right _ _).trans hHh)
  have hwin:B*((J:ℝ)+1)^2/h≤1/2 :=(div_le_iff₀ hh).mpr (by linarith)
  have hb:=gaussian_model_remainder_bound f C B R r h hC hB hR hr hrR hh hf hbound J K hKJ hwin hsmall
  rw[gaussian_polynomial_amplitudes_regroup] at hb
  have he:=exp_neg_factorial_bound E h hE hh (K+1)
  have hexp:Real.exp (-(h/4)*r^2)≤(E⁻¹)^(K+1)*((K+1).factorial:ℝ)/h^(K+1) := by
    convert he using 2
    dsimp only[E]
    ring
  apply hb.trans
  change A/h^(K+1)+T*Real.exp (-(h/4)*r^2)≤D/h^(K+1)
  calc _ ≤ A/h^(K+1)+T*((E⁻¹)^(K+1)*((K+1).factorial:ℝ)/h^(K+1)) :=
              add_le_add le_rfl (mul_le_mul_of_nonneg_left hexp hT)
       _ = (D-1)/h^(K+1):=by dsimp[D];ring
       _ ≤ _:=div_le_div_of_nonneg_right (by linarith) (pow_nonneg hh.le _)

lemma finite_complex_coefficients_unique_of_exp_comparison (F G:ℝ→ℂ) (a b:ℕ→ℂ) (N:ℕ)
    (ha:∀K≤N,∃C H:ℝ,0<C ∧ 0<H ∧ ∀h:ℝ,H≤h→
      ‖F h-∑j∈Finset.range (K+1),a j/(h:ℂ)^j‖≤C/h^(K+1))
    (hb:∀K≤N,∃C H:ℝ,0<C ∧ 0<H ∧ ∀h:ℝ,H≤h→
      ‖G h-∑j∈Finset.range (K+1),b j/(h:ℂ)^j‖≤C/h^(K+1))
    (hcomp:∃D ε H:ℝ,0<D ∧ 0<ε ∧ 0<H ∧ ∀h:ℝ,H≤h→
      ‖F h-G h‖≤D*Real.sqrt h*Real.exp (-(ε*h))) :
    ∀j≤N,a j=b j := by
  obtain ⟨D,ε,H0,hD,hε,hH0,hcomp⟩:=hcomp
  have hbF:∀K≤N,∃C H:ℝ,0<C ∧ 0<H ∧ ∀h:ℝ,H≤h→
      ‖F h-∑j∈Finset.range (K+1),b j/(h:ℂ)^j‖≤C/h^(K+1) := by
    intro K hKN
    obtain ⟨C,H,hC,hH,hb⟩:=hb K hKN
    let T:ℝ:=D*((2/ε)*(2/ε)^(K+1)*((K+1).factorial:ℝ))
    have hT:0<T:=by dsimp[T];positivity
    refine ⟨T+C,max 1 (max H H0),by positivity,zero_lt_one.trans_le (le_max_left _ _),?_⟩
    intro h hh
    have hh1:1≤h:=(le_max_left _ _).trans hh
    have hhH:H≤h:=(le_max_left _ _).trans ((le_max_right _ _).trans hh)
    have hh0:H0≤h:=(le_max_right _ _).trans ((le_max_right _ _).trans hh)
    have he:=normalized_outer_exp_factorial_bound (1/2) ε h (by norm_num) hε hh1 (K+1)
    rw[←Real.sqrt_eq_rpow] at he
    have hc:‖F h-G h‖≤T/h^(K+1) := by
      apply (hcomp h hh0).trans
      calc _ = D*(Real.sqrt h*Real.exp (-(ε*h))):=by ring
           _ ≤ D*((2/ε)*(2/ε)^(K+1)*((K+1).factorial:ℝ)/h^(K+1)):=mul_le_mul_of_nonneg_left he hD.le
           _ = _:=by dsimp[T];ring
    calc _ ≤ ‖F h-G h‖+‖G h-∑j∈Finset.range (K+1),b j/(h:ℂ)^j‖:=norm_sub_le_norm_sub_add_norm_sub _ _ _
         _ ≤ T/h^(K+1)+C/h^(K+1):=add_le_add hc (hb h hhH)
         _ = _:=by ring
  have hscale:Tendsto (fun g:ℕ=>(g:ℝ)) atTop atTop:=tendsto_natCast_atTop_atTop
  have hconvert (c:ℕ→ℂ)
      (hc:∀K≤N,∃C H:ℝ,0<C ∧ 0<H ∧ ∀h:ℝ,H≤h→
        ‖F h-∑j∈Finset.range (K+1),c j/(h:ℂ)^j‖≤C/h^(K+1)) :
      ∀K≤N,∃C:ℝ,0<C ∧ ∃g0:ℕ,∀g≥g0,0<(g:ℝ) ∧
        ‖F (g:ℝ)-∑j∈Finset.range (K+1),(((g:ℝ)^j)⁻¹) • c j‖≤C/(g:ℝ)^(K+1) := by
    intro K hKN
    obtain ⟨C,H,hC,hH,hc⟩:=hc K hKN
    obtain ⟨g0,hg0⟩:=eventually_atTop.mp (hscale.eventually (eventually_ge_atTop H))
    refine ⟨C,hC,g0,?_⟩
    intro g hg
    have hHg:H≤(g:ℝ):=hg0 g hg
    refine ⟨hH.trans_le hHg,?_⟩
    have hp:(∑j∈Finset.range (K+1),(((g:ℝ)^j)⁻¹) • c j)=
        ∑j∈Finset.range (K+1),c j/(g:ℂ)^j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only[Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_pow,Complex.ofReal_natCast,div_eq_mul_inv]
      ring
    rw[hp]
    exact hc (g:ℝ) hHg
  exact HigherOrder.finite_vector_inverse_power_expansion_unique (fun g=>F (g:ℝ))
    (fun g=>(g:ℝ)) a b hscale N (hconvert a ha) (hconvert b hbF)

lemma gaussian_model_integral_interval_representation (f:ℕ→ℂ→ℂ) (h r:ℝ) (J:ℕ) (hr:0≤r) :
    (∑s∈Finset.range (J+1),gaussianAmplitudeIntegral f h r s)=
      (Real.sqrt h:ℂ)*∑s∈Finset.range (J+1),
        (∫u:ℝ in (-r)..r,Complex.exp (-(h:ℂ)/2*(u:ℂ)^2)*f s (u:ℂ))/(h:ℂ)^s := by
  rw[Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have he:(∫u:ℝ in Icc (-r) r,Real.exp (-(h/2)*u^2) • f s (u:ℂ))=
      ∫u:ℝ in (-r)..r,Complex.exp (-(h:ℂ)/2*(u:ℂ)^2)*f s (u:ℂ) := by
    rw[integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le (by linarith:-r≤r)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    dsimp only
    rw[Complex.real_smul,Complex.ofReal_exp]
    congr 2
    push_cast
    ring
  dsimp only[gaussianAmplitudeIntegral]
  rw[he]
  ring

lemma gaussianModelCoefficient_zero_extend (f:ℕ→ℂ→ℂ) (N j:ℕ) (hj:j≤N) :
    gaussianModelCoefficient (fun s u=>if s≤N then f s u else 0) j=gaussianModelCoefficient f j := by
  unfold gaussianModelCoefficient
  apply Finset.sum_congr rfl
  intro s hs
  have hsN:s≤N:=(Nat.le_of_lt_succ (Finset.mem_range.mp hs)).trans hj
  have he:(fun u:ℂ=>if s≤N then f s u else 0)=f s:=by funext u;rw[if_pos hsN]
  dsimp only
  rw[he]

def rawScaledGaussianIntegral (β:ℂ→ℂ) (A:ℂ × ℂ→ℂ) (R h:ℝ):ℂ:=
  let τ:ℝ:=1/Real.sqrt h
  ∫w:ℝ in Icc (-(R/(4*τ))) (R/(4*τ)),Real.exp (-(1/2:ℝ)*w^2) •
    (Complex.exp ((w:ℂ)^2*β ((τ:ℂ)*(w:ℂ)))*A ((τ:ℂ),(τ:ℂ)*(w:ℂ)))
end WP.Analysis
