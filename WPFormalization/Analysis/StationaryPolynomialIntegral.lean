import WPFormalization.Analysis.FixedStationaryTaylor
import WPFormalization.Analysis.FiniteWatson
import WPFormalization.Analysis.GaussianFunctionalRealization
/-! Fixed-order genuine stationary Gaussian integrals. A joint analytic finite amplitude supplies common Cauchy circles; retained polynomial tails are controlled on the full real axis. Every displayed estimate is proved with standard axioms. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace WP.Analysis
lemma stationary_joint_cauchy_family (β:ℂ→ℂ) (A:ℂ × ℂ→ℂ)
    (hβ:AnalyticAt ℂ β 0) (hA:AnalyticAt ℂ A (0,0)) (hβ0:β 0=0) :
    ∃R M:ℝ,0<R ∧ 0<M ∧
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
  let R:ℝ:=ρ/2
  have hR:0<R:=half_pos hρ
  have hRρ:R<ρ:=by dsimp[R];linarith
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
  refine ⟨R,M,hR,hM,hstate,?_,?_⟩
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
end WP.Analysis
noncomputable section
open Set MeasureTheory
namespace WP.Analysis
lemma gaussian_imaginary_polynomial_outer_tail (P:Polynomial ℝ) :
    ∃C:ℝ,0<C ∧ ∀r:ℝ,0<r→
      ‖∫w:ℝ in (Icc (-r) r)ᶜ,Real.exp (-(1/2:ℝ)*w^2) •
        (P.map Complex.ofRealHom).eval (Complex.I*(w:ℂ))‖≤C*Real.exp (-(1/4:ℝ)*r^2) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    obtain ⟨C,hC,hP⟩:=hP
    obtain ⟨D,hD,hQ⟩:=hQ
    refine ⟨C+D,by positivity,?_⟩
    intro r hr
    have hPi:IntegrableOn (fun w:ℝ=>Real.exp (-(1/2:ℝ)*w^2) •
      (P.map Complex.ofRealHom).eval (Complex.I*(w:ℂ))) (Icc (-r) r)ᶜ :=
      (imaginary_gaussian_polynomial_integrable P).integrableOn
    have hQi:IntegrableOn (fun w:ℝ=>Real.exp (-(1/2:ℝ)*w^2) •
      (Q.map Complex.ofRealHom).eval (Complex.I*(w:ℂ))) (Icc (-r) r)ᶜ :=
      (imaginary_gaussian_polynomial_integrable Q).integrableOn
    simp only[Polynomial.map_add,Polynomial.eval_add,smul_add]
    rw[integral_add hPi hQi]
    exact (norm_add_le _ _).trans ((add_le_add (hP r hr) (hQ r hr)).trans_eq (by ring))
  | monomial n a =>
    let g:ℝ→ℝ:=fun w=>|w|^n*Real.exp (-(1/4:ℝ)*w^2)
    have hg:Integrable g := by
      simpa only[Real.norm_eq_abs,abs_mul,abs_pow,abs_of_pos (Real.exp_pos _)] using
        (gaussian_monomial_integrable (1/4) (by norm_num) n).norm
    have hgn(w:ℝ):0≤g w:=by dsimp[g];positivity
    let C:ℝ:=|a| *(∫w:ℝ,g w)+1
    have hC:0<C:=by dsimp[C];have h0:0≤∫w:ℝ,g w:=MeasureTheory.integral_nonneg (fun w=>hgn w);positivity
    refine ⟨C,hC,?_⟩
    intro r hr
    have hdom:Integrable (fun w:ℝ=>(|a| *Real.exp (-(1/4:ℝ)*r^2))*g w) :=hg.const_mul _
    have hp(w:ℝ)(hw:w∈(Icc (-r) r)ᶜ):
        ‖Real.exp (-(1/2:ℝ)*w^2) •
        ((Polynomial.monomial n a).map Complex.ofRealHom).eval (Complex.I*(w:ℂ))‖≤
          (|a| *Real.exp (-(1/4:ℝ)*r^2))*g w := by
      have hab:r≤|w| := by
        by_contra hn
        have ht:=abs_lt.mp (lt_of_not_ge hn)
        exact hw ⟨ht.1.le,ht.2.le⟩
      have hrs:r^2≤w^2:=by nlinarith[sq_abs w]
      have hexp:Real.exp (-(1/2:ℝ)*w^2)≤
          Real.exp (-(1/4:ℝ)*r^2)*Real.exp (-(1/4:ℝ)*w^2) := by
        rw[←Real.exp_add]
        exact Real.exp_le_exp.mpr (by nlinarith)
      simp only[Polynomial.map_monomial,Polynomial.eval_monomial,Complex.ofRealHom_eq_coe,
        norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),norm_mul,norm_pow,
        Complex.norm_real,Complex.norm_I,one_mul,mul_pow,one_pow]
      dsimp only[g]
      calc _ ≤ (Real.exp (-(1/4:ℝ)*r^2)*Real.exp (-(1/4:ℝ)*w^2))*(|a| *|w|^n) :=
                mul_le_mul_of_nonneg_right hexp (by positivity)
           _ = _ := by ring
    have hb:=norm_integral_le_of_norm_le hdom.integrableOn
      (ae_restrict_of_forall_mem measurableSet_Icc.compl hp)
    have hs:(∫w:ℝ in (Icc (-r) r)ᶜ,(|a| *Real.exp (-(1/4:ℝ)*r^2))*g w)≤
        ∫w:ℝ,(|a| *Real.exp (-(1/4:ℝ)*r^2))*g w :=
      setIntegral_le_integral hdom (Filter.Eventually.of_forall (fun w=>by positivity))
    apply (hb.trans hs).trans
    rw[integral_const_mul]
    dsimp only[C]
    nlinarith[Real.exp_pos (-(1/4:ℝ)*r^2)]
end WP.Analysis

noncomputable section
open Set MeasureTheory
namespace WP.Analysis
lemma stationary_polynomial_integral_expansion (F:ℝ→ℂ→ℂ) (P:ℕ→Polynomial ℝ)
    (M R:ℝ) (hM:0≤M) (hR:0<R)
    (hF:∀w,DifferentiableOn ℂ (F w) (Metric.closedBall 0 (R/(1+|w|))))
    (hbound:∀w z,z∈Metric.sphere (0:ℂ) (R/(1+|w|))→‖F w z‖≤M*Real.exp (w^2/4))
    (N:ℕ)
    (hcoeff:∀ n < N,∀w:ℝ,WP.coeff (F w) n=Polynomial.eval₂ Complex.ofRealHom (Complex.I*(w:ℂ)) (P n)) :
    ∃C:ℝ,0<C ∧ ∀τ:ℝ,0<τ→τ≤ min 1 (R/4)→
      IntegrableOn (fun w:ℝ=>Real.exp (-(1/2:ℝ)*w^2) • F w (τ:ℂ))
        (Icc (-(R/(4*τ))) (R/(4*τ)))→
      ‖(∫w:ℝ in Icc (-(R/(4*τ))) (R/(4*τ)),Real.exp (-(1/2:ℝ)*w^2) • F w (τ:ℂ))-
        ∑ n ∈ Finset.range N,(τ:ℂ)^n*(∫w:ℝ,Real.exp (-(1/2:ℝ)*w^2) •
          (Polynomial.map Complex.ofRealHom (P n)).eval (Complex.I*(w:ℂ)))‖≤C*τ^N := by
  choose D hD htail using fun n:ℕ=>gaussian_imaginary_polynomial_outer_tail (P n)
  let E:ℝ:=∑ n ∈ Finset.range N,D n
  have hE:0≤E:=Finset.sum_nonneg (fun n hn=>(hD n).le)
  let a:ℝ:=R^2/64
  have ha:0<a:=by dsimp[a];positivity
  let C:ℝ:=2*M/R^N*(∫w:ℝ,(1+|w|)^N*Real.exp (-(1/4:ℝ)*w^2))+
    E*(a⁻¹)^N*(N.factorial:ℝ)+1
  have hCN:0≤2*M/R^N*(∫w:ℝ,(1+|w|)^N*Real.exp (-(1/4:ℝ)*w^2)) := by
    apply mul_nonneg (by positivity)
    exact MeasureTheory.integral_nonneg (fun w=>by positivity)
  have hC:0<C:=by dsimp[C];positivity
  refine ⟨C,hC,?_⟩
  intro τ hτ hτsmall hFi
  have hτ1:τ≤1:=hτsmall.trans (min_le_left _ _)
  have hτR:τ≤R/4:=hτsmall.trans (min_le_right _ _)
  let r:ℝ:=R/(4*τ)
  have hr:0<r:=by dsimp[r];positivity
  let Q:ℝ→ℂ:=fun w=>∑ n ∈ Finset.range N,WP.coeff (F w) n*(τ:ℂ)^n
  let G:ℝ→ℂ:=fun w=>Real.exp (-(1/2:ℝ)*w^2) • Q w
  have hGn(n:ℕ)(hn:n∈Finset.range N):
      Integrable (fun w:ℝ=>(τ:ℂ)^n*(Real.exp (-(1/2:ℝ)*w^2) •
        (Polynomial.map Complex.ofRealHom (P n)).eval (Complex.I*(w:ℂ)))) :=
    (imaginary_gaussian_polynomial_integrable (P n)).const_mul _
  have hGe:G=(fun w:ℝ=>∑ n ∈ Finset.range N,(τ:ℂ)^n*(Real.exp (-(1/2:ℝ)*w^2) •
      (Polynomial.map Complex.ofRealHom (P n)).eval (Complex.I*(w:ℂ)))) := by
    funext w
    dsimp only[G,Q]
    rw[Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw[hcoeff n (Finset.mem_range.mp hn) w]
    simp only[←Polynomial.eval₂_eq_eval_map,Complex.real_smul]
    ring
  have hGi:Integrable G:=by rw[hGe];exact integrable_finsetSum _ hGn
  have hGint:(∫w:ℝ,G w)=∑ n ∈ Finset.range N,(τ:ℂ)^n*(∫w:ℝ,Real.exp (-(1/2:ℝ)*w^2) •
      (Polynomial.map Complex.ofRealHom (P n)).eval (Complex.I*(w:ℂ))) := by
    rw[hGe,integral_finsetSum]
    · simp only[integral_const_mul]
    · exact hGn
  have hGo:(∫w:ℝ in (Icc (-r) r)ᶜ,G w)=∑ n ∈ Finset.range N,(τ:ℂ)^n*(∫w:ℝ in (Icc (-r) r)ᶜ,
      Real.exp (-(1/2:ℝ)*w^2) •
      (Polynomial.map Complex.ofRealHom (P n)).eval (Complex.I*(w:ℂ))) := by
    rw[hGe,integral_finsetSum]
    · simp only[integral_const_mul]
    · intro n hn;exact (hGn n hn).integrableOn
  have hGtail:‖∫w:ℝ in (Icc (-r) r)ᶜ,G w‖≤E*Real.exp (-(1/4:ℝ)*r^2) := by
    rw[hGo]
    calc _ ≤ ∑ n ∈ Finset.range N,‖(τ:ℂ)^n*(∫w:ℝ in (Icc (-r) r)ᶜ,
        Real.exp (-(1/2:ℝ)*w^2) •
        (Polynomial.map Complex.ofRealHom (P n)).eval (Complex.I*(w:ℂ)))‖:=norm_sum_le _ _
         _ ≤ ∑ n ∈ Finset.range N,D n*Real.exp (-(1/4:ℝ)*r^2) := by
           apply Finset.sum_le_sum
           intro n hn
           rw[norm_mul,norm_pow,Complex.norm_of_nonneg hτ.le]
           exact (mul_le_mul (pow_le_one₀ hτ.le hτ1) (htail n r hr) (norm_nonneg _) zero_le_one).trans_eq (by ring)
         _ = _ := by rw[←Finset.sum_mul]
  have ht:=stationary_fixed_taylor_integral_bound F M R τ hM hR hτ hτR hF hbound N
  have hsub:(∫w:ℝ in Icc (-r) r,Real.exp (-(1/2:ℝ)*w^2) • (F w (τ:ℂ)-Q w))=
      (∫w:ℝ in Icc (-r) r,Real.exp (-(1/2:ℝ)*w^2) • F w (τ:ℂ))-
        ∫w:ℝ in Icc (-r) r,G w := by
    simp_rw[smul_sub]
    exact integral_sub hFi hGi.integrableOn
  have hsplit:∫w:ℝ,G w=(∫w:ℝ in Icc (-r) r,G w)+(∫w:ℝ in (Icc (-r) r)ᶜ,G w):=
    (integral_add_compl measurableSet_Icc hGi).symm
  have hid:(∫w:ℝ in Icc (-r) r,Real.exp (-(1/2:ℝ)*w^2) • F w (τ:ℂ))-(∫w:ℝ,G w)=
      (∫w:ℝ in Icc (-r) r,Real.exp (-(1/2:ℝ)*w^2) • (F w (τ:ℂ)-Q w))-
        (∫w:ℝ in (Icc (-r) r)ᶜ,G w) := by rw[hsub,hsplit];ring
  have hexp:Real.exp (-(1/4:ℝ)*r^2)≤(a⁻¹)^N*(N.factorial:ℝ)*τ^N := by
    have hab:(a/τ)≤(1/4:ℝ)*r^2 := by
      dsimp only[a,r]
      apply (div_le_iff₀ hτ).mpr
      field_simp
      nlinarith[sq_nonneg R]
    have he:=exp_neg_factorial_bound a (1/τ) ha (by positivity) N
    calc _ ≤ Real.exp (-(a*(1/τ))) := Real.exp_le_exp.mpr (by simpa only[div_eq_mul_inv,one_mul,neg_mul] using neg_le_neg hab)
         _ ≤ _ := he.trans_eq (by rw[div_pow];field_simp;simp)
  rw[←hGint]
  change ‖(∫w:ℝ in Icc (-r) r,Real.exp (-(1/2:ℝ)*w^2) • F w (τ:ℂ))-(∫w:ℝ,G w)‖≤_
  rw[hid]
  calc _ ≤ ‖∫w:ℝ in Icc (-r) r,Real.exp (-(1/2:ℝ)*w^2) • (F w (τ:ℂ)-Q w)‖+
      ‖∫w:ℝ in (Icc (-r) r)ᶜ,G w‖:=norm_sub_le _ _
       _ ≤ 2*M*(τ/R)^N*(∫w:ℝ,(1+|w|)^N*Real.exp (-(1/4:ℝ)*w^2))+
          E*((a⁻¹)^N*(N.factorial:ℝ)*τ^N) :=
          add_le_add ht (hGtail.trans (mul_le_mul_of_nonneg_left hexp hE))
       _ ≤ C*τ^N := by
         calc _ = (C-1)*τ^N := by dsimp[C];rw[div_pow];ring
              _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hτ.le N)

lemma stationary_joint_local_integrable (β:ℂ→ℂ) (A:ℂ × ℂ→ℂ) (R τ:ℝ)
    (hR:0<R) (hτ:0<τ) (hτR:τ≤R/4)
    (hstate:∀u v:ℂ,‖u‖≤R→‖v‖≤R→AnalyticAt ℂ β v ∧ AnalyticAt ℂ A (u,v)) :
    IntegrableOn (fun w:ℝ=>Real.exp (-(1/2:ℝ)*w^2) •
      (Complex.exp ((w:ℂ)^2*β ((τ:ℂ)*(w:ℂ)))*A ((τ:ℂ),(τ:ℂ)*(w:ℂ))))
      (Icc (-(R/(4*τ))) (R/(4*τ))) := by
  apply ContinuousOn.integrableOn_Icc
  intro w hw
  have hwabs:|w|≤R/(4*τ):=abs_le.mpr ⟨by linarith[hw.1],hw.2⟩
  have hτb:‖(τ:ℂ)‖≤R:=by rw[Complex.norm_of_nonneg hτ.le];linarith
  have hwb:‖(τ:ℂ)*(w:ℂ)‖≤R := by
    rw[norm_mul,Complex.norm_of_nonneg hτ.le,Complex.norm_real,Real.norm_eq_abs]
    have he:|w| *(4*τ)≤R:=(le_div_iff₀ (by positivity)).mp hwabs
    linarith
  have hp:=hstate (τ:ℂ) ((τ:ℂ)*(w:ℂ)) hτb hwb
  have hβc:ContinuousAt (fun w:ℝ=>β ((τ:ℂ)*(w:ℂ))) w :=
    ContinuousAt.comp (f:=fun w:ℝ=>(τ:ℂ)*(w:ℂ)) (g:=β) (x:=w)
      hp.1.continuousAt ((continuous_const.mul Complex.continuous_ofReal).continuousAt)
  have hAc:ContinuousAt (fun w:ℝ=>A ((τ:ℂ),(τ:ℂ)*(w:ℂ))) w :=
    ContinuousAt.comp (f:=fun w:ℝ=>((τ:ℂ),(τ:ℂ)*(w:ℂ))) (g:=A) (x:=w)
      hp.2.continuousAt ((continuous_const.prodMk (continuous_const.mul Complex.continuous_ofReal)).continuousAt)
  have hEc:ContinuousAt (fun w:ℝ=>Complex.exp ((w:ℂ)^2*β ((τ:ℂ)*(w:ℂ)))) w :=
    Complex.continuous_exp.continuousAt.comp ((Complex.continuous_ofReal.continuousAt.pow 2).mul hβc)
  have hGc:ContinuousAt (fun w:ℝ=>Real.exp (-(1/2:ℝ)*w^2)) w:=by fun_prop
  have hc:ContinuousAt (fun w:ℝ=>Real.exp (-(1/2:ℝ)*w^2) •
    (Complex.exp ((w:ℂ)^2*β ((τ:ℂ)*(w:ℂ)))*A ((τ:ℂ),(τ:ℂ)*(w:ℂ)))) w :=
    hGc.smul (hEc.mul hAc)
  exact hc.continuousWithinAt
end WP.Analysis
