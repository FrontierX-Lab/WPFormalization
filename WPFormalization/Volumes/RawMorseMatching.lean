import WPFormalization.Analysis.StationaryMatchingSupport
import WPFormalization.Volumes.RawExtractionIntegral
import WPFormalization.Volumes.ExtractionMorseComparison
/-! The original CG3 numerator coefficients equal the actual normalized Morse Gaussian coefficients. The proof fixes the genuine finite amplitude model, matches both real integrals and uses finite-order uniqueness. The actual germs are chosen once for every order; no replacement coefficient family is introduced. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace WP.Analysis
lemma raw_gaussian_integral_of_physical_germs (P:PsiTheory) (p:ℕ) (x:ℝ) (N:ℕ)
    (S B β:ℂ→ℂ) (Γ:ℕ→ℂ→ℂ)
    (hS:AnalyticAt ℂ S (x:ℂ)) (hB:AnalyticAt ℂ B (x:ℂ))
    (hSr:(fun t:ℝ=>S (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(extractionS t:ℂ)))
    (hBr:(fun t:ℝ=>B (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(Real.log (extractionB p t):ℂ)))
    (hvar:0<WP.euler WP.Psi x) (hβ:AnalyticAt ℂ β 0) (hβ0:β 0=0)
    (hfac:centeredExponentialSlice S (x:ℂ) (Complex.I/(Real.sqrt (WP.euler WP.Psi x):ℂ))=ᶠ[𝓝 0]
      (fun u:ℂ=>u^2*(β u-(1/2:ℂ))))
    (hΓ:∀s,AnalyticAt ℂ (Γ s) (x:ℂ) ∧
      (fun t:ℝ=>Γ s (t:ℂ))=ᶠ[𝓝 x]
        (fun t:ℝ=>(HigherOrder.markedCoefficient P p s (inverseY t):ℂ))) (R0:ℝ) (hR0:0<R0) :
    ∃A:ℂ × ℂ→ℂ,∃R:ℝ,0<R ∧ R≤R0 ∧
      (∀τ u:ℂ,A (τ,u)=Complex.exp (B ((x:ℂ)*Complex.exp ((Complex.I/(Real.sqrt (WP.euler WP.Psi x):ℂ))*u))-B (x:ℂ))*
        ∑s∈Finset.range (N+1),τ^(2*s)*Γ s ((x:ℂ)*Complex.exp ((Complex.I/(Real.sqrt (WP.euler WP.Psi x):ℂ))*u))) ∧
      (∀n:ℕ,n/2≤N→∀w:ℝ,WP.coeff
        (fun τ:ℂ=>Complex.exp ((w:ℂ)^2*β (τ*(w:ℂ)))*A (τ,τ*(w:ℂ))) n=
        Polynomial.eval₂ Complex.ofRealHom (Complex.I*(w:ℂ)) (extractionNumeratorPolynomial P p x n)) ∧
      (∀K≤N,∃C:ℝ,0<C ∧ ∀τ:ℝ,0<τ→τ≤ min 1 (R/4)→
        ‖(∫w:ℝ in Icc (-(R/(4*τ))) (R/(4*τ)),Real.exp (-(1/2:ℝ)*w^2) •
            (Complex.exp ((w:ℂ)^2*β ((τ:ℂ)*(w:ℂ)))*A ((τ:ℂ),(τ:ℂ)*(w:ℂ))))-
          (Real.sqrt (2*Real.pi):ℂ)*∑n∈Finset.range (2*(K+1)),(τ:ℂ)^n*
            ((PowerSeries.coeff n (HigherOrder.extractionNumerator P p x):ℝ):ℂ)‖≤C*τ^(2*(K+1))) := by
  let c:ℂ:=Complex.I/(Real.sqrt (WP.euler WP.Psi x):ℂ)
  let A:ℂ × ℂ→ℂ:=fun v=>Complex.exp (B ((x:ℂ)*Complex.exp (c*v.2))-B (x:ℂ))*
    ∑s∈Finset.range (N+1),v.1^(2*s)*Γ s ((x:ℂ)*Complex.exp (c*v.2))
  have harg:AnalyticAt ℂ (fun v:ℂ × ℂ=>(x:ℂ)*Complex.exp (c*v.2)) (0,0):=
    analyticAt_const.mul ((analyticAt_const.mul analyticAt_snd).cexp)
  have harg0:((x:ℂ)*Complex.exp (c*((0,0):ℂ × ℂ).2))=(x:ℂ):=by simp
  have hBj:AnalyticAt ℂ (fun v:ℂ × ℂ=>B ((x:ℂ)*Complex.exp (c*v.2))) (0,0):=
    hB.comp_of_eq harg harg0
  have hAj:AnalyticAt ℂ A (0,0) := by
    apply ((hBj.sub analyticAt_const).cexp).mul
    apply Finset.analyticAt_fun_sum
    intro s hs
    exact (analyticAt_fst.pow _).mul ((hΓ s).1.comp_of_eq harg harg0)
  obtain ⟨R,M,hR,hRR0,hM,hstate,hF,hbound⟩:=stationary_joint_cauchy_family_below β A R0 hR0 hβ hAj hβ0
  let F:ℝ→ℂ→ℂ:=fun w τ=>Complex.exp ((w:ℂ)^2*β (τ*(w:ℂ)))*A (τ,τ*(w:ℂ))
  have hcoeff(n:ℕ)(hn:n/2≤N)(w:ℝ):WP.coeff (F w) n=
      Polynomial.eval₂ Complex.ofRealHom (Complex.I*(w:ℂ)) (extractionNumeratorPolynomial P p x n) := by
    have he:(F w)=(fun τ:ℂ=>Complex.exp ((w:ℂ)^2*β (τ*(w:ℂ))+
        (B ((x:ℂ)*Complex.exp ((Complex.I*(w:ℂ)/(Real.sqrt (WP.euler WP.Psi x):ℂ))*τ))-B (x:ℂ)))*
      (∑s∈Finset.range (N+1),τ^(2*s)*Γ s
        ((x:ℂ)*Complex.exp ((Complex.I*(w:ℂ)/(Real.sqrt (WP.euler WP.Psi x):ℂ))*τ)))) := by
      funext τ
      dsimp only[F,A,c]
      rw[show (Complex.I/(Real.sqrt (WP.euler WP.Psi x):ℂ))*(τ*(w:ℂ))=
        (Complex.I*(w:ℂ)/(Real.sqrt (WP.euler WP.Psi x):ℂ))*τ by ring,Complex.exp_add]
      ring
    rw[he]
    exact extractionNumeratorPolynomial_actual_tilt_jets P p x (w:ℂ) S B β Γ hS hB hSr hBr hvar hβ hβ0 hfac hΓ n N hn
  refine ⟨A,R,hR,hRR0,(fun τ u=>rfl),hcoeff,?_⟩
  intro K hKN
  obtain ⟨C,hC,herror⟩:=stationary_polynomial_integral_expansion F
    (extractionNumeratorPolynomial P p x) M R hM.le hR hF hbound (2*(K+1))
    (fun n hn w=>hcoeff n (by omega) w)
  refine ⟨C,hC,?_⟩
  intro τ hτ hτsmall
  have hi:=stationary_joint_local_integrable β A R τ hR hτ (hτsmall.trans (min_le_right _ _))
    (fun u v hu hv=>⟨(hstate u v hu hv).1,(hstate u v hu hv).2.1⟩)
  have he:=herror τ hτ hτsmall hi
  have hpoly:(∑n∈Finset.range (2*(K+1)),(τ:ℂ)^n*(∫w:ℝ,Real.exp (-(1/2:ℝ)*w^2) •
      (Polynomial.map Complex.ofRealHom (extractionNumeratorPolynomial P p x n)).eval (Complex.I*(w:ℂ))))=
      (Real.sqrt (2*Real.pi):ℂ)*∑n∈Finset.range (2*(K+1)),(τ:ℂ)^n*
        ((PowerSeries.coeff n (HigherOrder.extractionNumerator P p x):ℝ):ℂ) := by
    rw[Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw[extractionNumerator_gaussian_integral]
    ring
  rw[hpoly] at he
  exact he

lemma raw_gaussian_inverse_power_error_of_tau (P:PsiTheory) (p:ℕ) (hp:1≤p) (x:ℝ)
    (hx:x∈Ioo (0:ℝ) xCritical) (β:ℂ→ℂ) (A:ℂ × ℂ→ℂ) (R:ℝ) (hR:0<R) (K:ℕ)
    (herror:∃C:ℝ,0<C ∧ ∀τ:ℝ,0<τ→τ≤ min 1 (R/4)→
      ‖(∫w:ℝ in Icc (-(R/(4*τ))) (R/(4*τ)),Real.exp (-(1/2:ℝ)*w^2) •
        (Complex.exp ((w:ℂ)^2*β ((τ:ℂ)*(w:ℂ)))*A ((τ:ℂ),(τ:ℂ)*(w:ℂ))))-
        (Real.sqrt (2*Real.pi):ℂ)*∑n∈Finset.range (2*(K+1)),(τ:ℂ)^n*
          ((PowerSeries.coeff n (HigherOrder.extractionNumerator P p x):ℝ):ℂ)‖≤C*τ^(2*(K+1))) :
    ∃C H:ℝ,0<C ∧ 0<H ∧ ∀h:ℝ,H≤h→
      ‖rawScaledGaussianIntegral β A R h-(Real.sqrt (2*Real.pi):ℂ)*
        ∑j∈Finset.range (K+1),((PowerSeries.coeff (2*j) (HigherOrder.extractionNumerator P p x):ℝ):ℂ)/(h:ℂ)^j‖≤C/h^(K+1) := by
  obtain ⟨C,hC,herr⟩:=herror
  obtain ⟨H,hH,hsmall⟩:=inverse_sqrt_stationary_threshold R hR
  refine ⟨C,H,hC,hH,?_⟩
  intro h hHh
  have hh:0<h:=hH.trans_le hHh
  obtain ⟨hτ,hτsmall⟩:=hsmall h hHh
  have he:=herr (1/Real.sqrt h) hτ hτsmall
  rw[extractionNumerator_truncation_even P p hp x hx] at he
  have hpoly:(∑j∈Finset.range (K+1),((PowerSeries.coeff (2*j) (HigherOrder.extractionNumerator P p x):ℝ):ℂ)*
      ((((1/Real.sqrt h:ℝ):ℂ))^2)^j)=
      ∑j∈Finset.range (K+1),((PowerSeries.coeff (2*j) (HigherOrder.extractionNumerator P p x):ℝ):ℂ)/(h:ℂ)^j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw[←pow_mul,(inverse_sqrt_even_power h hh j).1]
    ring
  rw[hpoly,(inverse_sqrt_even_power h hh (K+1)).2] at he
  exact he.trans_eq (by ring)

lemma raw_numerator_morse_coefficients_of_physical_germs (P:PsiTheory) (p:ℕ) (hp:1≤p)
    (x:ℝ) (hx:x∈Ioo (0:ℝ) xCritical) (S B β:ℂ→ℂ) (Γ:ℕ→ℂ→ℂ) (U W:ℂ→ℂ)
    (hS:AnalyticAt ℂ S (x:ℂ)) (hB:AnalyticAt ℂ B (x:ℂ))
    (hSr:(fun t:ℝ=>S (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(extractionS t:ℂ)))
    (hBr:(fun t:ℝ=>B (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(Real.log (extractionB p t):ℂ)))
    (hvar:0<WP.euler WP.Psi x) (hβ:AnalyticAt ℂ β 0) (hβ0:β 0=0)
    (hfac:extractionStationaryPhase S x=ᶠ[𝓝 0] (fun u:ℂ=>u^2*(β u-(1/2:ℂ))))
    (hΓ:∀s,AnalyticAt ℂ (Γ s) (x:ℂ) ∧
      (fun t:ℝ=>Γ s (t:ℂ))=ᶠ[𝓝 x]
        (fun t:ℝ=>(HigherOrder.markedCoefficient P p s (inverseY t):ℂ)))
    (hU:AnalyticAt ℂ U 0) (hW:AnalyticAt ℂ W 0) (hU0:U 0=0)
    (hconj:∀ᶠz:ℂ in 𝓝 0,U (W z)=z ∧ extractionStationaryPhase S x (U z)=-z^2/2)
    (ρ C:ℝ) (hρ:0<ρ) (hC:0<C) (hclose:∀z:ℂ,‖z‖<ρ→‖W z-z‖≤C*‖z‖^2)
    (N:ℕ) : ∀j≤N,
      ((PowerSeries.coeff (2*j) (HigherOrder.extractionNumerator P p x):ℝ):ℂ)=
        gaussianModelCoefficient (extractionMorseGermAmplitude B Γ x U) j := by
  let φ:ℂ→ℂ:=extractionStationaryPhase S x
  let a:ℕ→ℂ→ℂ:=extractionPremorseGermAmplitude B Γ x
  let b:ℕ→ℂ→ℂ:=extractionMorseGermAmplitude B Γ x U
  let c:ℂ:=Complex.I/(Real.sqrt (WP.euler WP.Psi x):ℂ)
  have harg:AnalyticAt ℂ (fun u:ℂ=>(x:ℂ)*Complex.exp (c*u)) 0:=by fun_prop
  have harg0:(x:ℂ)*Complex.exp (c*0)=(x:ℂ):=by simp
  have hφ:AnalyticAt ℂ φ 0:=(((hS.comp_of_eq harg harg0).sub analyticAt_const).sub (by fun_prop))
  have ha(s:ℕ):AnalyticAt ℂ (a s) 0:=
    ((hB.comp_of_eq harg harg0).sub analyticAt_const).cexp.mul ((hΓ s).1.comp_of_eq harg harg0)
  obtain ⟨r0,Rm,Sm,M,hr0,hr0Rm,hr0Sm,hM,hφd,hUd,hmap,hphase,hamp,hend⟩:=
    fixed_morse_finite_amplitude_cut_data_all_radii φ U W a N hφ hU hW hU0 (fun s hs=>ha s)
      hconj ρ C hρ hC hclose
  have hRm:0<Rm:=by linarith
  obtain ⟨rc,hrc,hcompare⟩:=fixed_morse_finite_amplitude_integral_comparison φ U W a N hφ hU hW hU0
    (fun s hs=>ha s) hconj ρ C hρ hC hclose
  obtain ⟨Rf,hRf,hfactor⟩:=Metric.eventually_nhds_iff.mp hfac
  let cap:ℝ:=min (4*r0) (min (4*rc) (min Rm Rf))
  have hcap:0<cap:=lt_min (by positivity) (lt_min (by positivity) (lt_min hRm hRf))
  obtain ⟨A,R,hR,hRcap,hA,hcoeff,hraw⟩:=raw_gaussian_integral_of_physical_germs P p x N S B β Γ
    hS hB hSr hBr hvar hβ hβ0 hfac hΓ cap hcap
  let r:ℝ:=R/4
  have hr:0<r:=by dsimp[r];positivity
  have hr0le:r≤r0:=by have he:=hRcap.trans (min_le_left _ _);dsimp[r];linarith
  have hrcle:r≤rc:=by have he:=hRcap.trans ((min_le_right _ _).trans (min_le_left _ _));dsimp[r];linarith
  have hRleRm:R≤Rm:=hRcap.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hRleRf:R≤Rf:=hRcap.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hrSm:r<Sm:=hr0le.trans_lt hr0Sm
  have hrRm:r<Rm:=by dsimp[r];linarith
  have hfacr(u:ℝ)(hu:u∈Icc (-r) r):φ (u:ℂ)=(u:ℂ)^2*(β (u:ℂ)-(1/2:ℂ)) := by
    apply hfactor
    rw[dist_zero_right,Complex.norm_real,Real.norm_eq_abs]
    have he:|u|≤r:=abs_le.mpr ⟨by linarith[hu.1],hu.2⟩
    dsimp[r] at he
    linarith
  have hAsum(τ u:ℂ):A (τ,u)=∑s∈Finset.range (N+1),τ^(2*s)*a s u := by
    rw[hA]
    dsimp only[a,extractionPremorseGermAmplitude]
    rw[Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  let f:ℕ→ℂ→ℂ:=fun s u=>if s≤N then b s u else 0
  let Rp:ℝ:=Rm/2
  have hRp:0<Rp:=half_pos hRm
  have hRpRm:Rp<Rm:=by dsimp[Rp];linarith
  have hrRp:r≤Rp/2:=by dsimp[r,Rp];linarith
  have hfd(s:ℕ):DifferentiableOn ℂ (f s) (Metric.closedBall 0 Rp) := by
    by_cases hs:s≤N
    · intro z hz
      have hzR:z∈Metric.ball (0:ℂ) Rm := by
        rw[Metric.mem_ball,dist_zero_right]
        exact (show ‖z‖≤Rp from by simpa only[Metric.mem_closedBall,dist_zero_right] using hz).trans_lt hRpRm
      have hUz:=hUd.analyticAt (Metric.isOpen_ball.mem_nhds hzR)
      have haz:AnalyticAt ℂ (a s) (U z):=(hamp s hs).1.analyticAt (Metric.isOpen_ball.mem_nhds (hmap hzR))
      have hbd:AnalyticAt ℂ (b s) z := (haz.comp hUz).mul hUz.deriv
      simpa only[f,ite_eq_left hs] using hbd.differentiableAt.differentiableWithinAt
    · simpa only[f,ite_eq_right hs] using (differentiableOn_const (c:=(0:ℂ)))
  have hfbound(s:ℕ)(z:ℂ)(hz:z∈Metric.closedBall (0:ℂ) Rp):‖f s z‖≤M*1^s*(s.factorial:ℝ)^2 := by
    by_cases hs:s≤N
    · have hzR:z∈Metric.ball (0:ℂ) Rm := by
        rw[Metric.mem_ball,dist_zero_right]
        exact (show ‖z‖≤Rp from by simpa only[Metric.mem_closedBall,dist_zero_right] using hz).trans_lt hRpRm
      have hb:‖b s z‖≤M:=(hamp s hs).2 z hzR
      have hfac1:1≤(s.factorial:ℝ):=by exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos s))
      simp only[f,ite_eq_left hs,one_pow,mul_one]
      exact hb.trans (by
        have h2:1≤(s.factorial:ℝ)^2:=by nlinarith
        simpa only[mul_one] using mul_le_mul_of_nonneg_left h2 hM.le)
    · simp only[f,ite_eq_right hs,norm_zero,one_pow,mul_one]
      positivity
  let F:ℝ→ℂ:=rawScaledGaussianIntegral β A R
  let G:ℝ→ℂ:=fun h=>∑s∈Finset.range (N+1),gaussianAmplitudeIntegral f h r s
  have hFphysical(h:ℝ)(hh:0<h):F h=(Real.sqrt h:ℂ)*
      ∑s∈Finset.range (N+1),(∫u:ℝ in (-r)..r,Complex.exp ((h:ℂ)*φ (u:ℂ))*a s (u:ℂ))/(h:ℂ)^s := by
    exact stationary_finite_model_rescaling φ β A a N R h Sm hR hh hrSm hφd
      (fun s hs=>(hamp s hs).1) hAsum hfacr
  have hGphysical(h:ℝ):G h=(Real.sqrt h:ℂ)*
      ∑s∈Finset.range (N+1),(∫u:ℝ in (-r)..r,Complex.exp (-(h:ℂ)/2*(u:ℂ)^2)*b s (u:ℂ))/(h:ℂ)^s := by
    change (∑s∈Finset.range (N+1),gaussianAmplitudeIntegral f h r s)=_
    rw[gaussian_model_integral_interval_representation f h r N hr.le]
    congr 1
    apply Finset.sum_congr rfl
    intro s hs
    have hsN:s≤N:=Nat.le_of_lt_succ (Finset.mem_range.mp hs)
    simp only[f,ite_eq_left hsN]
  obtain ⟨D,ε,hD,hε,hcomparison⟩:=hcompare r ⟨hr,hrcle⟩
  have hcomp:∃D ε H:ℝ,0<D ∧ 0<ε ∧ 0<H ∧ ∀h:ℝ,H≤h→
      ‖F h-G h‖≤D*Real.sqrt h*Real.exp (-(ε*h)) := by
    refine ⟨D,ε,1,hD,hε,by norm_num,?_⟩
    intro h hh1
    have hh:0<h:=zero_lt_one.trans_le hh1
    rw[hFphysical h hh,hGphysical h,←mul_sub,norm_mul,Complex.norm_of_nonneg (Real.sqrt_nonneg h)]
    exact (mul_le_mul_of_nonneg_left (hcomparison h hh1) (Real.sqrt_nonneg h)).trans_eq (by ring)
  let v:ℝ:=Real.sqrt (2*Real.pi)
  let ca:ℕ→ℂ:=fun j=>(v:ℂ)*((PowerSeries.coeff (2*j) (HigherOrder.extractionNumerator P p x):ℝ):ℂ)
  let cb:ℕ→ℂ:=fun j=>(v:ℂ)*gaussianModelCoefficient f j
  have hpre:∀K≤N,∃C H:ℝ,0<C ∧ 0<H ∧ ∀h:ℝ,H≤h→
      ‖F h-∑j∈Finset.range (K+1),ca j/(h:ℂ)^j‖≤C/h^(K+1) := by
    intro K hKN
    obtain ⟨C,H,hC,hH,herror⟩:=raw_gaussian_inverse_power_error_of_tau P p hp x hx β A R hR K (hraw K hKN)
    refine ⟨C,H,hC,hH,?_⟩
    intro h hHh
    have he:=herror h hHh
    have hp:(v:ℂ)*(∑j∈Finset.range (K+1),((PowerSeries.coeff (2*j) (HigherOrder.extractionNumerator P p x):ℝ):ℂ)/(h:ℂ)^j)=
        ∑j∈Finset.range (K+1),ca j/(h:ℂ)^j := by
      rw[Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      dsimp[ca]
      ring
    rwa[hp] at he
  have hpost:∀K≤N,∃C H:ℝ,0<C ∧ 0<H ∧ ∀h:ℝ,H≤h→
      ‖G h-∑j∈Finset.range (K+1),cb j/(h:ℂ)^j‖≤C/h^(K+1) := by
    intro K hKN
    obtain ⟨C,H,hC,hH,herror⟩:=fixed_gaussian_model_inverse_power_error f M 1 Rp r hM.le zero_le_one hRp hr hrRp
      hfd hfbound N K hKN
    refine ⟨C,H,hC,hH,?_⟩
    intro h hHh
    have he:=herror h hHh
    have hp:(v:ℂ)*(∑j∈Finset.range (K+1),gaussianModelCoefficient f j/(h:ℂ)^j)=
        ∑j∈Finset.range (K+1),cb j/(h:ℂ)^j := by
      rw[Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      dsimp[cb]
      ring
    rwa[hp] at he
  have heq:=finite_complex_coefficients_unique_of_exp_comparison F G ca cb N hpre hpost hcomp
  intro j hj
  have he:=heq j hj
  dsimp only[ca,cb] at he
  have hv:(v:ℂ)≠0:=by exact_mod_cast (Real.sqrt_pos.mpr (by positivity:0<2*Real.pi)).ne'
  have hc:=mul_left_cancel₀ hv he
  rw[gaussianModelCoefficient_zero_extend b N j hj] at hc
  exact hc

lemma actual_raw_gaussian_numerator_morse_identity (P:PsiTheory) (p:ℕ) (hp:1≤p) (x:ℝ)
    (hx:x∈Ioo (0:ℝ) xCritical) :
    ∃(S B:ℂ→ℂ)(Γ:ℕ→ℂ→ℂ)(U:ℂ→ℂ),
      AnalyticAt ℂ S (x:ℂ) ∧ AnalyticAt ℂ B (x:ℂ) ∧
      ((fun t:ℝ=>S (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(extractionS t:ℂ))) ∧
      ((fun t:ℝ=>B (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(Real.log (extractionB p t):ℂ))) ∧
      (∀s,AnalyticAt ℂ (Γ s) (x:ℂ) ∧
        (fun t:ℝ=>Γ s (t:ℂ))=ᶠ[𝓝 x]
          (fun t:ℝ=>(HigherOrder.markedCoefficient P p s (inverseY t):ℂ))) ∧
      AnalyticAt ℂ U 0 ∧ U 0=0 ∧ deriv U 0=1 ∧
      (∀ᶠz:ℂ in 𝓝 0,extractionStationaryPhase S x (U z)=-z^2/2) ∧
      ∀j:ℕ,((PowerSeries.coeff (2*j) (HigherOrder.extractionNumerator P p x):ℝ):ℂ)=
        gaussianModelCoefficient (extractionMorseGermAmplitude B Γ x U) j := by
  obtain ⟨S,B,β,Γ,U,W,hS,hB,hSr,hBr,hvar,hβ,hβ0,hfac,hΓ,hU,hW,hU0,hW0,hUd,hWd,hconj,
    ρ,C,hρ,hC,hclose⟩:=actual_extraction_stationary_morse_germs P p hp x hx
  refine ⟨S,B,Γ,U,hS,hB,hSr,hBr,hΓ,hU,hU0,hUd,hconj.mono (fun z hz=>hz.2.2),?_⟩
  intro j
  exact raw_numerator_morse_coefficients_of_physical_germs P p hp x hx S B β Γ U W hS hB hSr hBr
    hvar hβ hβ0 hfac hΓ hU hW hU0 (hconj.mono (fun z hz=>⟨hz.1,hz.2.2⟩))
    ρ C hρ hC (fun z hz=>(hclose z hz).2) j j le_rfl
end WP.Analysis
