import WPFormalization.Volumes.CriticalLogZ
import WPFormalization.Volumes.CriticalRelativeCoordinate
import WPFormalization.Analysis.DiagonalTaylorAnalytic
/-! Genuine critical standardized phase calculus. The phase is expressed using
the proved X inverse and logarithmic Z unit. Its joint analytic germ, precise
normalized first two angle jets, and gradient identities are derived locally.
The explicit fold and normalization premises are supplied by the preceding
actual kernel modules; no phase conclusion is asserted as an external input. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
def sndPartial (F : ℂ × ℂ → ℂ) (p : ℂ × ℂ) : ℂ := fderiv ℂ F p (0,1)
lemma sndPartial_analytic (F : ℂ × ℂ → ℂ) (p : ℂ × ℂ) (hF : AnalyticAt ℂ F p) :
    AnalyticAt ℂ (sndPartial F) p := by
  exact ((ContinuousLinearMap.apply ℂ ℂ ((0,1):ℂ × ℂ)).analyticAt _).comp hF.fderiv
lemma sndPartial_eq_deriv (F : ℂ × ℂ → ℂ) (p : ℂ × ℂ) (hF : AnalyticAt ℂ F p) :
    sndPartial F p=deriv (fun u : ℂ=>F (p.1,u)) p.2 := by
  have hc : HasDerivAt (fun u : ℂ=>(p.1,u)) ((0,1):ℂ × ℂ) p.2 :=
    (hasDerivAt_const _ _).prodMk (hasDerivAt_id _)
  exact (hF.differentiableAt.hasFDerivAt.comp_hasDerivAt _ hc).deriv.symm
lemma sndPartial_hasDerivAt (F : ℂ × ℂ → ℂ) (p : ℂ × ℂ) (hF : AnalyticAt ℂ F p) :
    HasDerivAt (fun u : ℂ=>F (p.1,u)) (sndPartial F p) p.2 := by
  have hc : HasDerivAt (fun u : ℂ=>(p.1,u)) ((0,1):ℂ × ℂ) p.2 :=
    (hasDerivAt_const _ _).prodMk (hasDerivAt_id _)
  exact hF.differentiableAt.hasFDerivAt.comp_hasDerivAt _ hc
end WP.Analysis
namespace WP.Analysis

def CriticalKernelUnits.centeredPhase (k : CriticalKernelUnits) (L : ℂ→ℂ)
    (q : ℂ × ℂ → ℂ) (p : ℂ × ℂ) : ℂ :=
  -(5/2:ℂ)*Complex.log (q p)-k.logZUnit (p.1*q p)+k.logZUnit p.1-
    Complex.I*k.psiUnit p.1*L p.1*p.2

lemma CriticalKernelUnits.centeredPhase_deriv_at (k : CriticalKernelUnits)
    (L : ℂ→ℂ) (q : ℂ × ℂ → ℂ) (δ u : ℂ) (hδ : δ ≠ 0)
    (hq : DifferentiableAt ℂ (fun v : ℂ=>q (δ,v)) u)
    (hqs : q (δ,u)∈Complex.slitPlane)
    (hJ : DifferentiableAt ℂ k.logZUnit (δ*q (δ,u)))
    (hA : k.A (δ*q (δ,u)) ≠ 0) (ha : k.a₁ (δ*q (δ,u)) ≠ 0)
    (hr : k.r₁ (δ*q (δ,u)) ≠ 0)
    (hXfactor : deriv X ((y₀:ℂ)-δ*q (δ,u))=(δ*q (δ,u))*k.a₁ (δ*q (δ,u)))
    (hJfactor : (δ*q (δ,u))*deriv k.logZUnit (δ*q (δ,u))=
      (k.A (δ*q (δ,u))*k.r₁ (δ*q (δ,u)))⁻¹-(5/2:ℂ))
    (hfold : ∀ᶠv:ℂ in 𝓝 u,
      X ((y₀:ℂ)-δ*q (δ,v))=X ((y₀:ℂ)-δ)*Complex.exp (Complex.I*v*δ^2*L δ)) :
    HasDerivAt (fun v:ℂ=>k.centeredPhase L q (δ,v))
      (Complex.I*L δ*k.psiUnit (δ*q (δ,u))/(q (δ,u))^2-
        Complex.I*k.psiUnit δ*L δ) u := by
  let q' : ℂ := deriv (fun v : ℂ=>q (δ,v)) u
  have hqn : q (δ,u) ≠ 0 := Complex.slitPlane_ne_zero hqs
  have hqD : HasDerivAt (fun v : ℂ=>q (δ,v)) q' u := hq.hasDerivAt
  have harg : HasDerivAt (fun v:ℂ=>(y₀:ℂ)-δ*q (δ,v)) (-δ*q') u := by
    convert! (hasDerivAt_const u (y₀:ℂ)).sub (hqD.const_mul δ) using 1 <;> ring
  have hleft := (X_differentiable _).hasDerivAt.comp u harg
  have hexp : HasDerivAt (fun v : ℂ=>Complex.exp (Complex.I*v*δ^2*L δ))
      (Complex.exp (Complex.I*u*δ^2*L δ)*(Complex.I*δ^2*L δ)) u := by
    have hz : HasDerivAt (fun v : ℂ=>Complex.I*v*δ^2*L δ) (Complex.I*δ^2*L δ) u := by
      convert! (((hasDerivAt_id u).const_mul Complex.I).mul_const (δ^2)).mul_const (L δ) using 1 <;> ring
    exact hz.cexp
  have hright := hexp.const_mul (X ((y₀:ℂ)-δ))
  have hfoldEq : (fun v:ℂ=>X ((y₀:ℂ)-δ*q (δ,v))) =ᶠ[𝓝 u]
      (fun v:ℂ=>X ((y₀:ℂ)-δ)*Complex.exp (Complex.I*v*δ^2*L δ)) := hfold
  have hde := (hleft.congr_of_eventuallyEq hfoldEq.symm).unique hright
  have hval := hfold.self_of_nhds
  have heq : -q (δ,u)*k.a₁ (δ*q (δ,u))*q'=
      X ((y₀:ℂ)-δ*q (δ,u))*Complex.I*L δ := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hδ)
    rw [hXfactor] at hde
    rw [hval]
    linear_combination hde
  have hqformula : q'=-(X ((y₀:ℂ)-δ*q (δ,u))*Complex.I*L δ)/
      (q (δ,u)*k.a₁ (δ*q (δ,u))) := by
    apply (eq_div_iff (mul_ne_zero hqn ha)).mpr
    linear_combination -heq
  have hlog := (Complex.hasDerivAt_log hqs).comp u hqD
  have hinner := hqD.const_mul δ
  have hJd := hJ.hasDerivAt.comp u hinner
  have hd := (((hlog.const_mul (-(5/2:ℂ))).sub hJd).add_const (k.logZUnit δ)).sub
    ((hasDerivAt_id u).const_mul (Complex.I*k.psiUnit δ*L δ))
  have hJre : (5/2:ℂ)+δ*q (δ,u)*deriv k.logZUnit (δ*q (δ,u))=
      (k.A (δ*q (δ,u))*k.r₁ (δ*q (δ,u)))⁻¹ := by
    linear_combination hJfactor
  have hslope : -(5/2:ℂ)*((q (δ,u))⁻¹*q')-
      deriv k.logZUnit (δ*q (δ,u))*(δ*q')=
        Complex.I*L δ*k.psiUnit (δ*q (δ,u))/(q (δ,u))^2 := by
    calc _ = -((5/2:ℂ)+δ*q (δ,u)*deriv k.logZUnit (δ*q (δ,u)))*q'/q (δ,u) := by
              field_simp
              <;> ring
         _ = -(k.A (δ*q (δ,u))*k.r₁ (δ*q (δ,u)))⁻¹*q'/q (δ,u) := by rw [hJre]
         _ = _ := by
           rw [hqformula,CriticalKernelUnits.psiUnit]
           field_simp
           <;> ring
  convert! hd using 1
  rw [mul_one,hslope]
end WP.Analysis

namespace WP.Analysis
lemma CriticalKernelUnits.centeredPhase_analytic (k : CriticalKernelUnits)
    (L : ℂ→ℂ) (q : ℂ × ℂ→ℂ) (hL : AnalyticAt ℂ L 0)
    (hq : AnalyticAt ℂ q (0,0)) (hq0 : q (0,0)=1) :
    AnalyticAt ℂ (k.centeredPhase L q) (0,0) := by
  have hplane : q (0,0)∈Complex.slitPlane := by rw [hq0];simp
  have hJp : AnalyticAt ℂ (fun p:ℂ × ℂ=>k.logZUnit p.1) (0,0) :=
    AnalyticAt.comp (f:=Prod.fst) (x:=((0,0):ℂ × ℂ)) k.logZUnit_analytic analyticAt_fst
  have hψp : AnalyticAt ℂ (fun p:ℂ × ℂ=>k.psiUnit p.1) (0,0) :=
    AnalyticAt.comp (f:=Prod.fst) (x:=((0,0):ℂ × ℂ)) k.psiUnit_analytic analyticAt_fst
  have hLp : AnalyticAt ℂ (fun p:ℂ × ℂ=>L p.1) (0,0) :=
    AnalyticAt.comp (f:=Prod.fst) (x:=((0,0):ℂ × ℂ)) hL analyticAt_fst
  have ht : AnalyticAt ℂ (fun p:ℂ × ℂ=>p.1*q p) (0,0) := analyticAt_fst.mul hq
  have hJt : AnalyticAt ℂ (fun p:ℂ × ℂ=>k.logZUnit (p.1*q p)) (0,0) := by
    have hJa : AnalyticAt ℂ k.logZUnit (((0,0):ℂ × ℂ).1*q (0,0)) := by simpa using k.logZUnit_analytic
    exact AnalyticAt.comp (f:=fun p:ℂ × ℂ=>p.1*q p) (x:=((0,0):ℂ × ℂ)) hJa ht
  exact ((((analyticAt_const.mul ((analyticAt_clog hplane).comp hq)).sub hJt).add hJp).sub
    (((analyticAt_const.mul hψp).mul hLp).mul analyticAt_snd))

lemma CriticalKernelUnits.centeredPhase_axis (k : CriticalKernelUnits)
    (L : ℂ→ℂ) (q : ℂ × ℂ→ℂ) (hqaxis : ∀ᶠδ:ℂ in 𝓝 0,q (δ,0)=1) :
    ∀ᶠδ:ℂ in 𝓝 0,k.centeredPhase L q (δ,0)=0 := by
  filter_upwards [hqaxis] with δ hδ
  simp [CriticalKernelUnits.centeredPhase,hδ]

lemma CriticalKernelUnits.relative_inverse_deriv_at (k : CriticalKernelUnits)
    (L : ℂ→ℂ) (q : ℂ × ℂ→ℂ) (δ u : ℂ) (hδ : δ≠0)
    (hq : DifferentiableAt ℂ (fun v:ℂ=>q (δ,v)) u)
    (hqn : q (δ,u)≠0) (ha : k.a₁ (δ*q (δ,u))≠0)
    (hXfactor : deriv X ((y₀:ℂ)-δ*q (δ,u))=(δ*q (δ,u))*k.a₁ (δ*q (δ,u)))
    (hfold : ∀ᶠv:ℂ in 𝓝 u,
      X ((y₀:ℂ)-δ*q (δ,v))=X ((y₀:ℂ)-δ)*Complex.exp (Complex.I*v*δ^2*L δ)) :
    HasDerivAt (fun v:ℂ=>q (δ,v))
      (-(X ((y₀:ℂ)-δ*q (δ,u))*Complex.I*L δ)/(q (δ,u)*k.a₁ (δ*q (δ,u)))) u := by
  let q' : ℂ := deriv (fun v:ℂ=>q (δ,v)) u
  have hqD : HasDerivAt (fun v:ℂ=>q (δ,v)) q' u := hq.hasDerivAt
  have harg : HasDerivAt (fun v:ℂ=>(y₀:ℂ)-δ*q (δ,v)) (-δ*q') u := by
    convert! (hasDerivAt_const u (y₀:ℂ)).sub (hqD.const_mul δ) using 1 <;> ring
  have hleft := (X_differentiable _).hasDerivAt.comp u harg
  have hexp : HasDerivAt (fun v:ℂ=>Complex.exp (Complex.I*v*δ^2*L δ))
      (Complex.exp (Complex.I*u*δ^2*L δ)*(Complex.I*δ^2*L δ)) u := by
    have hz : HasDerivAt (fun v:ℂ=>Complex.I*v*δ^2*L δ) (Complex.I*δ^2*L δ) u := by
      convert! (((hasDerivAt_id u).const_mul Complex.I).mul_const (δ^2)).mul_const (L δ) using 1 <;> ring
    exact hz.cexp
  have hright := hexp.const_mul (X ((y₀:ℂ)-δ))
  have hfoldEq : (fun v:ℂ=>X ((y₀:ℂ)-δ*q (δ,v))) =ᶠ[𝓝 u]
      (fun v:ℂ=>X ((y₀:ℂ)-δ)*Complex.exp (Complex.I*v*δ^2*L δ)) := hfold
  have hde := (hleft.congr_of_eventuallyEq hfoldEq.symm).unique hright
  have hval := hfold.self_of_nhds
  have heq : -q (δ,u)*k.a₁ (δ*q (δ,u))*q'=
      X ((y₀:ℂ)-δ*q (δ,u))*Complex.I*L δ := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hδ)
    rw [hXfactor] at hde
    rw [hval]
    linear_combination hde
  have hqformula : q'=-(X ((y₀:ℂ)-δ*q (δ,u))*Complex.I*L δ)/
      (q (δ,u)*k.a₁ (δ*q (δ,u))) := by
    apply (eq_div_iff (mul_ne_zero hqn ha)).mpr
    linear_combination -heq
  exact hqformula ▸ hqD
end WP.Analysis

namespace WP.Analysis
lemma CriticalKernelUnits.normalization_square (k : CriticalKernelUnits)
    (L : ℂ→ℂ) (hL : AnalyticAt ℂ L 0)
    (hphysical : ∀ᶠδ:ℝ in 𝓝 0,0<δ→
      (δ:ℂ)^2*L (δ:ℂ)=((Real.sqrt (euler Psi (XR (y₀-δ))))⁻¹:ℝ)) :
    ∀ᶠδ:ℂ in 𝓝 0,k.varianceUnit δ*(L δ)^2=1 := by
  apply complex_germ_identity_of_real_right _ _ (k.varianceUnit_analytic.mul (hL.pow 2)) analyticAt_const
  filter_upwards [k.physical,k.varianceUnit_physical,hphysical] with δ hphys hvar hnorm hδ
  obtain ⟨hδlt,_,_,_⟩ := hphys hδ
  have hY : y₀-δ ∈ Ico (0:ℝ) y₀ := ⟨by linarith,by linarith⟩
  have hxp : 0 < XR (y₀-δ) := by
    have hh := XR_strictMonoOn (show (0:ℝ)≤y₀ from y₀_pos.le) hY.2.le (by linarith : 0<y₀-δ)
    simpa only [XR_zero] using hh
  have hx : XR (y₀-δ) ∈ Ico (0:ℝ) xCritical :=
    ⟨hxp.le,XR_strictMonoOn hY.2.le (by simp) hY.2⟩
  have hvp : 0 < euler Psi (XR (y₀-δ)) := mul_pos hxp (Psi_deriv_pos_interior _ hx)
  have hs : (((Real.sqrt (euler Psi (XR (y₀-δ)))):ℂ))^2=(euler Psi (XR (y₀-δ)):ℂ) := by
    exact_mod_cast Real.sq_sqrt hvp.le
  have hsn : ((Real.sqrt (euler Psi (XR (y₀-δ)))):ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hvp).ne'
  change k.varianceUnit (δ:ℂ)*L (δ:ℂ)^2=1
  calc _ = (euler Psi (XR (y₀-δ)):ℂ)*((δ:ℂ)^2*L (δ:ℂ))^2 := by
          rw [hvar hδ]
          push_cast
          ring
       _ = (euler Psi (XR (y₀-δ)):ℂ)*(((Real.sqrt (euler Psi (XR (y₀-δ)))):ℂ)⁻¹)^2 := by
          rw [hnorm hδ,Complex.ofReal_inv]
       _ = 1 := by rw [inv_pow,←hs,mul_inv_cancel₀ (pow_ne_zero 2 hsn)]
end WP.Analysis

namespace WP.Analysis
lemma CriticalKernelUnits.centeredPhase_gradient_germ (k : CriticalKernelUnits)
    (L : ℂ→ℂ) (q : ℂ × ℂ→ℂ) (hL : AnalyticAt ℂ L 0)
    (hq : AnalyticAt ℂ q (0,0)) (hq0 : q (0,0)=1)
    (hfold : ∀ᶠp:ℂ × ℂ in 𝓝 (0,0),
      X ((y₀:ℂ)-p.1*q p)=X ((y₀:ℂ)-p.1)*Complex.exp (Complex.I*p.2*p.1^2*L p.1)) :
    ∀ᶠp:ℂ × ℂ in 𝓝 (0,0),p.1≠0→
      sndPartial (k.centeredPhase L q) p=
        Complex.I*L p.1*k.psiUnit (p.1*q p)/(q p)^2-Complex.I*k.psiUnit p.1*L p.1 := by
  have hTa : AnalyticAt ℂ (fun p:ℂ × ℂ=>p.1*q p) (0,0) := analyticAt_fst.mul hq
  have hTt : Tendsto (fun p:ℂ × ℂ=>p.1*q p) (𝓝 (0,0)) (𝓝 (0:ℂ)) := by
    simpa using hTa.continuousAt.tendsto
  have hA0 : k.A 0≠0 := by rw [k.A_zero];norm_num
  have ha0 : k.a₁ 0≠0 := by rw [k.a_zero];exact_mod_cast criticalB_pos.ne'
  have hr0 : k.r₁ 0≠0 := by rw [k.r_zero];norm_num
  have hplane : q (0,0)∈Complex.slitPlane := by rw [hq0];simp
  have hqplane := hq.continuousAt.eventually (Complex.isOpen_slitPlane.mem_nhds hplane)
  have hphase := k.centeredPhase_analytic L q hL hq hq0
  filter_upwards [hq.eventually_analyticAt,hphase.eventually_analyticAt,hqplane,
    hTt.eventually k.logZUnit_analytic.eventually_analyticAt,
    hTt.eventually (k.A_analytic.continuousAt.eventually_ne hA0),
    hTt.eventually (k.a_analytic.continuousAt.eventually_ne ha0),
    hTt.eventually (k.r_analytic.continuousAt.eventually_ne hr0),
    hTt.eventually k.derivX_factor,hTt.eventually k.logZUnit_deriv,hfold.eventually_nhds]
    with p hqp hψp hqs hJ hA ha hr hXf hJf hfoldp hδ
  have hcurve : ContinuousAt (fun v:ℂ=>(p.1,v)) p.2 := by fun_prop
  have hfoldslice := hcurve.tendsto.eventually hfoldp
  have hd := k.centeredPhase_deriv_at L q p.1 p.2 hδ hqp.curry_right.differentiableAt
    hqs hJ.differentiableAt hA ha hr hXf hJf hfoldslice
  exact (sndPartial_hasDerivAt _ p hψp).unique hd

lemma CriticalKernelUnits.gradient_axis_hasDerivAt (k : CriticalKernelUnits)
    (L : ℂ→ℂ) (q : ℂ→ℂ) (δ : ℂ)
    (hq0 : q 0=1) (ha : k.a₁ δ≠0)
    (hqD : HasDerivAt q (-(X ((y₀:ℂ)-δ)*Complex.I*L δ)/k.a₁ δ) 0)
    (hψ : DifferentiableAt ℂ k.psiUnit δ)
    (hsquare : k.varianceUnit δ*(L δ)^2=1) :
    HasDerivAt (fun u:ℂ=>Complex.I*L δ*k.psiUnit (δ*q u)/(q u)^2-
        Complex.I*k.psiUnit δ*L δ) (-1) 0 := by
  let q' : ℂ := -(X ((y₀:ℂ)-δ)*Complex.I*L δ)/k.a₁ δ
  have hq : HasDerivAt q q' 0 := hqD
  have harg : HasDerivAt (fun u:ℂ=>δ*q u) (δ*q') 0 := hq.const_mul δ
  have hψq : HasDerivAt (fun u:ℂ=>k.psiUnit (δ*q u)) (deriv k.psiUnit δ*(δ*q')) 0 := by
    have hp : HasDerivAt k.psiUnit (deriv k.psiUnit δ) (δ*q 0) := by
      simpa only [hq0,mul_one] using hψ.hasDerivAt
    exact hp.comp 0 harg
  have hnum := hψq.const_mul (Complex.I*L δ)
  have hden := hq.pow 2
  have hquot := hnum.div hden (by simp only [Pi.pow_apply,hq0,one_pow];norm_num)
  have hs : Complex.I*L δ*(deriv k.psiUnit δ*(δ*q'))-
      Complex.I*L δ*k.psiUnit δ*(2*q')= -k.varianceUnit δ*(L δ)^2 := by
    dsimp only [q',CriticalKernelUnits.varianceUnit]
    field_simp
    simp only [Complex.I_sq]
    ring
  convert! hquot.sub_const (Complex.I*k.psiUnit δ*L δ) using 1
  simp only [Pi.pow_apply,hq0,mul_one,one_pow,div_one,Nat.cast_ofNat,Nat.reduceSub,pow_one]
  rw [hs,neg_mul,hsquare]
end WP.Analysis

namespace WP.Analysis
lemma CriticalKernelUnits.centeredPhase_jets (k : CriticalKernelUnits)
    (L : ℂ→ℂ) (q : ℂ × ℂ→ℂ) (hL : AnalyticAt ℂ L 0)
    (hq : AnalyticAt ℂ q (0,0)) (hq0 : q (0,0)=1)
    (hqaxis : ∀ᶠδ:ℂ in 𝓝 0,q (δ,0)=1)
    (hfold : ∀ᶠp:ℂ × ℂ in 𝓝 (0,0),
      X ((y₀:ℂ)-p.1*q p)=X ((y₀:ℂ)-p.1)*Complex.exp (Complex.I*p.2*p.1^2*L p.1))
    (hsquare : ∀ᶠδ:ℂ in 𝓝 0,k.varianceUnit δ*(L δ)^2=1) :
    ∀ᶠδ:ℂ in 𝓝 0,k.centeredPhase L q (δ,0)=0 ∧
      sndPartial (k.centeredPhase L q) (δ,0)=0 ∧
      sndPartial (sndPartial (k.centeredPhase L q)) (δ,0)=-1 := by
  let F : ℂ × ℂ→ℂ := k.centeredPhase L q
  have hF : AnalyticAt ℂ F (0,0) := k.centeredPhase_analytic L q hL hq hq0
  have hFp := sndPartial_analytic F (0,0) hF
  have hFpp := sndPartial_analytic (sndPartial F) (0,0) hFp
  have haxis : Tendsto (fun δ:ℂ=>(δ,(0:ℂ))) (𝓝 0) (𝓝 ((0,0):ℂ × ℂ)) := by
    exact (show ContinuousAt (fun δ:ℂ=>(δ,(0:ℂ))) 0 by fun_prop).tendsto
  have hPa : AnalyticAt ℂ (fun δ:ℂ=>sndPartial F (δ,0)) 0 :=
    AnalyticAt.comp (f:=fun δ:ℂ=>(δ,(0:ℂ))) (x:=0) hFp (analyticAt_id.prod analyticAt_const)
  have hPPa : AnalyticAt ℂ (fun δ:ℂ=>sndPartial (sndPartial F) (δ,0)) 0 :=
    AnalyticAt.comp (f:=fun δ:ℂ=>(δ,(0:ℂ))) (x:=0) hFpp (analyticAt_id.prod analyticAt_const)
  have hgrad := k.centeredPhase_gradient_germ L q hL hq hq0 hfold
  have hfirst : (fun δ:ℂ=>sndPartial F (δ,0)) =ᶠ[𝓝 0] (fun _=>0) := by
    apply (hPa.frequently_eq_iff_eventually_eq analyticAt_const).mp
    have he : (fun δ:ℂ=>sndPartial F (δ,0)) =ᶠ[𝓝[≠] 0] (fun _=>0) := by
      filter_upwards [(haxis.eventually hgrad).filter_mono nhdsWithin_le_nhds,
        hqaxis.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with δ hd hqδ hδ
      have hn : δ≠0 := by simpa only [mem_compl_iff,mem_singleton_iff] using hδ
      change sndPartial (k.centeredPhase L q) (δ,0)=0
      rw [hd hn,hqδ,mul_one,one_pow,div_one]
      ring
    exact he.frequently
  have ha0 : k.a₁ 0≠0 := by rw [k.a_zero];exact_mod_cast criticalB_pos.ne'
  have hsecond : (fun δ:ℂ=>sndPartial (sndPartial F) (δ,0)) =ᶠ[𝓝 0] (fun _=>-1) := by
    apply (hPPa.frequently_eq_iff_eventually_eq analyticAt_const).mp
    have he : (fun δ:ℂ=>sndPartial (sndPartial F) (δ,0)) =ᶠ[𝓝[≠] 0] (fun _=>-1) := by
      filter_upwards [(haxis.eventually hgrad.eventually_nhds).filter_mono nhdsWithin_le_nhds,
        (haxis.eventually hfold.eventually_nhds).filter_mono nhdsWithin_le_nhds,
        (haxis.eventually hq.eventually_analyticAt).filter_mono nhdsWithin_le_nhds,
        (haxis.eventually hFp.eventually_analyticAt).filter_mono nhdsWithin_le_nhds,
        hqaxis.filter_mono nhdsWithin_le_nhds,hsquare.filter_mono nhdsWithin_le_nhds,
        k.derivX_factor.filter_mono nhdsWithin_le_nhds,
        k.psiUnit_analytic.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
        (k.a_analytic.continuousAt.eventually_ne ha0).filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin]
        with δ hgradloc hfoldloc hqδ hFpδ hqaxisδ hsδ hXδ hψδ haδ hδ
      have hn : δ≠0 := by simpa only [mem_compl_iff,mem_singleton_iff] using hδ
      have hcurve : ContinuousAt (fun u:ℂ=>(δ,u)) 0 := by fun_prop
      have hfoldslice := hcurve.tendsto.eventually hfoldloc
      have hqD := k.relative_inverse_deriv_at L q δ 0 hn hqδ.curry_right.differentiableAt
        (by rw [hqaxisδ];norm_num) (by simpa only [hqaxisδ,mul_one] using haδ)
        (by simpa only [hqaxisδ,mul_one] using hXδ) hfoldslice
      have hqD' : HasDerivAt (fun u:ℂ=>q (δ,u))
          (-(X ((y₀:ℂ)-δ)*Complex.I*L δ)/k.a₁ δ) 0 := by
        simpa only [hqaxisδ,mul_one,one_mul] using hqD
      have hdG := k.gradient_axis_hasDerivAt L (fun u:ℂ=>q (δ,u)) δ hqaxisδ haδ hqD'
        hψδ.differentiableAt hsδ
      have hegrad : (fun u:ℂ=>sndPartial F (δ,u)) =ᶠ[𝓝 0]
          (fun u:ℂ=>Complex.I*L δ*k.psiUnit (δ*q (δ,u))/(q (δ,u))^2-
            Complex.I*k.psiUnit δ*L δ) := by
        filter_upwards [hcurve.tendsto.eventually hgradloc] with u hu
        exact hu hn
      have hdP := hdG.congr_of_eventuallyEq hegrad
      exact (sndPartial_hasDerivAt (sndPartial F) (δ,0) hFpδ).unique hdP
    exact he.frequently
  filter_upwards [k.centeredPhase_axis L q hqaxis,hfirst,hsecond] with δ h0 h1 h2
  exact ⟨h0,h1,h2⟩
end WP.Analysis
