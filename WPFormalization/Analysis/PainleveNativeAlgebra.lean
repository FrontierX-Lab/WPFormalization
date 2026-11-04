import WPFormalization.External.PainleveAnalyticData
import WPFormalization.HigherOrder.PureEndpoint
import Mathlib

/-! The actual native coordinate q=exp(log(x/A)/5) and the normalized GIKM
solution u(q^4)/q^2-1+4/(25x^2). The fifth-root identity, both derivatives and
the native PI equation are proved. At a regular native point the required
analyticity of u is recovered by the formal analytic inverse theorem.
Sector analyticity and decay are separate subsequent obligations.
-/
noncomputable section
namespace WP.Analysis
open Complex Filter
abbrev piAction : ℝ := WP.External.painleveAction

def nativeFifthRoot (x : ℂ) : ℂ := Complex.exp (Complex.log (x/(piAction:ℂ))/5)

def actualNativeH (G : WP.External.PainleveAnalytic.GIKMData) (k : ℤ) (x : ℂ) : ℂ :=
  G.u k ((nativeFifthRoot x)^4)/(nativeFifthRoot x)^2-1+4/(25*x^2)

lemma nativeFifthRoot_ne_zero (x : ℂ) : nativeFifthRoot x≠0 := Complex.exp_ne_zero _
lemma nativeFifthRoot_pow_five (x : ℂ) (hx : x≠0) :
    nativeFifthRoot x^5=x/(piAction:ℂ) := by
  unfold nativeFifthRoot
  rw [←Complex.exp_nat_mul]
  norm_num
  rw [show (5:ℂ)*(Complex.log (x/(piAction:ℂ))/5)=Complex.log (x/(piAction:ℂ)) by ring,
    Complex.exp_log (div_ne_zero hx (Complex.ofReal_ne_zero.mpr HigherOrder.painleveAction_pos.ne'))]

lemma nativeFifthRoot_hasDerivAt (x : ℂ) (hx0 : x≠0)
    (hx : x/(piAction:ℂ)∈Complex.slitPlane) :
    HasDerivAt nativeFifthRoot (nativeFifthRoot x/(5*x)) x := by
  have ha0 : (piAction:ℂ)≠0 := Complex.ofReal_ne_zero.mpr HigherOrder.painleveAction_pos.ne'
  have hd := (((hasDerivAt_id x).div_const (piAction:ℂ)).clog hx).div_const (5:ℂ) |>.cexp
  convert hd using 1
  · funext z
    rfl
  · dsimp [nativeFifthRoot]
    field_simp [ha0,hx0]
lemma nativeFifthRoot_analyticAt (x : ℂ) (hx : x/(piAction:ℂ)∈Complex.slitPlane) :
    AnalyticAt ℂ nativeFifthRoot x := by
  exact (((analyticAt_id.div_const (c:=(piAction:ℂ))).clog hx).div_const (c:=(5:ℂ))).cexp

lemma nativeCoordinate_hasDerivAt (x : ℂ) (hx0 : x≠0)
    (hx : x/(piAction:ℂ)∈Complex.slitPlane) :
    HasDerivAt (fun z:ℂ => nativeFifthRoot z^4) (4*nativeFifthRoot x^4/(5*x)) x := by
  apply (nativeFifthRoot_hasDerivAt x hx0 hx |>.pow 4).congr_deriv
  field_simp [hx0]
  ring

lemma actualNativeH_analytic_recovers_u (G : WP.External.PainleveAnalytic.GIKMData) (k : ℤ)
    (x : ℂ) (hx0 : x≠0) (hx : x/(piAction:ℂ)∈Complex.slitPlane)
    (hh : AnalyticAt ℂ (actualNativeH G k) x) :
    AnalyticAt ℂ (G.u k) (nativeFifthRoot x^4) := by
  have hq := nativeFifthRoot_analyticAt x hx
  have hq0 := nativeFifthRoot_ne_zero x
  have hcoord := nativeCoordinate_hasDerivAt x hx0 hx
  have hcoord0 : deriv (fun z:ℂ => nativeFifthRoot z^4) x≠0 := by
    rw [hcoord.deriv]
    exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 4 hq0))
      (mul_ne_zero (by norm_num) hx0)
  have hEq : (fun z:ℂ => G.u k (nativeFifthRoot z^4))=
      (fun z:ℂ => (actualNativeH G k z+1-4/(25*z^2))*nativeFifthRoot z^2) := by
    funext z
    unfold actualNativeH
    field_simp [nativeFifthRoot_ne_zero z]
    ring
  have hComp : AnalyticAt ℂ (fun z:ℂ => G.u k (nativeFifthRoot z^4)) x := by
    rw [hEq]
    apply AnalyticAt.mul _ (hq.pow 2)
    apply AnalyticAt.sub (hh.add analyticAt_const)
    exact analyticAt_const.div (analyticAt_const.mul (analyticAt_id.pow 2))
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx0))
  apply (analyticAt_comp_iff_of_deriv_ne_zero (hq.pow 4) hcoord0).mp
  simpa only [Function.comp_def,Pi.pow_apply] using hComp

def nativeJet0 (x q u : ℂ) : ℂ := u/q^2-1+4/(25*x^2)
def nativeJet1 (x q u u₁ : ℂ) : ℂ := 4*q^2*u₁/(5*x)-2*u/(5*x*q^2)-8/(25*x^3)
def nativeJet2 (x q u u₁ u₂ : ℂ) : ℂ :=
  16*q^6*u₂/(25*x^2)-4*q^2*u₁/(5*x^2)+14*u/(25*x^2*q^2)+24/(25*x^4)

lemma native_ode_residual_factor (x q u u₁ : ℂ) (hx : x≠0) (hq : q≠0) :
    nativeJet2 x q u u₁ (6*u^2-6*q^4)+nativeJet1 x q u u₁/x-
      nativeJet0 x q u-(nativeJet0 x q u)^2/2-(392/625:ℂ)/x^4=
      (96*q^10/(25*x^2)-1/2)*((u/q^2)^2-1) := by
  unfold nativeJet0 nativeJet1 nativeJet2
  field_simp [hx,hq]
  ring

lemma nativeFifthRoot_pow_ten (x : ℂ) (hx : x≠0) :
    nativeFifthRoot x^10=(25/192:ℂ)*x^2 := by
  have ha2R : piAction^2=(192/25:ℝ) := HigherOrder.painleveAction_sq
  have ha2 : (piAction:ℂ)^2=(192/25:ℂ) := by
    rw [←Complex.ofReal_pow,ha2R]
    norm_num
  calc
    _ = (nativeFifthRoot x^5)^2 := by ring
    _ = (x/(piAction:ℂ))^2 := by rw [nativeFifthRoot_pow_five x hx]
    _ = _ := by rw [div_pow,ha2];ring

lemma native_ode_residual_zero (x u u₁ : ℂ) (hx : x≠0) :
    nativeJet2 x (nativeFifthRoot x) u u₁ (6*u^2-6*(nativeFifthRoot x)^4)+
      nativeJet1 x (nativeFifthRoot x) u u₁/x-
      nativeJet0 x (nativeFifthRoot x) u-(nativeJet0 x (nativeFifthRoot x) u)^2/2-
        (392/625:ℂ)/x^4=0 := by
  rw [native_ode_residual_factor x (nativeFifthRoot x) u u₁ hx (nativeFifthRoot_ne_zero x),
    nativeFifthRoot_pow_ten x hx]
  have he : 96*((25/192:ℂ)*x^2)/(25*x^2)-1/2=0 := by field_simp [hx];ring
  rw [he,zero_mul]

def actualNativeH1 (G : WP.External.PainleveAnalytic.GIKMData) (k : ℤ) (x : ℂ) : ℂ :=
  nativeJet1 x (nativeFifthRoot x) (G.u k (nativeFifthRoot x^4))
    (deriv (G.u k) (nativeFifthRoot x^4))

def actualNativeH2 (G : WP.External.PainleveAnalytic.GIKMData) (k : ℤ) (x : ℂ) : ℂ :=
  nativeJet2 x (nativeFifthRoot x) (G.u k (nativeFifthRoot x^4))
    (deriv (G.u k) (nativeFifthRoot x^4)) (deriv (deriv (G.u k)) (nativeFifthRoot x^4))

lemma actualNativeH_hasDerivAt (G : WP.External.PainleveAnalytic.GIKMData) (k : ℤ)
    (x : ℂ) (hx0 : x≠0) (hx : x/(piAction:ℂ)∈Complex.slitPlane)
    (hu : AnalyticAt ℂ (G.u k) (nativeFifthRoot x^4)) :
    HasDerivAt (actualNativeH G k) (actualNativeH1 G k x) x := by
  have hq := nativeFifthRoot_hasDerivAt x hx0 hx
  have hq0 := nativeFifthRoot_ne_zero x
  have hU := hu.differentiableAt.hasDerivAt.comp x (hq.pow 4)
  have hB := (hU.div (hq.pow 2) (pow_ne_zero 2 hq0)).sub_const 1
  have hC := (hasDerivAt_const x (4:ℂ)).div ((hasDerivAt_id x |>.pow 2).const_mul (25:ℂ))
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx0))
  apply (hB.add hC).congr_deriv
  unfold actualNativeH1 nativeJet1
  simp only [Pi.pow_apply,Function.comp_apply,id_eq]
  field_simp [hx0,hq0]
  ring

lemma actualNativeH1_hasDerivAt (G : WP.External.PainleveAnalytic.GIKMData) (k : ℤ)
    (x : ℂ) (hx0 : x≠0) (hx : x/(piAction:ℂ)∈Complex.slitPlane)
    (hu : AnalyticAt ℂ (G.u k) (nativeFifthRoot x^4)) :
    HasDerivAt (actualNativeH1 G k) (actualNativeH2 G k x) x := by
  have hq := nativeFifthRoot_hasDerivAt x hx0 hx
  have hq0 := nativeFifthRoot_ne_zero x
  have hU := hu.differentiableAt.hasDerivAt.comp x (hq.pow 4)
  have hU1 := hu.deriv.differentiableAt.hasDerivAt.comp x (hq.pow 4)
  have hA := (((hq.pow 2).const_mul (4:ℂ)).mul hU1).div
    ((hasDerivAt_id x).const_mul (5:ℂ)) (mul_ne_zero (by norm_num) hx0)
  have hB := (hU.const_mul (2:ℂ)).div
    (((hasDerivAt_id x).const_mul (5:ℂ)).mul (hq.pow 2))
    (mul_ne_zero (mul_ne_zero (by norm_num) hx0) (pow_ne_zero 2 hq0))
  have hC := (hasDerivAt_const x (8:ℂ)).div ((hasDerivAt_id x |>.pow 3).const_mul (25:ℂ))
    (mul_ne_zero (by norm_num) (pow_ne_zero 3 hx0))
  apply ((hA.sub hB).sub hC).congr_deriv
  unfold actualNativeH2 nativeJet2
  simp only [Pi.pow_apply,Pi.mul_apply,Function.comp_apply,id_eq]
  field_simp [hx0,hq0]
  ring

lemma actualNativeH_ode (G : WP.External.PainleveAnalytic.GIKMData) (k : ℤ)
    (x : ℂ) (hx0 : x≠0) (hx : x/(piAction:ℂ)∈Complex.slitPlane)
    (hh : AnalyticAt ℂ (actualNativeH G k) x) :
    deriv (deriv (actualNativeH G k)) x+deriv (actualNativeH G k) x/x-
      actualNativeH G k x-(actualNativeH G k x)^2/2-(392/625:ℂ)/x^4=0 := by
  have hu := actualNativeH_analytic_recovers_u G k x hx0 hx hh
  have hq := nativeFifthRoot_analyticAt x hx
  have hξe : ∀ᶠ y:ℂ in nhds x,y/(piAction:ℂ)∈Complex.slitPlane := by
    have hc : Continuous (fun y:ℂ => y/(piAction:ℂ)) := by fun_prop
    exact (hc.tendsto x).eventually (Complex.isOpen_slitPlane.mem_nhds hx)
  have hξ0 : ∀ᶠ y:ℂ in nhds x,y≠0 := eventually_ne_nhds hx0
  have hue : ∀ᶠ y:ℂ in nhds x,AnalyticAt ℂ (G.u k) (nativeFifthRoot y^4) := by
    simpa only [Pi.pow_apply] using (hq.pow 4).continuousAt.tendsto.eventually hu.eventually_analyticAt
  have hDerEq : deriv (actualNativeH G k)=ᶠ[nhds x] actualNativeH1 G k := by
    filter_upwards [hξe,hξ0,hue] with y hy hy0 huy
    exact (actualNativeH_hasDerivAt G k y hy0 hy huy).deriv
  have hd2 := (actualNativeH1_hasDerivAt G k x hx0 hx hu).congr_of_eventuallyEq hDerEq |>.deriv
  have hd1 := (actualNativeH_hasDerivAt G k x hx0 hx hu).deriv
  rw [hd2,hd1]
  change nativeJet2 x (nativeFifthRoot x) (G.u k (nativeFifthRoot x^4))
      (deriv (G.u k) (nativeFifthRoot x^4)) (deriv (deriv (G.u k)) (nativeFifthRoot x^4))+
    nativeJet1 x (nativeFifthRoot x) (G.u k (nativeFifthRoot x^4))
      (deriv (G.u k) (nativeFifthRoot x^4))/x-
    nativeJet0 x (nativeFifthRoot x) (G.u k (nativeFifthRoot x^4))-
      (nativeJet0 x (nativeFifthRoot x) (G.u k (nativeFifthRoot x^4)))^2/2-
      (392/625:ℂ)/x^4=0
  rw [G.ode k (nativeFifthRoot x^4) hu]
  exact native_ode_residual_zero x (G.u k (nativeFifthRoot x^4))
    (deriv (G.u k) (nativeFifthRoot x^4)) hx0

end WP.Analysis
