import WPFormalization.Analysis.PainleveNativeAlgebra
import WPFormalization.HigherOrder.PainleveJumpDefinitions
import Mathlib

/-! The fifth-root coordinate is matched to unwrapped GIKM polar powers and
to the actual positive-real jump coordinate. The genuine GIKM sector data
imply native analyticity with a radius for each fixed angular margin. -/
noncomputable section
namespace WP.Analysis
open Complex Set Filter
open WP.External.PainleveAnalytic

lemma nativeFifthRoot_ray (t θ : ℝ) (ht : 0<t) (hθl : -Real.pi<θ) (hθu : θ≤Real.pi) :
    nativeFifthRoot (ray θ t)=polarPower (t/piAction) θ (1/5) := by
  have hr : 0<t/piAction := div_pos ht HigherOrder.painleveAction_pos
  have he : ray θ t/(piAction:ℂ)=((t/piAction:ℝ):ℂ)*Complex.exp (Complex.I*(θ:ℂ)) := by
    unfold ray
    push_cast
    ring
  unfold nativeFifthRoot
  rw [he,Complex.log_ofReal_mul hr (Complex.exp_ne_zero _),
    Complex.log_exp (by simpa using hθl) (by simpa using hθu)]
  unfold polarPower
  have hp : ((Real.log (t/piAction):ℂ)+Complex.I*(θ:ℂ))/5=
      ((Real.log (t/piAction)*(1/5:ℝ):ℝ):ℂ)+Complex.I*(((1/5:ℝ)*θ:ℝ):ℂ) := by
    push_cast
    ring
  simp only [Real.rpow_eq_pow]
  rw [hp,Complex.exp_add,Real.rpow_def_of_pos hr,Complex.ofReal_exp]

lemma nativeFifthRoot_ray_pow (t θ : ℝ) (ht : 0<t) (hθl : -Real.pi<θ) (hθu : θ≤Real.pi) (n : ℕ) :
    nativeFifthRoot (ray θ t)^n=polarPower (t/piAction) θ ((n:ℝ)/5) := by
  rw [nativeFifthRoot_ray t θ ht hθl hθu]
  unfold polarPower
  rw [mul_pow]
  have hr : 0<t/piAction := div_pos ht HigherOrder.painleveAction_pos
  have hp : (Real.rpow (t/piAction) (1/5))^n=Real.rpow (t/piAction) ((n:ℝ)/5) := by
    simp only [Real.rpow_eq_pow]
    rw [←Real.rpow_natCast,←Real.rpow_mul hr.le]
    congr 1
    ring
  have he : (Complex.exp (Complex.I*(((1/5:ℝ)*θ:ℝ):ℂ)))^n=
      Complex.exp (Complex.I*((((n:ℝ)/5)*θ:ℝ):ℂ)) := by
    rw [←Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [he,←Complex.ofReal_pow,hp]

lemma nativeFifthRoot_ofReal_pow (t : ℝ) (ht : 0<t) (n : ℕ) :
    nativeFifthRoot (t:ℂ)^n=(Real.rpow (t/piAction) ((n:ℝ)/5):ℂ) := by
  have h := nativeFifthRoot_ray_pow t 0 ht (by linarith [Real.pi_pos]) Real.pi_pos.le n
  simpa [ray,polarPower] using h

lemma nativeCoordinate_ofReal (t : ℝ) (ht : 0<t) :
    nativeFifthRoot (t:ℂ)^4=(HigherOrder.painleveJumpCoordinate t:ℂ) := by
  simpa [HigherOrder.painleveJumpCoordinate,piAction] using nativeFifthRoot_ofReal_pow t ht 4

lemma nativeSquare_ofReal (t : ℝ) (ht : 0<t) :
    nativeFifthRoot (t:ℂ)^2=(Real.sqrt (HigherOrder.painleveJumpCoordinate t):ℂ) := by
  rw [nativeFifthRoot_ofReal_pow t ht 2]
  congr 1
  unfold HigherOrder.painleveJumpCoordinate
  change (t/piAction)^((2:ℝ)/5)=Real.sqrt ((t/piAction)^(4/5:ℝ))
  have hr : 0<t/piAction := div_pos ht HigherOrder.painleveAction_pos
  rw [Real.sqrt_eq_rpow,←Real.rpow_mul hr.le]
  congr 1
  norm_num

lemma actualNativeH_ofReal (G : GIKMData) (k : ℤ) (t : ℝ) (ht : 0<t) :
    actualNativeH G k (t:ℂ)=G.u k (HigherOrder.painleveJumpCoordinate t:ℂ)/
      (Real.sqrt (HigherOrder.painleveJumpCoordinate t):ℂ)-1+4/(25*(t:ℂ)^2) := by
  unfold actualNativeH
  rw [nativeCoordinate_ofReal t ht,nativeSquare_ofReal t ht]
lemma native_ray_div_mem_slitPlane (t θ : ℝ) (ht : 0<t)
    (hθl : -Real.pi<θ) (hθu : θ<Real.pi) :
    ray θ t/(piAction:ℂ)∈Complex.slitPlane := by
  have hr : 0<t/piAction := div_pos ht HigherOrder.painleveAction_pos
  have he : ray θ t/(piAction:ℂ)=
      Complex.exp ((Real.log (t/piAction):ℂ)+Complex.I*(θ:ℂ)) := by
    rw [Complex.exp_add,←Complex.ofReal_exp,Real.exp_log hr]
    unfold ray
    push_cast
    ring
  rw [he]
  apply Complex.expOpenPartialHomeomorph.map_source
  change ((Real.log (t/piAction):ℂ)+Complex.I*(θ:ℂ)).im∈Ioo (-Real.pi) Real.pi
  simpa using (show θ∈Ioo (-Real.pi) Real.pi from ⟨hθl,hθu⟩)

lemma nativeCoordinate_ray (t θ : ℝ) (ht : 0<t) (hθl : -Real.pi<θ) (hθu : θ≤Real.pi) :
    nativeFifthRoot (ray θ t)^4=
      ray (4*θ/5) (Real.rpow (t/piAction) (4/5)) := by
  have h := nativeFifthRoot_ray_pow t θ ht hθl hθu 4
  simpa only [polarPower,ray,Nat.cast_ofNat,show (4/5:ℝ)*θ=4*θ/5 by ring] using h

lemma native_radius_eventually_large (R : ℝ) :
    ∃T:ℝ,0<T ∧ ∀t:ℝ,T≤t → R<Real.rpow (t/piAction) (4/5) := by
  have hdiv : Tendsto (fun t:ℝ => t/piAction) atTop atTop :=
    Filter.Tendsto.atTop_div_const HigherOrder.painleveAction_pos tendsto_id
  have hpow : Tendsto (fun t:ℝ => Real.rpow (t/piAction) (4/5)) atTop atTop := by
    simpa only [Real.rpow_eq_pow,Function.comp_def] using
      (tendsto_rpow_atTop (by norm_num : (0:ℝ)<4/5)).comp hdiv
  have he : ∀ᶠ t:ℝ in atTop,R<Real.rpow (t/piAction) (4/5) :=
    (tendsto_atTop.1 hpow (R+1)).mono (fun t ht => lt_of_lt_of_le (by linarith) ht)
  obtain ⟨T,hT⟩ := eventually_atTop.1 he
  refine ⟨max 1 T,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro t ht
  exact hT t ((le_max_right _ _).trans ht)

lemma actualNativeH_analyticAt_of_u (G : GIKMData) (k : ℤ) (x : ℂ) (hx0 : x≠0)
    (hx : x/(piAction:ℂ)∈Complex.slitPlane)
    (hu : AnalyticAt ℂ (G.u k) (nativeFifthRoot x^4)) :
    AnalyticAt ℂ (actualNativeH G k) x := by
  have hq := nativeFifthRoot_analyticAt x hx
  have hq4 : AnalyticAt ℂ (fun z:ℂ => nativeFifthRoot z^4) x := by
    convert hq.pow 4 using 1
  have hU : AnalyticAt ℂ (fun z:ℂ => G.u k (nativeFifthRoot z^4)) x :=
    AnalyticAt.comp (f:=fun z:ℂ => nativeFifthRoot z^4) (x:=x) hu hq4
  have hB : AnalyticAt ℂ (fun z:ℂ => G.u k (nativeFifthRoot z^4)/nativeFifthRoot z^2-1) x :=
    (hU.div (hq.pow 2) (pow_ne_zero 2 (nativeFifthRoot_ne_zero x))).sub analyticAt_const
  have hC : AnalyticAt ℂ (fun z:ℂ => 4/(25*z^2)) x :=
    analyticAt_const.div (analyticAt_const.mul (analyticAt_id.pow 2))
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx0))
  convert hB.add hC using 1
  ext z
  simp [actualNativeH]

lemma nativeDomain_point_properties (s : Side) (ε T : ℝ) (hε : 0<ε) (hT : 0<T)
    (x : ℂ) (hx : x∈nativeDomain s ε T) :
    x≠0 ∧ x/(piAction:ℂ)∈Complex.slitPlane := by
  obtain ⟨t,θ,ht,hθl,hθu,rfl⟩ := hx
  have ht0 : 0<t := hT.trans ht
  have hLo : -Real.pi<θ := by
    cases s <;> simp only [sideSign,one_mul,neg_one_mul] at hθl hθu <;> linarith [Real.pi_pos]
  have hHi : θ<Real.pi := by
    cases s <;> simp only [sideSign,one_mul,neg_one_mul] at hθl hθu <;> linarith [Real.pi_pos]
  have hp := native_ray_div_mem_slitPlane t θ ht0 hLo hHi
  refine ⟨?_,hp⟩
  intro he
  rw [he,zero_div] at hp
  exact Complex.zero_notMem_slitPlane hp

lemma nativeCoordinate_maps_sector (s : Side) (ε R : ℝ) (hε : 0<ε) (hεπ : ε<Real.pi/4) :
    ∃T:ℝ,0<T ∧ ∀x∈nativeDomain s ε T,
      nativeFifthRoot x^4∈gikmSector (if s=Side.upper then 1 else 0) (2*ε/5) R := by
  obtain ⟨T,hT,hRadius⟩ := native_radius_eventually_large R
  refine ⟨T,hT,?_⟩
  intro x hx
  obtain ⟨t,θ,ht,hθl,hθu,rfl⟩ := hx
  have ht0 : 0<t := hT.trans ht
  have hLo : -Real.pi<θ := by
    cases s <;> simp only [sideSign,one_mul,neg_one_mul] at hθl hθu <;> linarith [Real.pi_pos]
  have hHi : θ<Real.pi := by
    cases s <;> simp only [sideSign,one_mul,neg_one_mul] at hθl hθu <;> linarith [Real.pi_pos]
  refine ⟨Real.rpow (t/piAction) (4/5),4*θ/5,hRadius t ht.le,?_,?_,
    nativeCoordinate_ray t θ ht0 hLo hHi.le⟩
  · cases s <;> norm_num [sideSign] at hθl hθu ⊢ <;> linarith [Real.pi_pos]
  · cases s <;> norm_num [sideSign] at hθl hθu ⊢ <;> linarith [Real.pi_pos]

lemma actualNativeH_analytic_nativeDomain (G : GIKMData) (s : Side) (ε : ℝ)
    (hε : 0<ε) (hεπ : ε<Real.pi/4) :
    ∃T:ℝ,0<T ∧ AnalyticOnNhd ℂ (actualNativeH G (if s=Side.upper then 1 else 0))
      (nativeDomain s ε T) := by
  have hδ : 0<2*ε/5 := by positivity
  have hδπ : 2*ε/5<4*Real.pi/5 := by linarith [Real.pi_pos]
  obtain ⟨R,hR,hU⟩ := G.sector_analytic (if s=Side.upper then 1 else 0) (2*ε/5) hδ hδπ
  obtain ⟨T,hT,hMap⟩ := nativeCoordinate_maps_sector s ε R hε hεπ
  refine ⟨T,hT,?_⟩
  intro x hx
  obtain ⟨hx0,hxp⟩ := nativeDomain_point_properties s ε T hε hT x hx
  exact actualNativeH_analyticAt_of_u G _ x hx0 hxp (hU _ (hMap x hx))

end WP.Analysis
