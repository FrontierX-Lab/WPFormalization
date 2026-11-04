import WPFormalization.Analysis.PainleveNativeCoordinates
import WPFormalization.Analysis.NativeZeroParameter
import Mathlib
/-! The genuine fixed-N=1 GIKM algebraic remainder implies native decay
uniformly on each proper angular sector and on the selected imaginary ray.
The CCH lateral parameter is then proved to vanish, so its exact zero-parameter
representation applies to the actual transformed GIKM solutions. -/
noncomputable section
namespace WP.Analysis
open Complex Set Filter
open WP.External.PainleveAnalytic

lemma native_polarPower_comp (b θ q p : ℝ) (hb : 0<b) :
    polarPower (Real.rpow b q) (q*θ) p=polarPower b θ (q*p) := by
  unfold polarPower
  simp only [Real.rpow_eq_pow]
  rw [←Real.rpow_mul hb.le]
  congr 1
  congr 1
  push_cast
  ring

lemma native_polarPower_inv (b θ p : ℝ) (hb : 0<b) :
    (polarPower b θ p)⁻¹=polarPower b θ (-p) := by
  unfold polarPower
  simp only [Real.rpow_eq_pow]
  rw [Real.rpow_neg hb.le,mul_inv_rev,Complex.ofReal_inv]
  have he : Complex.I*(((-p)*θ:ℝ):ℂ)=-(Complex.I*((p*θ:ℝ):ℂ)) := by push_cast;ring
  rw [he,Complex.exp_neg]
  ring

lemma native_polarPower_norm (b θ p : ℝ) (hb : 0<b) :
    ‖polarPower b θ p‖=Real.rpow b p := by
  unfold polarPower
  simp only [Real.rpow_eq_pow]
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hb p),Complex.norm_exp]
  simp

def nativeAsymptoticPolynomial (x : ℂ) : ℂ :=
  nativeFifthRoot x^2-1/(48*nativeFifthRoot x^8)

lemma native_source_polynomial_one (G : GIKMData) (t θ : ℝ)
    (ht : 0<t) (hθl : -Real.pi<θ) (hθu : θ≤Real.pi) :
    algebraicPolynomial G.a 1 (Real.rpow (t/piAction) (4/5)) (4*θ/5)=
      nativeAsymptoticPolynomial (ray θ t) := by
  have hb : 0<t/piAction := div_pos ht HigherOrder.painleveAction_pos
  have hlead : polarPower (Real.rpow (t/piAction) (4/5)) (4*θ/5) (1/2)=
      nativeFifthRoot (ray θ t)^2 := by
    have hc := native_polarPower_comp (t/piAction) θ (4/5) (1/2) hb
    have hq := nativeFifthRoot_ray_pow t θ ht hθl hθu 2
    norm_num at hc hq
    simpa only [Real.rpow_eq_pow, show 4*θ/5=(4/5:ℝ)*θ by ring] using hc.trans hq.symm
  have htail : polarPower (Real.rpow (t/piAction) (4/5)) (4*θ/5) (-2)=
      (nativeFifthRoot (ray θ t)^8)⁻¹ := by
    have hc := native_polarPower_comp (t/piAction) θ (4/5) (-2) hb
    have hq := nativeFifthRoot_ray_pow t θ ht hθl hθu 8
    have hi := native_polarPower_inv (t/piAction) θ (8/5) hb
    norm_num at hc hq hi
    rw [←hq] at hi
    simpa only [Real.rpow_eq_pow, show 4*θ/5=(4/5:ℝ)*θ by ring] using hc.trans hi.symm
  have ha1 : G.a 1=(-1/48:ℚ) := by
    rw [G.sourceCoefficient_eq_actual]
    exact HigherOrder.zeroInstantonCoefficient_one
  norm_num [algebraicPolynomial,Finset.sum_range_succ,G.a_zero,ha1]
  simp only [Real.rpow_eq_pow] at hlead htail
  rw [hlead,htail]
  unfold nativeAsymptoticPolynomial
  ring

lemma actualNativeH_as_error (G : GIKMData) (k : ℤ) (x : ℂ) (hx : x≠0) :
    actualNativeH G k x=(G.u k (nativeFifthRoot x^4)-nativeAsymptoticPolynomial x)/nativeFifthRoot x^2 := by
  have hq := nativeFifthRoot_ne_zero x
  have hc : 1/(48*nativeFifthRoot x^10)=4/(25*x^2) := by
    rw [nativeFifthRoot_pow_ten x hx]
    field_simp [hx]
    ring
  unfold actualNativeH nativeAsymptoticPolynomial
  rw [←hc]
  field_simp [hq]
  ring

lemma native_decay_power_identity (t : ℝ) (ht : 0<t) :
    Real.rpow (Real.rpow (t/piAction) (4/5)) (-9/2)/Real.rpow (t/piAction) (2/5)=
      piAction^4*Real.rpow t (-4) := by
  have hb : 0<t/piAction := div_pos ht HigherOrder.painleveAction_pos
  simp only [Real.rpow_eq_pow]
  rw [←Real.rpow_mul hb.le,←Real.rpow_sub hb]
  have he : (4/5:ℝ)*(-9/2)-(2/5)=-4 := by ring
  rw [he]
  have hbn : (t/piAction)^(-4:ℝ)=((t/piAction)^4)⁻¹ := by
    rw [Real.rpow_neg hb.le]
    norm_num
  have htn : t^(-4:ℝ)=(t^4)⁻¹ := by
    rw [Real.rpow_neg ht.le]
    norm_num
  rw [hbn,htn,div_pow,inv_div]
  ring
lemma actualNativeH_decay_native_sector (G : GIKMData) (s : Side) (ε : ℝ)
    (hε : 0<ε) (hεπ : ε<Real.pi/4) :
    ∃ C R:ℝ,0<C ∧ 0<R ∧ ∀t θ:ℝ,R≤t →
      -Real.pi/2+ε<sideSign s*θ → sideSign s*θ<3*Real.pi/4 →
      ‖actualNativeH G (if s=Side.upper then 1 else 0) (ray θ t)‖≤C*Real.rpow t (-4) := by
  have hδ : 0<2*ε/5 := by positivity
  have hδπ : 2*ε/5<4*Real.pi/5 := by linarith [Real.pi_pos]
  obtain ⟨C,R,hC,hR,hErr⟩ := G.fixed_algebraic
    (if s=Side.upper then 1 else 0) 1 (2*ε/5) hδ hδπ
  obtain ⟨T,hT,hRadius⟩ := native_radius_eventually_large R
  refine ⟨C*piAction^4,T,mul_pos hC (pow_pos HigherOrder.painleveAction_pos _),hT,?_⟩
  intro t θ ht hθl hθu
  have ht0 : 0<t := hT.trans_le ht
  have hb : 0<t/piAction := div_pos ht0 HigherOrder.painleveAction_pos
  have hLo : -Real.pi<θ := by
    cases s <;> simp only [sideSign,one_mul,neg_one_mul] at hθl hθu <;> linarith [Real.pi_pos]
  have hHi : θ<Real.pi := by
    cases s <;> simp only [sideSign,one_mul,neg_one_mul] at hθl hθu <;> linarith [Real.pi_pos]
  have hl : -6*Real.pi/5+4*Real.pi*(if s=Side.upper then (1:ℤ) else 0)/5+2*ε/5≤4*θ/5 := by
    cases s <;> norm_num [sideSign] at hθl hθu ⊢ <;> linarith [Real.pi_pos]
  have hu : 4*θ/5≤2*Real.pi/5+4*Real.pi*(if s=Side.upper then (1:ℤ) else 0)/5-2*ε/5 := by
    cases s <;> norm_num [sideSign] at hθl hθu ⊢ <;> linarith [Real.pi_pos]
  have herr := hErr (Real.rpow (t/piAction) (4/5)) (4*θ/5) (hRadius t ht).le hl hu
  rw [←nativeCoordinate_ray t θ ht0 hLo hHi.le,
    native_source_polynomial_one G t θ ht0 hLo hHi.le] at herr
  norm_num at herr
  have hqnorm : ‖nativeFifthRoot (ray θ t)^2‖=Real.rpow (t/piAction) (2/5) := by
    rw [nativeFifthRoot_ray_pow t θ ht0 hLo hHi.le 2]
    simpa using native_polarPower_norm (t/piAction) θ (2/5) hb
  have hx0 : ray θ t≠0 := by
    have hp := native_ray_div_mem_slitPlane t θ ht0 hLo hHi
    intro hh
    rw [hh,zero_div] at hp
    exact Complex.zero_notMem_slitPlane hp
  calc
    _ = ‖G.u (if s=Side.upper then 1 else 0) (nativeFifthRoot (ray θ t)^4)-
          nativeAsymptoticPolynomial (ray θ t)‖/Real.rpow (t/piAction) (2/5) := by
      rw [actualNativeH_as_error G _ _ hx0,norm_div,hqnorm]
    _ ≤ C*Real.rpow (Real.rpow (t/piAction) (4/5)) (-9/2)/Real.rpow (t/piAction) (2/5) := by
      apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hb.le _)
      simpa only [Real.rpow_eq_pow,neg_div] using herr
    _ = _ := by
      rw [mul_div_assoc,native_decay_power_identity t ht0]
      ring

lemma actualNativeH_nativeSmall (G : GIKMData) (s : Side) :
    NativeSmall s (actualNativeH G (if s=Side.upper then 1 else 0)) := by
  refine ⟨actualNativeH_analytic_nativeDomain G s,?_,?_⟩
  · intro x hx hh
    obtain ⟨ε,R,hε,hεπ,hR,hx⟩ := hx
    obtain ⟨hx0,hxp⟩ := nativeDomain_point_properties s ε R hε hR x hx
    exact actualNativeH_ode G _ x hx0 hxp hh
  · intro ε hε hεπ
    let ε' : ℝ := min (ε/2) (Real.pi/8)
    have he' : 0<ε' := lt_min (by positivity) (by positivity)
    have he'π : ε'<Real.pi/4 := by
      have hp := min_le_right (ε/2) (Real.pi/8)
      dsimp [ε']
      linarith [Real.pi_pos]
    obtain ⟨C,R,hC,hR,hd⟩ := actualNativeH_decay_native_sector G s ε' he' he'π
    refine ⟨C,R,hC,hR,?_⟩
    intro t θ ht hθ
    obtain ⟨hθl,hθu⟩ := abs_le.mp hθ
    have hle : ε'≤ε/2 := min_le_left _ _
    apply hd t θ ht
    · cases s <;> simp only [sideSign,one_mul,neg_one_mul] <;> linarith
    · cases s <;> simp only [sideSign,one_mul,neg_one_mul] <;> linarith [Real.pi_pos]

lemma actualNativeH_decay_selectedRay (G : GIKMData) (s : Side) :
    ∃ C R:ℝ,0<C ∧ 0<R ∧ ∀t:ℝ,R≤t →
      ‖actualNativeH G (if s=Side.upper then 1 else 0) (ray (sideSign s*Real.pi/2) t)‖≤
        C*Real.rpow t (-4) := by
  obtain ⟨C,R,hC,hR,hd⟩ := actualNativeH_decay_native_sector G s (Real.pi/8)
    (by positivity) (by linarith [Real.pi_pos])
  refine ⟨C,R,hC,hR,?_⟩
  intro t ht
  apply hd t _ ht <;> cases s <;> norm_num [sideSign] <;> linarith [Real.pi_pos]

lemma actualNativeH_cch_parameter_zero (G : GIKMData) (D : CCHData) (s : Side) :
    D.parameter s (actualNativeH G (if s=Side.upper then 1 else 0))=0 := by
  obtain ⟨C,R,_,_,hd⟩ := actualNativeH_decay_selectedRay G s
  exact cch_parameter_eq_zero_of_ray_decay D s _ (actualNativeH_nativeSmall G s) C R hd

lemma actualNativeH_eq_lateral_sum (G : GIKMData) (D : CCHData) (s : Side)
    (φ:ℝ) (hφ:0<φ) (hφπ:φ<Real.pi/2) :
    ∃ξ₀:ℝ,0<ξ₀ ∧ ∀ξ:ℝ,ξ₀≤ξ →
      actualNativeH G (if s=Side.upper then 1 else 0) (ξ:ℂ)=
        laplaceAlong D.H₀ (-sideSign s*φ) ξ :=
  D.zero_parameter_sum s _ (actualNativeH_nativeSmall G s)
    (actualNativeH_cch_parameter_zero G D s) φ hφ hφπ

end WP.Analysis
