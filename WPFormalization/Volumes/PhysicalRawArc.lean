import WPFormalization.Volumes.PhysicalPhaseCorrection
import WPFormalization.Volumes.RawMorseMatching
import WPFormalization.HigherOrder.PhaseFamilyModel
noncomputable section
namespace WP.Analysis
open Set Filter MeasureTheory
open scoped Topology
lemma premorse_centered_model_integrand (S Bc:ℂ→ℂ)(Γ:ℕ→ℂ→ℂ)
    (h x v:ℝ)(k N:ℕ)(u:ℝ)(hh:0<h)(hv:0<v)
    (hν:(h:ℂ)*complexEuler S (x:ℂ)=(k:ℂ)):
    Complex.exp ((h:ℂ)*centeredExponentialSlice S (x:ℂ)
      (Complex.I/(Real.sqrt v:ℂ)) (u:ℂ)) *
      ((Bc ((x:ℂ)*Complex.exp ((Complex.I/(Real.sqrt v:ℂ))*(u:ℂ)))/Bc (x:ℂ))*
        ∑s∈Finset.range (N+1),(((1/Real.sqrt h:ℝ):ℂ))^(2*s)*
          Γ s ((x:ℂ)*Complex.exp ((Complex.I/(Real.sqrt v:ℂ))*(u:ℂ))))=
    (Bc (x:ℂ))⁻¹*(Complex.exp (-(k:ℂ)*((u/Real.sqrt v:ℝ):ℂ)*Complex.I)*
      Complex.exp (-((h:ℂ)*S (x:ℂ)))*
        HigherOrder.phaseFamilyModel S (fun s z=>Bc z*Γ s z) h N
          ((x:ℂ)*Complex.exp (((u/Real.sqrt v:ℝ):ℂ)*Complex.I))):=by
  have hs:(Real.sqrt v:ℂ)≠0:=by exact_mod_cast (Real.sqrt_pos.mpr hv).ne'
  have ha:(Complex.I/(Real.sqrt v:ℂ))*(u:ℂ)=(((u/Real.sqrt v:ℝ):ℂ))*Complex.I:=by
    push_cast
    ring
  have he:Complex.exp ((h:ℂ)*centeredExponentialSlice S (x:ℂ)
      (Complex.I/(Real.sqrt v:ℂ)) (u:ℂ))=
      Complex.exp (-(k:ℂ)*((u/Real.sqrt v:ℝ):ℂ)*Complex.I)*
        Complex.exp (-((h:ℂ)*S (x:ℂ)))*
        Complex.exp ((h:ℂ)*S ((x:ℂ)*Complex.exp (((u/Real.sqrt v:ℝ):ℂ)*Complex.I))):=by
    rw[←Complex.exp_add,←Complex.exp_add]
    unfold centeredExponentialSlice
    rw[ha]
    have ht:(h:ℂ)*((((u/Real.sqrt v:ℝ):ℂ))*Complex.I*complexEuler S (x:ℂ))=
        (k:ℂ)*(((u/Real.sqrt v:ℝ):ℂ))*Complex.I:=by
      calc _=((u/Real.sqrt v:ℝ):ℂ)*Complex.I*((h:ℂ)*complexEuler S (x:ℂ)):=by ring
           _= _:=by rw[hν];ring
    congr 1
    linear_combination -ht
  rw[he,ha,HigherOrder.phaseFamilyModel]
  have hsum:(∑s∈Finset.range (N+1),(((1/Real.sqrt h:ℝ):ℂ))^(2*s)*
      Γ s ((x:ℂ)*Complex.exp (((u/Real.sqrt v:ℝ):ℂ)*Complex.I)))=
      ∑s∈Finset.range (N+1),(h:ℂ)⁻¹^s*Γ s ((x:ℂ)*Complex.exp (((u/Real.sqrt v:ℝ):ℂ)*Complex.I)):=by
    apply Finset.sum_congr rfl
    intro s hss
    rw[(inverse_sqrt_even_power h hh s).1,inv_pow,one_div]
  rw[hsum]
  have hsum2:(∑s∈Finset.range (N+1),(h:ℂ)⁻¹^s*(Bc ((x:ℂ)*Complex.exp (((u/Real.sqrt v:ℝ):ℂ)*Complex.I))*
      Γ s ((x:ℂ)*Complex.exp (((u/Real.sqrt v:ℝ):ℂ)*Complex.I))))=
      Bc ((x:ℂ)*Complex.exp (((u/Real.sqrt v:ℝ):ℂ)*Complex.I))*
      (∑s∈Finset.range (N+1),(h:ℂ)⁻¹^s*Γ s ((x:ℂ)*Complex.exp (((u/Real.sqrt v:ℝ):ℂ)*Complex.I))):=by
    rw[Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hss
    ring
  rw[hsum2]
  ring
lemma rawScaledGaussianIntegral_eq_centered_arc (S B Bc:ℂ→ℂ)(Γ:ℕ→ℂ→ℂ)
    (β:ℂ→ℂ)(A:ℂ × ℂ→ℂ)(R h x v:ℝ)(k N:ℕ)
    (hR:0<R)(hh:0<h)(hv:0<v)
    (hν:(h:ℂ)*complexEuler S (x:ℂ)=(k:ℂ))
    (hA:∀τ u:ℂ,A (τ,u)=Complex.exp (B ((x:ℂ)*Complex.exp ((Complex.I/(Real.sqrt v:ℂ))*u))-B (x:ℂ))*
      ∑s∈Finset.range (N+1),τ^(2*s)*Γ s ((x:ℂ)*Complex.exp ((Complex.I/(Real.sqrt v:ℂ))*u)))
    (hfac:∀u∈Icc (-(R/4)) (R/4),centeredExponentialSlice S (x:ℂ)
      (Complex.I/(Real.sqrt v:ℂ)) (u:ℂ)=(u:ℂ)^2*(β (u:ℂ)-(1/2:ℂ)))
    (hBexp:∀u∈Icc (-(R/4)) (R/4),
      Complex.exp (B ((x:ℂ)*Complex.exp ((Complex.I/(Real.sqrt v:ℂ))*(u:ℂ)))-B (x:ℂ))=
        Bc ((x:ℂ)*Complex.exp ((Complex.I/(Real.sqrt v:ℂ))*(u:ℂ)))/Bc (x:ℂ)):
    rawScaledGaussianIntegral β A R h=(Real.sqrt h:ℂ)*(Real.sqrt v:ℂ)/(Bc (x:ℂ))*
      ∫θ:ℝ in (-(R/(4*Real.sqrt v)))..(R/(4*Real.sqrt v)),
        Complex.exp (-(k:ℂ)*(θ:ℂ)*Complex.I)*Complex.exp (-((h:ℂ)*S (x:ℂ)))*
          HigherOrder.phaseFamilyModel S (fun s z=>Bc z*Γ s z) h N
            ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)):=by
  unfold rawScaledGaussianIntegral
  rw[stationary_inverse_sqrt_rescale β A R h hR.le hh]
  let f:ℝ→ℂ:=fun θ=>Complex.exp (-(k:ℂ)*(θ:ℂ)*Complex.I)*Complex.exp (-((h:ℂ)*S (x:ℂ)))*
    HigherOrder.phaseFamilyModel S (fun s z=>Bc z*Γ s z) h N ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))
  have he:(∫u:ℝ in Icc (-(R/4)) (R/4),Complex.exp ((h:ℂ)*((u:ℂ)^2*(β (u:ℂ)-(1/2:ℂ))))*
      A (((1/Real.sqrt h:ℝ):ℂ),(u:ℂ)))=
      (Bc (x:ℂ))⁻¹*∫u:ℝ in (-(R/4))..(R/4),f (u/Real.sqrt v):=by
    rw[←intervalIntegral.integral_const_mul,←symmetric_set_integral_eq_interval _ (R/4) (by positivity)]
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    dsimp only
    rw[←hfac u hu,hA,hBexp u hu]
    exact premorse_centered_model_integrand S Bc Γ h x v k N u hh hv hν
  rw[he,intervalIntegral.integral_comp_div f (Real.sqrt_pos.mpr hv).ne']
  have hl:-(R/4)/Real.sqrt v= -(R/(4*Real.sqrt v)):=by ring
  have hr:(R/4)/Real.sqrt v=R/(4*Real.sqrt v):=by ring
  rw[hl,hr,Complex.real_smul]
  ring
end WP.Analysis
namespace WP.Analysis
open Set Filter MeasureTheory
open scoped Topology
lemma physical_raw_centered_arc_data (P:PsiTheory)(p:ℕ)(hp:1≤p)(x:ℝ)
    (hx:x∈Ioo (0:ℝ) xCritical)(S Bc:ℂ→ℂ)(Γ:ℕ→ℂ→ℂ)
    (hS:AnalyticAt ℂ S (x:ℂ))(hBc:AnalyticAt ℂ Bc (x:ℂ))
    (hSr:(fun t:ℝ=>S (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(extractionS t:ℂ)))
    (hBcr:(fun t:ℝ=>Bc (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(extractionB p t:ℂ)))
    (hΓ:∀s,AnalyticAt ℂ (Γ s) (x:ℂ) ∧
      (fun t:ℝ=>Γ s (t:ℂ))=ᶠ[𝓝 x]
        (fun t:ℝ=>(HigherOrder.markedCoefficient P p s (inverseY t):ℂ))) (N:ℕ):
    ∃β:ℂ→ℂ,∃A:ℂ × ℂ→ℂ,∃R δ:ℝ,0<R ∧ 0<δ ∧ δ≤Real.pi ∧
      (∀h:ℝ,∀k:ℕ,0<h→h*WP.Psi x=(k:ℝ)→
        rawScaledGaussianIntegral β A R h=(Real.sqrt h:ℂ)*(Real.sqrt (WP.euler WP.Psi x):ℂ)/(Bc (x:ℂ))*
          ∫θ:ℝ in (-δ)..δ,Complex.exp (-(k:ℂ)*(θ:ℂ)*Complex.I)*Complex.exp (-((h:ℂ)*S (x:ℂ)))*
            HigherOrder.phaseFamilyModel S (fun s z=>Bc z*Γ s z) h N
              ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))) ∧
      (∀K≤N,∃C H:ℝ,0<C ∧ 0<H ∧ ∀h:ℝ,H≤h→
        ‖rawScaledGaussianIntegral β A R h-(Real.sqrt (2*Real.pi):ℂ)*
          ∑j∈Finset.range (K+1),((PowerSeries.coeff (2*j) (HigherOrder.extractionNumerator P p x):ℝ):ℂ)/(h:ℂ)^j‖≤C/h^(K+1)):=by
  obtain ⟨hν,β,hv,hβ,hβ0,hfac⟩:=physical_phase_correction_of_trace S x hx hS hSr
  have hBcx:Bc (x:ℂ)=(extractionB p x:ℂ):=hBcr.self_of_nhds
  have hBpos:0<extractionB p x:=extractionB_pos_interior p x ⟨hx.1.le,hx.2⟩
  have hBcne:Bc (x:ℂ)≠0:=by rw[hBcx];exact_mod_cast hBpos.ne'
  let B:ℂ→ℂ:=fun z=>Complex.log (Bc z)
  have hBa:AnalyticAt ℂ B (x:ℂ):=hBc.clog (by rw[hBcx];exact Or.inl hBpos)
  have hBr:(fun t:ℝ=>B (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(Real.log (extractionB p t):ℂ)):=by
    filter_upwards[hBcr,isOpen_Ioo.mem_nhds hx] with t ht htx
    dsimp[B]
    rw[ht,←Complex.ofReal_log (extractionB_pos_interior p t ⟨htx.1.le,htx.2⟩).le]
  have ht:Tendsto (fun u:ℂ=>(x:ℂ)*Complex.exp ((Complex.I/(Real.sqrt (WP.euler WP.Psi x):ℂ))*u))
      (𝓝 0) (𝓝 (x:ℂ)):=by
    have hc:ContinuousAt (fun u:ℂ=>(x:ℂ)*Complex.exp ((Complex.I/(Real.sqrt (WP.euler WP.Psi x):ℂ))*u)) 0:=by fun_prop
    simpa only[mul_zero,Complex.exp_zero,mul_one] using hc.tendsto
  have hBexp:∀ᶠu:ℂ in 𝓝 0,
      Complex.exp (B ((x:ℂ)*Complex.exp ((Complex.I/(Real.sqrt (WP.euler WP.Psi x):ℂ))*u))-B (x:ℂ))=
        Bc ((x:ℂ)*Complex.exp ((Complex.I/(Real.sqrt (WP.euler WP.Psi x):ℂ))*u))/Bc (x:ℂ):=by
    filter_upwards[ht.eventually (hBc.continuousAt.eventually_ne hBcne)] with u hu
    dsimp[B]
    rw[Complex.exp_sub,Complex.exp_log hu,Complex.exp_log hBcne]
  obtain ⟨r0,hr0,hloc⟩:=Metric.eventually_nhds_iff.mp (hfac.and hBexp)
  let cap:ℝ:=min r0 (4*Real.pi*Real.sqrt (WP.euler WP.Psi x))
  have hcap:0<cap:=lt_min hr0 (by positivity)
  obtain ⟨A,R,hR,hRcap,hA,hcoeff,hraw⟩:=raw_gaussian_integral_of_physical_germs P p x N S B β Γ
    hS hBa hSr hBr hv hβ hβ0 hfac hΓ cap hcap
  let δ:ℝ:=R/(4*Real.sqrt (WP.euler WP.Psi x))
  have hδ:0<δ:=by dsimp[δ];positivity
  have hδπ:δ≤Real.pi:=by
    dsimp[δ]
    apply (div_le_iff₀ (by positivity:0<4*Real.sqrt (WP.euler WP.Psi x))).mpr
    have hb:=hRcap.trans (min_le_right r0 _)
    nlinarith
  have hlocal(u:ℝ)(hu:u∈Icc (-(R/4)) (R/4)):
      centeredExponentialSlice S (x:ℂ) (Complex.I/(Real.sqrt (WP.euler WP.Psi x):ℂ)) (u:ℂ)=
        (u:ℂ)^2*(β (u:ℂ)-(1/2:ℂ)) ∧
      Complex.exp (B ((x:ℂ)*Complex.exp ((Complex.I/(Real.sqrt (WP.euler WP.Psi x):ℂ))*(u:ℂ)))-B (x:ℂ))=
        Bc ((x:ℂ)*Complex.exp ((Complex.I/(Real.sqrt (WP.euler WP.Psi x):ℂ))*(u:ℂ)))/Bc (x:ℂ):=by
    apply hloc
    rw[dist_zero_right,Complex.norm_real,Real.norm_eq_abs]
    have habs:|u|≤R/4:=abs_le.mpr ⟨hu.1,hu.2⟩
    have hb:=hRcap.trans (min_le_left r0 (4*Real.pi*Real.sqrt (WP.euler WP.Psi x)))
    nlinarith
  refine ⟨β,A,R,δ,hR,hδ,hδπ,?_,?_⟩
  · intro h k hh hk
    exact rawScaledGaussianIntegral_eq_centered_arc S B Bc Γ β A R h x (WP.euler WP.Psi x) k N hR hh hv
      (by rw[hν];exact_mod_cast hk) hA (fun u hu=>(hlocal u hu).1) (fun u hu=>(hlocal u hu).2)
  · intro K hKN
    exact raw_gaussian_inverse_power_error_of_tau P p hp x hx β A R hR K (hraw K hKN)
end WP.Analysis
