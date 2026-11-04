import WPFormalization.Volumes.CompactModelRealTrace
import WPFormalization.Analysis.StationaryTaylorCoefficients
/-! One actual compact-interior leading Gaussian chart. A single common tuple is chosen before the physical point and genus. The logarithmic phase has the literal normalized jets, the true leading amplitude has axis one, and the uniform real trace is centered at the arbitrary real mean h*Psi. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace WP.Analysis
def compactCenteredLogAction (S L:ℂ→ℂ) (h:ℝ) (x w:ℂ):ℂ:=
  (h:ℂ)*centeredExponentialPhase S L (x,-Complex.I*w/(Real.sqrt h:ℂ))
def compactLeadingCenteredAmplitude (P:PsiTheory) (Bc L:ℂ→ℂ) (f:ℕ→ℂ→ℂ) (h:ℝ) (x w:ℂ):ℂ:=
  compactPremorseAmplitude P Bc L f 0 (x,-Complex.I*w/(Real.sqrt h:ℂ))
lemma compactCenteredLogAction_jets (S L:ℂ→ℂ) (h:ℝ) (hh:0<h) (x:ℂ)
    (hS:AnalyticAt ℂ S x) (hnorm:L x^2*((complexEuler^[2]) S) x=1) :
    compactCenteredLogAction S L h x 0=0 ∧ WP.coeff (compactCenteredLogAction S L h x) 1=0 ∧
      WP.coeff (compactCenteredLogAction S L h x) 2=(1/2:ℂ) := by
  let φ:ℂ→ℂ:=fun u=>centeredExponentialPhase S L (x,u)
  let c:ℂ:= -Complex.I/(Real.sqrt h:ℂ)
  have hjet:=centeredExponentialSlice_jets S x (Complex.I*L x) hS
  have hsecond:=centeredExponentialPhase_second S L x hS hnorm
  have hc(n:ℕ):WP.coeff (compactCenteredLogAction S L h x) n=
      (h:ℂ)*c^n*WP.coeff φ n := by
    have he:compactCenteredLogAction S L h x=(fun w:ℂ=>(h:ℂ)*φ (w*c)):=by
      funext w;dsimp only[compactCenteredLogAction,φ,c];congr 2;ring
    rw[he]
    have ht:=congrArg (PowerSeries.coeff n) (taylor_const_mul (h:ℂ) (fun w:ℂ=>φ (w*c)))
    simp only[taylor_coeff,PowerSeries.coeff_C_mul] at ht
    rw[ht,coeff_complex_scale_right]
    ring
  have hc1:WP.coeff φ 1=0 := by
    simpa only[WP.coeff,Nat.factorial_one,Nat.cast_one,div_one,iteratedDeriv_one,φ,
      centeredExponentialPhase] using hjet.2.1
  have hc2:WP.coeff φ 2= -(1/2:ℂ) := by
    change iteratedDeriv 2 φ 0/(2:ℂ)= -(1/2:ℂ)
    rw[hsecond]
    ring
  have hs:(Real.sqrt h:ℂ)≠0:=by exact_mod_cast (Real.sqrt_pos.mpr hh).ne'
  have hs2:(Real.sqrt h:ℂ)^2=(h:ℂ):=by exact_mod_cast Real.sq_sqrt hh.le
  refine ⟨by simp[compactCenteredLogAction,centeredExponentialPhase,centeredExponentialSlice],?_,?_⟩
  · rw[hc,hc1,mul_zero]
  · rw[hc,hc2]
    dsimp only[c]
    rw[div_pow,neg_sq,Complex.I_sq,hs2]
    have hn:(h:ℂ)≠0:=by exact_mod_cast hh.ne'
    field_simp

lemma actual_compact_leading_gaussian_chart (P:PsiTheory) (p:ℕ) (hp:1≤p)
    (a b:ℝ) (ha:0<a) (hab:a≤b) (hbc:b<xCritical) :
    ∃(S L Bc:ℂ→ℂ)(f:ℕ→ℂ→ℂ)(ρ C D:ℝ),0<ρ ∧ 0<C ∧ 0<D ∧
      ∀x∈Icc a b,∀g:ℕ,Stable g p→0<(complexity g p:ℝ)→
      let h:ℝ:=complexity g p
      let logA:ℂ→ℂ:=compactCenteredLogAction S L h (x:ℂ)
      let amp:ℂ→ℂ:=compactLeadingCenteredAmplitude P Bc L f h (x:ℂ)
      AnalyticOnNhd ℂ logA (Metric.ball 0 (ρ*Real.sqrt h)) ∧
      logA 0=0 ∧ WP.coeff logA 1=0 ∧ WP.coeff logA 2=(1/2:ℂ) ∧
      (∀w:ℂ,‖w‖<ρ*Real.sqrt h→‖logA w‖≤C*‖w‖^2) ∧
      AnalyticOnNhd ℂ amp (Metric.ball 0 (ρ*Real.sqrt h)) ∧ amp 0=1 ∧
      (∀w:ℂ,‖w‖<ρ*Real.sqrt h→‖amp w‖≤D) ∧
      ∀u:ℝ,|u|<ρ*Real.sqrt h→
        let σ:ℝ:=Real.sqrt (h*WP.euler WP.Psi x)
        let xt:ℝ:=x*Real.exp (u/σ)
        xt∈Ioo (0:ℝ) xCritical ∧
        Complex.exp (logA (u:ℂ))*amp (u:ℂ)=
          Complex.exp (-((h*WP.Psi x:ℝ):ℂ)*(u:ℂ)/(σ:ℂ))*
            ((markedModel g p (inverseY xt)/markedModel g p (inverseY x):ℝ):ℂ) := by
  obtain ⟨S,L,Bc,f,Ω,r,C,B,hΩ,hcover,hr,hC,hB,hdata,hBc,hf,hAf,hstate⟩:=
    actual_compact_model_uniform_data P p hp a b ha hab hbc
  obtain ⟨rt,hrt,htrace⟩:=compact_real_trace_uniform a b ha hab hbc S L
    (fun x hx=>(hdata x hx).2.1) (fun x hx=>(hdata x hx).2.2.1)
  let ρ:ℝ:=min r rt
  have hρ:0<ρ:=lt_min hr hrt
  have hρr:ρ≤r:=min_le_left _ _
  have hρt:ρ≤rt:=min_le_right _ _
  refine ⟨S,L,Bc,f,ρ,1,C,hρ,by norm_num,hC,?_⟩
  intro x hx g hs hh
  dsimp only
  let h:ℝ:=complexity g p
  have hsqrt:0<Real.sqrt h:=Real.sqrt_pos.mpr hh
  obtain ⟨hS,hL,hSr,hν,hv,hLr,hunit⟩:=hdata x hx
  have hxI:x∈Ioo (0:ℝ) xCritical:=⟨ha.trans_le hx.1,hx.2.trans_lt hbc⟩
  have hxco:x∈Ico (0:ℝ) xCritical:=⟨hxI.1.le,hxI.2⟩
  have hvar:0<WP.euler WP.Psi x:=mul_pos hxI.1 (Psi_deriv_pos_interior x hxco)
  have hhn:(Real.sqrt h:ℂ)≠0:=by exact_mod_cast hsqrt.ne'
  have hpoint(w:ℂ)(hw:‖w‖<ρ*Real.sqrt h):‖-Complex.I*w/(Real.sqrt h:ℂ)‖<r := by
    rw[norm_div,norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_of_nonneg hsqrt.le]
    exact ((div_lt_iff₀ hsqrt).mpr hw).trans_le hρr
  have hmap(w:ℂ):AnalyticAt ℂ (fun w:ℂ=>((x:ℂ),-Complex.I*w/(Real.sqrt h:ℂ))) w:=
    analyticAt_const.prod ((analyticAt_const.mul analyticAt_id).div analyticAt_const hhn)
  have hjet:=compactCenteredLogAction_jets S L h hh (x:ℂ) hS hunit.self_of_nhds
  refine ⟨?_,hjet.1,hjet.2.1,hjet.2.2,?_,?_,?_,?_,?_⟩
  · intro w hw
    have ha:AnalyticAt ℂ (centeredExponentialPhase S L) ((x:ℂ),-Complex.I*w/(Real.sqrt h:ℂ)):=
      (hstate (x:ℂ) (hcover x hx) _ (hpoint w (by simpa only[Metric.mem_ball,dist_zero_right] using hw))).1
    exact analyticAt_const.mul (ha.comp
      (f:=fun w:ℂ=>((x:ℂ),-Complex.I*w/(Real.sqrt h:ℂ))) (x:=w) (hmap w))
  · intro w hw
    have hb:‖centeredExponentialPhase S L ((x:ℂ),-Complex.I*w/(Real.sqrt h:ℂ))‖≤
      ‖-Complex.I*w/(Real.sqrt h:ℂ)‖^2:=
      (hstate (x:ℂ) (hcover x hx) _ (hpoint w hw)).2.1
    dsimp only[compactCenteredLogAction]
    rw[norm_mul,Complex.norm_of_nonneg hh.le]
    apply (mul_le_mul_of_nonneg_left hb hh.le).trans_eq
    rw[norm_div,norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_of_nonneg hsqrt.le,div_pow,Real.sq_sqrt hh.le]
    field_simp
  · intro w hw
    have hwr:‖-Complex.I*w/(Real.sqrt h:ℂ)‖<r:=hpoint w
      (by simpa only[Metric.mem_ball,dist_zero_right] using hw)
    have hz:((x:ℂ),-Complex.I*w/(Real.sqrt h:ℂ))∈Ω ×ˢ Metric.ball 0 r:=
      ⟨hcover x hx,by simpa only[Metric.mem_ball,dist_zero_right] using hwr⟩
    exact (hAf 0 _ hz).comp
      (f:=fun w:ℂ=>((x:ℂ),-Complex.I*w/(Real.sqrt h:ℂ))) (x:=w) (hmap w)
  · dsimp only[compactLeadingCenteredAmplitude,compactPremorseAmplitude]
    simp only[mul_zero,zero_div,compactModelPoint_axis]
    rw[(hBc x hxco).2,div_self (by exact_mod_cast (extractionB_pos_interior p x hxco).ne'),one_mul,
      PositiveConvolution.planarInverse_ofReal P x hxco]
    have hy:inverseY x∈Ico (0:ℝ) y₀:=(inverseY_branch x hxco).1
    rw[hf 0 _ ⟨hy.1,hy.2.le⟩]
    simp
  · intro w hw
    exact by simpa only[compactLeadingCenteredAmplitude,pow_zero,Nat.factorial_zero,Nat.cast_one,one_pow,mul_one] using
      (hstate (x:ℂ) (hcover x hx) _ (hpoint w hw)).2.2.2 0
  · intro u hu
    let t:ℝ:=u/Real.sqrt h
    have ht:|t|<rt := by
      dsimp only[t]
      rw[abs_div,abs_of_pos hsqrt]
      exact ((div_lt_iff₀ hsqrt).mpr hu).trans_le hρt
    obtain ⟨htI,hSt⟩:=htrace x hx t ht
    have hLc:L (x:ℂ)=(1/Real.sqrt (WP.euler WP.Psi x):ℝ):=by simpa only[one_div] using hLr
    have hxt:compactRealTilt L x t=x*Real.exp (u/Real.sqrt (h*WP.euler WP.Psi x)) := by
      dsimp only[compactRealTilt,t]
      rw[hLc,Complex.ofReal_re,Real.sqrt_mul hh.le]
      congr 2
      ring
    have he:=compact_centered_leading_real_trace P g p hs S L Bc f x t hxI htI hLc
      hSr.self_of_nhds hSt hν (hBc x hxco).2 (hBc _ ⟨htI.1.le,htI.2⟩).2 (fun Y hY=>hf 0 Y hY)
    rw[hxt] at he htI
    refine ⟨htI,?_⟩
    have huarg: -Complex.I*(t:ℂ)=-Complex.I*(u:ℂ)/(Real.sqrt h:ℂ):=by dsimp only[t];push_cast;ring
    rw[huarg] at he
    change Complex.exp ((complexity g p:ℂ)*centeredExponentialPhase S L ((x:ℂ),-Complex.I*(u:ℂ)/(Real.sqrt h:ℂ)))*
      compactPremorseAmplitude P Bc L f 0 ((x:ℂ),-Complex.I*(u:ℂ)/(Real.sqrt h:ℂ))=_
    rw[he]
    push_cast
    rw[Real.sqrt_mul hh.le,Complex.ofReal_mul]
    congr 2
    dsimp only[t]
    push_cast
    ring
end WP.Analysis
