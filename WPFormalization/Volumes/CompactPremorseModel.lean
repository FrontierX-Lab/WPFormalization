import WPFormalization.Volumes.CompactPhaseUniform
import WPFormalization.Volumes.ExtractionAmplitude
import WPFormalization.HigherOrder.MarkedExtensionProof
/-! Actual common compact pre-Morse phase and amplitude data. The amplitude is the genuine extractionB ratio times the original marked coefficients at the actual planar inverse. All indices share the same complex disk, Gevrey bounds and true tilted-point domain. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace WP.Analysis
lemma extractionB_pos_interior (p:ℕ) (x:ℝ) (hx:x ∈ Ico (0:ℝ) xCritical):0<extractionB p x := by
  have hY:inverseY x ∈ Ico (0:ℝ) y₀:=(inverseY_branch x hx).1
  have hYc:inverseY x ∈ Icc (0:ℝ) y₀:=⟨hY.1,hY.2.le⟩
  have h0:Ico (0:ℝ) y₀ 0:=⟨le_rfl,y₀_pos⟩
  have h0c:Icc (0:ℝ) y₀ 0:=⟨le_rfl,y₀_pos.le⟩
  dsimp only [extractionB]
  exact div_pos
    (mul_pos (Real.rpow_pos_of_pos (r_pos _ hY) _)
      (Real.sqrt_pos.mpr (mul_pos (marked_A_pos _ hYc) (marked_Theta_pos _ hYc))))
    (mul_pos (Real.rpow_pos_of_pos (r_pos _ h0) _)
      (Real.sqrt_pos.mpr (mul_pos (marked_A_pos _ h0c) (marked_Theta_pos _ h0c))))

def compactModelPoint (L:ℂ → ℂ) (p:ℂ × ℂ):ℂ :=
  p.1*Complex.exp ((Complex.I*L p.1)*p.2)
def compactPremorseAmplitude (P:PsiTheory) (Bc L:ℂ → ℂ) (f:ℕ → ℂ → ℂ) (j:ℕ) (p:ℂ × ℂ):ℂ :=
  Bc (compactModelPoint L p)/Bc p.1*f j (PositiveConvolution.planarInverse P (compactModelPoint L p))
lemma compactModelPoint_analyticAt (L:ℂ → ℂ) (x:ℂ) (hL:AnalyticAt ℂ L x):
    AnalyticAt ℂ (compactModelPoint L) (x,0) := by
  have hLc:AnalyticAt ℂ (fun p:ℂ × ℂ=>L p.1) (x,0):=hL.comp (f:=fun p:ℂ × ℂ=>p.1) analyticAt_fst
  exact analyticAt_fst.mul (((analyticAt_const.mul hLc).mul analyticAt_snd).cexp)
lemma compactModelPoint_axis (L:ℂ → ℂ) (x:ℂ):compactModelPoint L (x,0)=x := by simp [compactModelPoint]

lemma actual_compact_premorse_amplitude_family (P:PsiTheory) (p:ℕ) (hp:1 ≤ p)
    (a b:ℝ) (ha:0<a) (hab:a ≤ b) (hbc:b<xCritical) (L:ℂ → ℂ)
    (hL:∀x ∈ Icc a b,AnalyticAt ℂ L (x:ℂ)) :
    ∃(Bc:ℂ → ℂ)(f:ℕ → ℂ → ℂ)(U:Set ℂ)(r C B:ℝ),
      (∀x ∈ Ico (0:ℝ) xCritical,AnalyticAt ℂ Bc (x:ℂ) ∧ Bc (x:ℂ)=(extractionB p x:ℂ)) ∧
      (∀j Y,Y ∈ Icc (0:ℝ) y₀ → f j (Y:ℂ)=(HigherOrder.markedCoefficient P p j Y:ℂ)) ∧
      IsOpen U ∧ (∀x ∈ Icc a b,(x:ℂ) ∈ U) ∧ 0<r ∧ 0<C ∧ 0<B ∧
      (∀j,AnalyticOnNhd ℂ (compactPremorseAmplitude P Bc L f j) (U ×ˢ Metric.ball 0 r)) ∧
      ∀x ∈ U,∀u:ℂ,‖u‖<r → ‖compactModelPoint L (x,u)‖<xCritical ∧
        ∀j,‖compactPremorseAmplitude P Bc L f j (x,u)‖ ≤ C*B^j*(j.factorial:ℝ)^2 := by
  obtain ⟨Bc,hBc0,hBc⟩:=extractionB_complex_extension P p
  obtain ⟨C₀,B,hC₀,hB,Ωf,ac,f,hΩf,hcover,hf,hrest,hbound⟩:=
    HigherOrder.markedCoefficient_common_complex_gevrey_two P p hp
  let K:Set ℂ:=(fun x:ℝ=>(x:ℂ)) '' Icc a b
  have hK:IsCompact K:=isCompact_Icc.image Complex.continuous_ofReal
  let A:ℂ × ℂ → ℂ:=fun z=>Bc (compactModelPoint L z)/Bc z.1
  let Y:ℂ × ℂ → ℂ:=fun z=>PositiveConvolution.planarInverse P (compactModelPoint L z)
  have hpoint(x:ℝ)(hx:x ∈ Icc a b):x ∈ Ico (0:ℝ) xCritical:=⟨(ha.trans_le hx.1).le,hx.2.trans_lt hbc⟩
  have hAn(x:ℂ)(hx:x ∈ K):AnalyticAt ℂ A (x,0) ∧ A (x,0)=1 := by
    rcases hx with ⟨t,ht,rfl⟩
    have htI:=hpoint t ht
    have hBct:AnalyticAt ℂ Bc (t:ℂ):=(hBc t htI).1
    have hBcn:Bc (t:ℂ)≠0:=by rw[(hBc t htI).2];exact_mod_cast (extractionB_pos_interior p t htI).ne'
    have harg:=compactModelPoint_analyticAt L (t:ℂ) (hL t ht)
    constructor
    · exact (hBct.comp_of_eq harg (compactModelPoint_axis L (t:ℂ))).div
        (hBct.comp (f:=fun z:ℂ × ℂ=>z.1) analyticAt_fst) hBcn
    · dsimp only[A]
      rw[compactModelPoint_axis,div_self hBcn]
  have hYn(x:ℂ)(hx:x ∈ K):AnalyticAt ℂ Y (x,0) ∧ Y (x,0) ∈ Ωf := by
    rcases hx with ⟨t,ht,rfl⟩
    have htI:=hpoint t ht
    have htN:‖(t:ℂ)‖<xCritical:=by rw[Complex.norm_of_nonneg htI.1];exact htI.2
    have harg:=compactModelPoint_analyticAt L (t:ℂ) (hL t ht)
    constructor
    · exact (PositiveConvolution.planarInverse_analyticAt P (t:ℂ) htN).comp_of_eq harg
        (compactModelPoint_axis L (t:ℂ))
    · dsimp only[Y]
      rw[compactModelPoint_axis,PositiveConvolution.planarInverse_ofReal P t htI]
      have hy:inverseY t ∈ Ico (0:ℝ) y₀:=(inverseY_branch t htI).1
      exact hcover _ ⟨hy.1,hy.2.le⟩
  have hfb:∀j z,z ∈ Ωf → ‖f j z‖ ≤ C₀*B^j*(j.factorial:ℝ)^2 := by
    intro j z hz
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans (hbound j z hz)
  obtain ⟨U,hU,hKU,r,hr,hAf,hAb⟩:=compact_axis_composition_gevrey_two_family K hK A Y Ωf hΩf f C₀ B
    hC₀.le hB.le (fun x hx=>(hAn x hx).1) (fun x hx=>(hYn x hx).1)
    (fun x hx=>(hAn x hx).2) (fun x hx=>(hYn x hx).2) (fun j=>(hf j).2) hfb
  have hdisk:∀x ∈ K,∀ᶠz:ℂ × ℂ in 𝓝 (x,0),‖compactModelPoint L z‖<xCritical := by
    rintro x ⟨t,ht,rfl⟩
    have htI:=hpoint t ht
    have hn:‖compactModelPoint L ((t:ℂ),0)‖<xCritical := by
      rw[compactModelPoint_axis,Complex.norm_of_nonneg htI.1];exact htI.2
    exact (compactModelPoint_analyticAt L (t:ℂ) (hL t ht)).continuousAt.norm.tendsto.eventually
      (eventually_lt_nhds hn)
  obtain ⟨V,hV,hKV,s,hs,hdisks⟩:=compact_axis_uniform_neighborhood K hK
    (fun z=>‖compactModelPoint L z‖<xCritical) hdisk
  refine ⟨Bc,f,U∩V,min r s,2*C₀,B,hBc,(fun j Y hY=>(hrest j Y hY).2),
    hU.inter hV,(fun x hx=>⟨hKU ⟨x,hx,rfl⟩,hKV ⟨x,hx,rfl⟩⟩),lt_min hr hs,
    by positivity,hB,?_,?_⟩
  · intro j z hz
    exact hAf j z ⟨hz.1.1,Metric.mem_ball.mpr (by
      have hu:‖z.2‖< min r s:=by simpa only[Metric.mem_ball,dist_zero_right] using hz.2
      simpa only[dist_zero_right] using hu.trans_le (min_le_left _ _))⟩
  · intro x hx u hu
    exact ⟨hdisks x hx.2 u (hu.trans_le (min_le_right _ _)),
      fun j=>hAb j x hx.1 u (hu.trans_le (min_le_left _ _))⟩
lemma actual_compact_model_uniform_data (P:PsiTheory) (p:ℕ) (hp:1 ≤ p)
    (a b:ℝ) (ha:0<a) (hab:a ≤ b) (hbc:b<xCritical) :
    ∃(S L Bc:ℂ → ℂ)(f:ℕ → ℂ → ℂ)(Ω:Set ℂ)(r C B:ℝ),IsOpen Ω ∧
      (∀x ∈ Icc a b,(x:ℂ) ∈ Ω) ∧ 0<r ∧ 0<C ∧ 0<B ∧
      (∀x ∈ Icc a b,AnalyticAt ℂ S (x:ℂ) ∧ AnalyticAt ℂ L (x:ℂ) ∧
        (∀ᶠt:ℝ in 𝓝 x,S (t:ℂ)=(extractionS t:ℂ)) ∧
        complexEuler S (x:ℂ)=(WP.Psi x:ℂ) ∧
        ((complexEuler^[2]) S) (x:ℂ)=(WP.euler WP.Psi x:ℂ) ∧
        L (x:ℂ)=((Real.sqrt (WP.euler WP.Psi x))⁻¹:ℝ) ∧
        ∀ᶠq:ℂ in 𝓝 (x:ℂ),(L q)^2*((complexEuler^[2]) S) q=1) ∧
      (∀x ∈ Ico (0:ℝ) xCritical,AnalyticAt ℂ Bc (x:ℂ) ∧ Bc (x:ℂ)=(extractionB p x:ℂ)) ∧
      (∀j Y,Y ∈ Icc (0:ℝ) y₀ → f j (Y:ℂ)=(HigherOrder.markedCoefficient P p j Y:ℂ)) ∧
      (∀j,AnalyticOnNhd ℂ (compactPremorseAmplitude P Bc L f j) (Ω ×ˢ Metric.ball 0 r)) ∧
      ∀x ∈ Ω,∀u:ℂ,‖u‖<r → AnalyticAt ℂ (centeredExponentialPhase S L) (x,u) ∧
        ‖centeredExponentialPhase S L (x,u)‖ ≤ ‖u‖^2 ∧
        ‖compactModelPoint L (x,u)‖<xCritical ∧
        ∀j,‖compactPremorseAmplitude P Bc L f j (x,u)‖ ≤ C*B^j*(j.factorial:ℝ)^2 := by
  obtain ⟨S,L,U,rU,hU,hcoverU,hposU,hData,hPhase⟩:=actual_compact_phase_uniform_bound a b ha hab hbc
  obtain ⟨Bc,f,V,rV,C,B,hBc,hf,hV,hcoverV,hrV,hC,hB,hAf,hAb⟩:=
    actual_compact_premorse_amplitude_family P p hp a b ha hab hbc L (fun x hx=>(hData x hx).2.1)
  refine ⟨S,L,Bc,f,U∩V,min rU rV,C,B,hU.inter hV,
    (fun x hx=>⟨hcoverU x hx,hcoverV x hx⟩),lt_min hposU hrV,hC,hB,hData,hBc,hf,?_,?_⟩
  · intro j z hz
    apply hAf j z
    refine ⟨hz.1.2,?_⟩
    rw[Metric.mem_ball,dist_zero_right]
    have hz2:‖z.2‖< min rU rV:=by simpa only[Metric.mem_ball,dist_zero_right] using hz.2
    exact hz2.trans_le (min_le_right _ _)
  · intro x hx u hu
    have h1:=hPhase x hx.1 u (hu.trans_le (min_le_left _ _))
    have h2:=hAb x hx.2 u (hu.trans_le (min_le_right _ _))
    exact ⟨h1.1,h1.2,h2.1,h2.2⟩
end WP.Analysis
