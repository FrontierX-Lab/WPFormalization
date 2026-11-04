import WPFormalization.Volumes.CompactPremorseModel
import WPFormalization.Volumes.CriticalModelTrace
/-! Compact physical real tilts and the genuine J0 centered marked-model trace. The radius comes from actual action germs uniformly on the compact interval. The exact trace holds for arbitrary real t and uses no integer saddle condition. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace WP.Analysis
def compactRealTiltExtension (L:ℂ→ℂ) (z:ℂ × ℂ):ℝ:=
  z.1.re*Real.exp (z.2.re*(L z.1).re)
def compactRealTilt (L:ℂ→ℂ) (x t:ℝ):ℝ:=x*Real.exp (t*(L (x:ℂ)).re)
lemma compact_real_trace_uniform (a b:ℝ) (ha:0<a) (hab:a≤b) (hbc:b<xCritical)
    (S L:ℂ→ℂ) (hL:∀x∈Icc a b,AnalyticAt ℂ L (x:ℂ))
    (hSr:∀x∈Icc a b,(fun t:ℝ=>S (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(extractionS t:ℂ))) :
    ∃ρ:ℝ,0<ρ ∧∀x∈Icc a b,∀t:ℝ,|t|<ρ→compactRealTilt L x t∈Ioo (0:ℝ) xCritical ∧
      S (compactRealTilt L x t:ℂ)=(extractionS (compactRealTilt L x t):ℂ) := by
  let K:Set ℂ:=(fun x:ℝ=>(x:ℂ)) '' Icc a b
  have hK:IsCompact K:=isCompact_Icc.image Complex.continuous_ofReal
  let Q:ℂ × ℂ→Prop:=fun z=>compactRealTiltExtension L z∈Ioo (0:ℝ) xCritical ∧
    S (compactRealTiltExtension L z:ℂ)=(extractionS (compactRealTiltExtension L z):ℂ)
  have hQ:∀x∈K,∀ᶠz:ℂ × ℂ in 𝓝 (x,0),Q z := by
    rintro x ⟨v,hv,rfl⟩
    have hp:ContinuousAt (fun z:ℂ × ℂ=>z.1) ((v:ℂ),0):=continuous_fst.continuousAt
    have hLc:ContinuousAt (fun z:ℂ × ℂ=>L z.1) ((v:ℂ),0):=
      ContinuousAt.comp (f:=fun z:ℂ × ℂ=>z.1) (g:=L) (x:=((v:ℂ),0)) (hL v hv).continuousAt hp
    have hc:ContinuousAt (compactRealTiltExtension L) ((v:ℂ),0) := by
      change ContinuousAt (fun z:ℂ × ℂ=>z.1.re*Real.exp (z.2.re*(L z.1).re)) ((v:ℂ),0)
      fun_prop
    have ht:Tendsto (compactRealTiltExtension L) (𝓝 ((v:ℂ),0)) (𝓝 v) := by
      simpa only[compactRealTiltExtension,Complex.ofReal_re,Complex.zero_re,zero_mul,Real.exp_zero,mul_one]
        using hc.tendsto
    have hnear:∀ᶠt:ℝ in 𝓝 v,t∈Ioo (0:ℝ) xCritical ∧ S (t:ℂ)=(extractionS t:ℂ) := by
      filter_upwards[isOpen_Ioo.mem_nhds (show v∈Ioo (0:ℝ) xCritical from
        ⟨ha.trans_le hv.1,hv.2.trans_lt hbc⟩),hSr v hv] with t ht he
      exact ⟨ht,he⟩
    exact ht.eventually hnear
  obtain ⟨U,hU,hKU,ρ,hρ,hprop⟩:=compact_axis_uniform_neighborhood K hK Q hQ
  refine ⟨ρ,hρ,?_⟩
  intro x hx t ht
  have hp:=hprop (x:ℂ) (hKU ⟨x,hx,rfl⟩) (t:ℂ) (by simpa only[Complex.norm_real,Real.norm_eq_abs] using ht)
  simpa only[Q,compactRealTiltExtension,Complex.ofReal_re,compactRealTilt] using hp
lemma markedModel_ratio_extractionB (g p:ℕ) (hs:Stable g p) (x z:ℝ)
    (hx:x∈Ico (0:ℝ) xCritical) (hz:z∈Ico (0:ℝ) xCritical) :
    markedModel g p (inverseY z)/markedModel g p (inverseY x)=
      Real.exp ((complexity g p:ℝ)*(extractionS z-extractionS x))*extractionB p z/extractionB p x := by
  obtain ⟨hY,hXY⟩:=inverseY_branch x hx
  obtain ⟨hZ,hXZ⟩:=inverseY_branch z hz
  have hm0:markedModel g p 0≠0:=(markedModel_pos_parameter g p hs 0 ⟨le_rfl,y₀_pos⟩).ne'
  have hb:extractionB p x≠0:=(extractionB_pos_interior p x hx).ne'
  rw[extraction_factorization_proof g p (inverseY x) hY,
    extraction_factorization_proof g p (inverseY z) hZ,hXY,hXZ,mul_sub,Real.exp_sub]
  field_simp [hm0,hb,Real.exp_ne_zero]

lemma compact_centered_leading_real_trace (P:PsiTheory) (g p:ℕ) (hs:Stable g p)
    (S L Bc:ℂ→ℂ) (f:ℕ→ℂ→ℂ) (x t:ℝ)
    (hx:x∈Ioo (0:ℝ) xCritical)
    (hz:compactRealTilt L x t∈Ioo (0:ℝ) xCritical)
    (hL:L (x:ℂ)=(1/Real.sqrt (WP.euler WP.Psi x):ℝ))
    (hSx:S (x:ℂ)=(extractionS x:ℂ))
    (hSz:S (compactRealTilt L x t:ℂ)=(extractionS (compactRealTilt L x t):ℂ))
    (hν:complexEuler S (x:ℂ)=(WP.Psi x:ℂ))
    (hBx:Bc (x:ℂ)=(extractionB p x:ℂ))
    (hBz:Bc (compactRealTilt L x t:ℂ)=(extractionB p (compactRealTilt L x t):ℂ))
    (hf:∀Y∈Icc (0:ℝ) y₀,f 0 (Y:ℂ)=(HigherOrder.markedCoefficient P p 0 Y:ℂ)) :
    Complex.exp ((complexity g p:ℂ)*centeredExponentialPhase S L ((x:ℂ),-Complex.I*(t:ℂ)))*
      compactPremorseAmplitude P Bc L f 0 ((x:ℂ),-Complex.I*(t:ℂ))=
      ((Real.exp (-(complexity g p:ℝ)*WP.Psi x*t/Real.sqrt (WP.euler WP.Psi x))*
        (markedModel g p (inverseY (compactRealTilt L x t))/markedModel g p (inverseY x)):ℝ):ℂ) := by
  let z:ℝ:=compactRealTilt L x t
  change Bc (z:ℂ)=(extractionB p z:ℂ) at hBz
  have hpoint:compactModelPoint L ((x:ℂ),-Complex.I*(t:ℂ))=(z:ℂ) := by
    dsimp only[compactModelPoint,z,compactRealTilt]
    rw[hL]
    simp only[Complex.ofReal_re]
    have he:(Complex.I*(1/(Real.sqrt (WP.euler WP.Psi x):ℂ)))*(-Complex.I*(t:ℂ))=
        ((t*(1/Real.sqrt (WP.euler WP.Psi x)):ℝ):ℂ) := by push_cast;rw[←mul_assoc];ring_nf;simp
    rw[Complex.ofReal_div,Complex.ofReal_one,he,←Complex.ofReal_exp,←Complex.ofReal_mul]
  have hzI:z∈Ico (0:ℝ) xCritical:=⟨hz.1.le,hz.2⟩
  have hY:inverseY z∈Ico (0:ℝ) y₀:=(inverseY_branch z hzI).1
  have hpn:‖(z:ℂ)‖<xCritical:=by rw[Complex.norm_of_nonneg hz.1.le];exact hz.2
  have hfp:f 0 (PositiveConvolution.planarInverse P (z:ℂ))=1 := by
    rw[PositiveConvolution.planarInverse_ofReal P z hzI,hf _ ⟨hY.1,hY.2.le⟩]
    simp
  have hphase:centeredExponentialPhase S L ((x:ℂ),-Complex.I*(t:ℂ))=
      ((extractionS z-extractionS x-WP.Psi x*t/Real.sqrt (WP.euler WP.Psi x):ℝ):ℂ) := by
    unfold centeredExponentialPhase centeredExponentialSlice
    change S (compactModelPoint L ((x:ℂ),-Complex.I*(t:ℂ)))-S (x:ℂ)-
      (Complex.I*L (x:ℂ))*(-Complex.I*(t:ℂ))*complexEuler S (x:ℂ)=_
    rw[hpoint,hSx,hSz,hL,hν]
    push_cast
    have hi:=Complex.I_sq
    ring_nf
    simp[Complex.I_sq]
    <;> ring
  have hratio:=markedModel_ratio_extractionB g p hs x z ⟨hx.1.le,hx.2⟩ hzI
  unfold compactPremorseAmplitude
  change Complex.exp ((complexity g p:ℂ)*centeredExponentialPhase S L ((x:ℂ),-Complex.I*(t:ℂ)))*
    (Bc (compactModelPoint L ((x:ℂ),-Complex.I*(t:ℂ)))/Bc (x:ℂ)*
      f 0 (PositiveConvolution.planarInverse P (compactModelPoint L ((x:ℂ),-Complex.I*(t:ℂ)))))=_
  rw[hpoint,hBz,hBx,hfp,mul_one,hphase,hratio]
  push_cast
  rw[show (complexity g p:ℂ)*(↑(extractionS z)-↑(extractionS x)-↑(WP.Psi x)*↑t/↑(Real.sqrt (WP.euler WP.Psi x)))=
    -(complexity g p:ℂ)*↑(WP.Psi x)*↑t/↑(Real.sqrt (WP.euler WP.Psi x))+
      (complexity g p:ℂ)*(↑(extractionS z)-↑(extractionS x)) by ring,Complex.exp_add]
  ring

end WP.Analysis
