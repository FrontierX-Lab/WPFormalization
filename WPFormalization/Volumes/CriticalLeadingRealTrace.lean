import WPFormalization.Volumes.CriticalCenteredLog
import WPFormalization.Volumes.CriticalModelTrace
/-! Actual leading-model traces with a real center.
Unlike integer coefficient extraction, a Gaussian local limit uses the real
mean h*Psi(x). The genuine critical log action and leading amplitude equal
the tilted physical markedModel ratio after centering by that real mean.
All action/amplitude restrictions and the uniform positive-distance lens are
supplied by existing proved kernel data; no integer-saddle assumption is used.
The previous natural-number D7 API is kept unchanged. -/
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma CriticalGaussianCoordinateData.centered_exponential_physical_real_center_at
    (d:CriticalGaussianCoordinateData)(δ ε h v μ:ℝ)(k:ℝ)(w:ℝ)
    (hh:0<h)(hv:0<v)(hδ:0<δ)
    (hq:(δ:ℂ)*d.q ((δ:ℂ),-Complex.I*(w:ℂ)/(Real.sqrt h:ℂ))=(ε:ℂ))
    (hphase:((extractionS (XR (y₀-ε))-extractionS (XR (y₀-δ)):ℝ):ℂ)=
      -(5/2:ℂ)*Complex.log ((ε:ℂ)/(δ:ℂ))-d.kernel.logZUnit (ε:ℂ)+d.kernel.logZUnit (δ:ℂ))
    (hμ:d.kernel.psiUnit (δ:ℂ)*d.L (δ:ℂ)=((μ/Real.sqrt v:ℝ):ℂ))
    (hk:(k:ℝ)=h*μ):
    Complex.exp ((h:ℂ)*d.kernel.centeredPhase d.L d.q
      ((δ:ℂ),-Complex.I*(w:ℂ)/(Real.sqrt h:ℂ)))=
      Complex.exp (-(k:ℂ)*(w:ℂ)/(Real.sqrt (h*v):ℂ))*
        ((Real.exp (h*(extractionS (XR (y₀-ε))-extractionS (XR (y₀-δ)))):ℝ):ℂ):=by
  rw[d.kernel.centeredPhase_physical_at d.L d.q δ ε _ hδ hq hphase]
  have hs:(Real.sqrt h:ℂ)≠0:=by exact_mod_cast (Real.sqrt_pos.mpr hh).ne'
  have hvn:(Real.sqrt v:ℂ)≠0:=by exact_mod_cast (Real.sqrt_pos.mpr hv).ne'
  have hlinear:(h:ℂ)*(-(Complex.I*d.kernel.psiUnit (δ:ℂ)*d.L (δ:ℂ)*
      (-Complex.I*(w:ℂ)/(Real.sqrt h:ℂ))))=
        -(k:ℂ)*(w:ℂ)/(Real.sqrt (h*v):ℂ):=by
    have hc:(k:ℂ)=(h:ℂ)*(μ:ℂ):=by exact_mod_cast hk
    rw[Real.sqrt_mul hh.le,Complex.ofReal_mul,hc]
    calc
      _=-(h:ℂ)*(d.kernel.psiUnit (δ:ℂ)*d.L (δ:ℂ))*(w:ℂ)/(Real.sqrt h:ℂ):=by
        have hi:=Complex.I_sq
        field_simp
        linear_combination (h:ℂ)*d.kernel.psiUnit (δ:ℂ)*d.L (δ:ℂ)*(w:ℂ)*hi
      _=_:=by
        rw[hμ,Complex.ofReal_div]
        field_simp
  rw[mul_sub,sub_eq_add_neg,←mul_neg,hlinear,Complex.exp_add]
  rw[←Complex.ofReal_mul,←Complex.ofReal_exp]
  ring

lemma CriticalGaussianCoordinateData.leading_model_physical_real_center_at
    (d:CriticalGaussianCoordinateData)(g p:ℕ)(hs:Stable g p)(Q:ℂ→ℂ)
    (δ ε v μ w:ℝ)(hδ:0<δ)(hε:0<ε)
    (hY:y₀-δ∈Ico (0:ℝ) y₀)(hZ:y₀-ε∈Ico (0:ℝ) y₀)
    (hh:0<(complexity g p:ℝ))(hv:0<v)
    (hq:(δ:ℂ)*d.q ((δ:ℂ),-Complex.I*(w:ℂ)/(Real.sqrt (complexity g p:ℝ):ℂ))=(ε:ℂ))
    (hphase:((extractionS (XR (y₀-ε))-extractionS (XR (y₀-δ)):ℝ):ℂ)=
      -(5/2:ℂ)*Complex.log ((ε:ℂ)/(δ:ℂ))-d.kernel.logZUnit (ε:ℂ)+d.kernel.logZUnit (δ:ℂ))
    (hμ:d.kernel.psiUnit (δ:ℂ)*d.L (δ:ℂ)=((μ/Real.sqrt v:ℝ):ℂ))
    (hphysδ:((Real.rpow (r (y₀-δ)) ((p:ℝ)/2)*Real.sqrt (WP.A (y₀-δ)*Theta (y₀-δ)):ℝ):ℂ)=
      ((Real.rpow δ ((p:ℝ)/2):ℝ):ℂ)*d.kernel.amplitudeUnit Q p (δ:ℂ))
    (hphysε:((Real.rpow (r (y₀-ε)) ((p:ℝ)/2)*Real.sqrt (WP.A (y₀-ε)*Theta (y₀-ε)):ℝ):ℂ)=
      ((Real.rpow ε ((p:ℝ)/2):ℝ):ℂ)*d.kernel.amplitudeUnit Q p (ε:ℂ)):
    Complex.exp (d.centeredLogAction (complexity g p:ℝ) (δ:ℂ) (w:ℂ))*
      d.leadingCenteredAmplitude Q p (complexity g p:ℝ) (δ:ℂ) (w:ℂ)=
      Complex.exp (-(((complexity g p:ℝ)*μ:ℝ):ℂ)*(w:ℂ)/
        (Real.sqrt ((complexity g p:ℝ)*v):ℂ))*
        ((markedModel g p (y₀-ε)/markedModel g p (y₀-δ):ℝ):ℂ):=by
  have hexp:=d.centered_exponential_physical_real_center_at δ ε (complexity g p:ℝ) v μ
    ((complexity g p:ℝ)*μ) w hh hv hδ hq hphase hμ rfl
  have hamp:=d.kernel.jointAmplitude_physical_at Q p d.q δ ε _ hδ hε hq hphysδ hphysε
  have hratio:=markedModel_ratio_phase_amplitude g p hs _ _ hY hZ
  unfold CriticalGaussianCoordinateData.centeredLogAction CriticalGaussianCoordinateData.leadingCenteredAmplitude
  rw[hexp,hamp,hratio]
  push_cast
  ring

lemma CriticalGaussianCoordinateData.leading_model_real_trace
    (d:CriticalGaussianCoordinateData)(P:PsiTheory)(p:ℕ)(Q:ℂ→ℂ)
    (hQphys:∀ᶠδ:ℝ in 𝓝 0,0<δ→Q (δ:ℂ)=(WP.Theta (y₀-δ):ℂ)):
    ∃R:ℝ,0<R ∧ R<y₀ ∧ ∀δ∈Ioo (0:ℝ) R,∀g:ℕ,Stable g p→
      0<(complexity g p:ℝ)→∀w:ℝ,|w|<R*Real.sqrt (complexity g p:ℝ)→
      let x:ℝ:=XR (y₀-δ)*Real.exp (w/Real.sqrt ((complexity g p:ℝ)*euler Psi (XR (y₀-δ))))
      x∈Ioo (0:ℝ) xCritical ∧
      Complex.exp (d.centeredLogAction (complexity g p:ℝ) (δ:ℂ) (w:ℂ))*
        d.leadingCenteredAmplitude Q p (complexity g p:ℝ) (δ:ℂ) (w:ℂ)=
        Complex.exp (-(((complexity g p:ℝ)*Psi (XR (y₀-δ)):ℝ):ℂ)*(w:ℂ)/
          (Real.sqrt ((complexity g p:ℝ)*euler Psi (XR (y₀-δ))):ℂ))*
          ((markedModel g p (inverseY x)/markedModel g p (y₀-δ):ℝ):ℂ):=by
  obtain ⟨Rt,hRt,hRty,htilt⟩:=d.real_tilt_parameters P
  obtain ⟨Ra,hRa,hRay,hamp,hmean,hphase⟩:=d.physical_amplitude_phase_neighborhood Q p hQphys
  let R:ℝ:=min Rt (Ra/4)
  have hR:0<R:=lt_min hRt (div_pos hRa (by norm_num))
  have hRt':R≤Rt:=min_le_left _ _
  have hRa4:R≤Ra/4:=min_le_right _ _
  have hRy:R<y₀:=hRt'.trans_lt hRty
  refine ⟨R,hR,hRy,?_⟩
  intro δ hδ g hs hh w hw
  dsimp only
  let h:ℝ:=complexity g p
  let x:ℝ:=XR (y₀-δ)*Real.exp (w/Real.sqrt (h*euler Psi (XR (y₀-δ))))
  let ε:ℝ:=y₀-inverseY x
  have hδRa:δ∈Ioo (0:ℝ) Ra:=⟨hδ.1,by linarith[hδ.2]⟩
  have htw:=htilt δ ⟨hδ.1,hδ.2.trans_le hRt'⟩ h hh w
    (hw.trans_le (mul_le_mul_of_nonneg_right hRt' (Real.sqrt_nonneg h)))
  dsimp only at htw
  change x∈Ioo (0:ℝ) xCritical ∧δ/2≤ε∧ε≤2*δ∧
    (δ:ℂ)*d.q ((δ:ℂ),-Complex.I*(w:ℂ)/(Real.sqrt h:ℂ))=(ε:ℂ) at htw
  have hε:ε∈Ioo (0:ℝ) Ra:=⟨by linarith[htw.2.1,hδ.1],by linarith[htw.2.2.1,hδ.2]⟩
  have hY:y₀-δ∈Ico (0:ℝ) y₀:=⟨by linarith[hδRa.2],by linarith[hδ.1]⟩
  have hZ:y₀-ε∈Ico (0:ℝ) y₀:=⟨by linarith[hε.2],by linarith[hε.1]⟩
  have hxp:0<XR (y₀-δ):=by
    have ht:=XR_strictMonoOn (show (0:ℝ)∈Iic y₀ from y₀_pos.le)
      (show y₀-δ∈Iic y₀ from hY.2.le) (by linarith[hδRa.2]:0<y₀-δ)
    simpa only[XR_zero] using ht
  have hxc:XR (y₀-δ)<xCritical:=
    XR_strictMonoOn (show y₀-δ∈Iic y₀ from hY.2.le) (show y₀∈Iic y₀ from Set.mem_Iic.mpr le_rfl) hY.2
  have hv:0<euler Psi (XR (y₀-δ)):=
    mul_pos hxp (Psi_deriv_pos_interior _ ⟨hxp.le,hxc⟩)
  have he:=d.leading_model_physical_real_center_at g p hs Q δ ε _ _ w
    hδ.1 hε.1 hY hZ hh hv htw.2.2.2 (hphase δ hδRa ε hε)
    (hmean δ hδRa) (hamp δ hδRa) (hamp ε hε)
  have hz:y₀-ε=inverseY x:=by dsimp only[ε];ring
  rw[hz] at he
  exact ⟨htw.1,he⟩
end WP.Analysis
