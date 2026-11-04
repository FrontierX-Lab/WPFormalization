import WPFormalization.Volumes.CriticalModelGrowth
import WPFormalization.Volumes.CriticalExtractionPhysical
import WPFormalization.Volumes.OriginFiniteModel
/-! Physical real traces of the actual centered finite marked model.
Exact marked-model factorization, the true extractionS log-action identity,
and physical r/A/Theta amplitudes give the real tilted model ratio. All
physical germ radii are made uniform using the genuine inverse lens and
comparability of the two positive critical distances. The supplied canonical
coefficient real trace and Theta-unit data are proved upstream data, not a
new asymptotic/model-comparison hypothesis. No continuation of totalized
physical r through the critical endpoint is claimed. -/
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma markedModel_ratio_phase_amplitude (g p:ℕ)(hs:Stable g p)(Y Z:ℝ)
    (hY:Y∈Ico (0:ℝ) y₀)(hZ:Z∈Ico (0:ℝ) y₀):
    markedModel g p Z/markedModel g p Y=
      Real.exp ((complexity g p:ℝ)*(extractionS (XR Z)-extractionS (XR Y)))*
        (Real.rpow (r Z) ((p:ℝ)/2)*Real.sqrt (WP.A Z*Theta Z))/
          (Real.rpow (r Y) ((p:ℝ)/2)*Real.sqrt (WP.A Y*Theta Y)):=by
  have h0:(0:ℝ)∈Ico (0:ℝ) y₀:=⟨le_rfl,y₀_pos⟩
  have hM0:markedModel g p 0≠0:=(markedModel_pos_parameter g p hs 0 h0).ne'
  have ha0:Real.rpow (r 0) ((p:ℝ)/2)*Real.sqrt (WP.A 0*Theta 0)≠0:=
    (marked_amplitude_pos p 0 h0).ne'
  have haY:Real.rpow (r Y) ((p:ℝ)/2)*Real.sqrt (WP.A Y*Theta Y)≠0:=
    (marked_amplitude_pos p Y hY).ne'
  have hinvY:inverseY (XR Y)=Y:=inverseY_eq_of_root _ _ hY.2.le rfl
  have hinvZ:inverseY (XR Z)=Z:=inverseY_eq_of_root _ _ hZ.2.le rfl
  obtain ⟨hr0,hs0⟩:=mul_ne_zero_iff.mp ha0
  obtain ⟨hrY,hsY⟩:=mul_ne_zero_iff.mp haY
  rw[extraction_factorization_proof g p Y hY,extraction_factorization_proof g p Z hZ,
    extractionB,extractionB,hinvY,hinvZ,mul_sub,Real.exp_sub]
  field_simp [hM0,hr0,hs0,hrY,hsY]
end WP.Analysis

namespace WP.Analysis
open Set Filter
open scoped Topology
lemma CriticalGaussianCoordinateData.centered_exponential_physical_at
    (d:CriticalGaussianCoordinateData)(δ ε h v μ:ℝ)(k:ℕ)(w:ℝ)
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
end WP.Analysis

namespace WP.Analysis
open Set Filter
open scoped Topology
lemma CriticalGaussianCoordinateData.centeredFiniteMarkedModel_physical_at
    (d:CriticalGaussianCoordinateData)(P:PsiTheory)(g p k J:ℕ)(hs:Stable g p)
    (Q:ℂ→ℂ)(L:ℕ→ℂ→ℂ)(δ ε v μ w:ℝ)
    (hδ:0<δ)(hε:0<ε)(hY:y₀-δ∈Ico (0:ℝ) y₀)(hZ:y₀-ε∈Ico (0:ℝ) y₀)
    (hh:0<(complexity g p:ℝ))(hv:0<v)
    (hq:(δ:ℂ)*d.q ((δ:ℂ),-Complex.I*(w:ℂ)/(Real.sqrt (complexity g p:ℝ):ℂ))=(ε:ℂ))
    (hphase:((extractionS (XR (y₀-ε))-extractionS (XR (y₀-δ)):ℝ):ℂ)=
      -(5/2:ℂ)*Complex.log ((ε:ℂ)/(δ:ℂ))-d.kernel.logZUnit (ε:ℂ)+d.kernel.logZUnit (δ:ℂ))
    (hμ:d.kernel.psiUnit (δ:ℂ)*d.L (δ:ℂ)=((μ/Real.sqrt v:ℝ):ℂ))
    (hk:(k:ℝ)=(complexity g p:ℝ)*μ)
    (hphysδ:((Real.rpow (r (y₀-δ)) ((p:ℝ)/2)*Real.sqrt (WP.A (y₀-δ)*Theta (y₀-δ)):ℝ):ℂ)=
      ((Real.rpow δ ((p:ℝ)/2):ℝ):ℂ)*d.kernel.amplitudeUnit Q p (δ:ℂ))
    (hphysε:((Real.rpow (r (y₀-ε)) ((p:ℝ)/2)*Real.sqrt (WP.A (y₀-ε)*Theta (y₀-ε)):ℝ):ℂ)=
      ((Real.rpow ε ((p:ℝ)/2):ℝ):ℂ)*d.kernel.amplitudeUnit Q p (ε:ℂ))
    (hL:∀Y∈Icc (0:ℝ) y₀,∀j,L j (Y:ℂ)=(HigherOrder.markedCoefficient P p j Y:ℂ)):
    d.centeredFiniteMarkedModel Q p L (complexity g p:ℝ) J (δ:ℂ) (w:ℂ)=
      Complex.exp (-(k:ℂ)*(w:ℂ)/(Real.sqrt ((complexity g p:ℝ)*v):ℂ))*
        ((markedModel g p (y₀-ε)/markedModel g p (y₀-δ)*
          HigherOrder.realFiniteMarkedFactor P p (complexity g p:ℝ) J (y₀-ε)/
          HigherOrder.realFiniteMarkedFactor P p (complexity g p:ℝ) J (y₀-δ):ℝ):ℂ):=by
  let h:ℝ:=complexity g p
  let u:ℂ:=-Complex.I*(w:ℂ)/(Real.sqrt h:ℂ)
  have hphaseExp:=d.centered_exponential_physical_at δ ε h v μ k w hh hv hδ hq hphase hμ hk
  have hamp:=d.kernel.jointAmplitude_physical_at Q p d.q δ ε u hδ hε hq hphysδ hphysε
  have hfinite(Y:ℝ)(hYi:Y∈Ico (0:ℝ) y₀):
      HigherOrder.finiteMarkedFactor L h J (Y:ℂ)=
        (HigherOrder.realFiniteMarkedFactor P p h J Y:ℂ):=by
    unfold HigherOrder.finiteMarkedFactor HigherOrder.realFiniteMarkedFactor
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    rw[hL Y ⟨hYi.1,hYi.2.le⟩ j]
  have hsum:(∑j∈Finset.range (J+1),d.preMorseAmplitude Q p L j ((δ:ℂ),u)/(h:ℂ)^j)=
      d.kernel.jointAmplitude Q p d.q ((δ:ℂ),u)*HigherOrder.finiteMarkedFactor L h J ((y₀:ℂ)-(ε:ℂ)):=by
    unfold CriticalGaussianCoordinateData.preMorseAmplitude HigherOrder.finiteMarkedFactor
    dsimp only
    rw[hq,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hratio:=markedModel_ratio_phase_amplitude g p hs _ _ hY hZ
  unfold CriticalGaussianCoordinateData.centeredFiniteMarkedModel
  change Complex.exp ((h:ℂ)*d.kernel.centeredPhase d.L d.q ((δ:ℂ),u))*
    (∑j∈Finset.range (J+1),d.preMorseAmplitude Q p L j ((δ:ℂ),u)/(h:ℂ)^j)/
    HigherOrder.finiteMarkedFactor L h J ((y₀:ℂ)-(δ:ℂ))=_
  rw[hsum,hphaseExp,hamp,←Complex.ofReal_sub,←Complex.ofReal_sub,hfinite _ hY,hfinite _ hZ]
  rw[hratio]
  push_cast
  dsimp only[h]
  push_cast
  simp only[mul_comm,mul_left_comm,mul_assoc]
  ring
end WP.Analysis
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma CriticalGaussianCoordinateData.physical_amplitude_phase_neighborhood
    (d:CriticalGaussianCoordinateData)(Q:ℂ→ℂ)(p:ℕ)
    (hQphys:∀ᶠδ:ℝ in 𝓝 0,0<δ→Q (δ:ℂ)=(WP.Theta (y₀-δ):ℂ)):
    ∃R:ℝ,0<R ∧ R<y₀ ∧
      (∀δ∈Ioo (0:ℝ) R,
        ((Real.rpow (r (y₀-δ)) ((p:ℝ)/2)*Real.sqrt (WP.A (y₀-δ)*Theta (y₀-δ)):ℝ):ℂ)=
          ((Real.rpow δ ((p:ℝ)/2):ℝ):ℂ)*d.kernel.amplitudeUnit Q p (δ:ℂ)) ∧
      (∀δ∈Ioo (0:ℝ) R,
        d.kernel.psiUnit (δ:ℂ)*d.L (δ:ℂ)=
          ((Psi (XR (y₀-δ))/Real.sqrt (euler Psi (XR (y₀-δ))):ℝ):ℂ)) ∧
      (∀δ∈Ioo (0:ℝ) R,∀ε∈Ioo (0:ℝ) R,
        ((extractionS (XR (y₀-ε))-extractionS (XR (y₀-δ)):ℝ):ℂ)=
          -(5/2:ℂ)*Complex.log ((ε:ℂ)/(δ:ℂ))-d.kernel.logZUnit (ε:ℂ)+d.kernel.logZUnit (δ:ℂ)):=by
  obtain ⟨Ra,hRa,hamp⟩:=Metric.eventually_nhds_iff.mp (d.kernel.amplitudeUnit_physical Q hQphys p)
  obtain ⟨Rp,hRp,hphase⟩:=Metric.eventually_nhds_iff.mp d.kernel.extractionS_difference_physical
  obtain ⟨Rn,hRn,hnorm⟩:=Metric.eventually_nhds_iff.mp d.physical_normalization
  let R:ℝ:=min (y₀/2) (min Ra (min Rp Rn))
  have hR:0<R:=lt_min (div_pos y₀_pos (by norm_num)) (lt_min hRa (lt_min hRp hRn))
  have hRy:R<y₀:=(min_le_left _ _).trans_lt (by linarith[y₀_pos])
  have hRRa:R≤Ra:=(min_le_right _ _).trans (min_le_left _ _)
  have hRRp:R≤Rp:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRRn:R≤Rn:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨R,hR,hRy,?_,?_,?_⟩
  · intro δ hδ
    exact hamp (by rw[Real.dist_eq,sub_zero,abs_of_pos hδ.1];exact hδ.2.trans_le hRRa) hδ.1
  · intro δ hδ
    exact (hnorm (by rw[Real.dist_eq,sub_zero,abs_of_pos hδ.1];exact hδ.2.trans_le hRRn) hδ.1).2
  · intro δ hδ ε hε
    have hpdist:dist ((δ,ε):ℝ × ℝ) (0,0)<Rp:=by
      simpa only[dist_eq_norm,Prod.mk_sub_mk,sub_zero,Prod.norm_def,max_lt_iff,Real.norm_eq_abs,
        abs_of_pos hδ.1,abs_of_pos hε.1] using
          And.intro (hδ.2.trans_le hRRp) (hε.2.trans_le hRRp)
    exact hphase (y:=(δ,ε)) hpdist hδ.1 hε.1
end WP.Analysis
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma CriticalGaussianCoordinateData.centered_finite_model_real_trace
    (d:CriticalGaussianCoordinateData)(P:PsiTheory)(p:ℕ)(Q:ℂ→ℂ)(L:ℕ→ℂ→ℂ)
    (hQphys:∀ᶠδ:ℝ in 𝓝 0,0<δ→Q (δ:ℂ)=(WP.Theta (y₀-δ):ℂ))
    (hL:∀Y∈Icc (0:ℝ) y₀,∀j,L j (Y:ℂ)=(HigherOrder.markedCoefficient P p j Y:ℂ)):
    ∃R:ℝ,0<R ∧ R<y₀ ∧ ∀δ∈Ioo (0:ℝ) R,∀g k J:ℕ,Stable g p→
      0<(complexity g p:ℝ)→(k:ℝ)=(complexity g p:ℝ)*Psi (XR (y₀-δ))→
      ∀w:ℝ,|w|<R*Real.sqrt (complexity g p:ℝ)→
      let x:ℝ:=XR (y₀-δ)*Real.exp (w/Real.sqrt ((complexity g p:ℝ)*euler Psi (XR (y₀-δ))))
      x∈Ioo (0:ℝ) xCritical ∧
      d.centeredFiniteMarkedModel Q p L (complexity g p:ℝ) J (δ:ℂ) (w:ℂ)=
        Complex.exp (-(k:ℂ)*(w:ℂ)/(Real.sqrt ((complexity g p:ℝ)*euler Psi (XR (y₀-δ))):ℂ))*
          ((markedModel g p (inverseY x)/markedModel g p (y₀-δ)*
            HigherOrder.realFiniteMarkedFactor P p (complexity g p:ℝ) J (inverseY x)/
            HigherOrder.realFiniteMarkedFactor P p (complexity g p:ℝ) J (y₀-δ):ℝ):ℂ):=by
  obtain ⟨Rt,hRt,hRty,htilt⟩:=d.real_tilt_parameters P
  obtain ⟨Ra,hRa,hRay,hamp,hmean,hphase⟩:=d.physical_amplitude_phase_neighborhood Q p hQphys
  let R:ℝ:=min Rt (Ra/4)
  have hR:0<R:=lt_min hRt (div_pos hRa (by norm_num))
  have hRt':R≤Rt:=min_le_left _ _
  have hRa4:R≤Ra/4:=min_le_right _ _
  have hRy:R<y₀:=hRt'.trans_lt hRty
  refine ⟨R,hR,hRy,?_⟩
  intro δ hδ g k J hs hh hk w hw
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
  have he:=d.centeredFiniteMarkedModel_physical_at P g p k J hs Q L δ ε _ _ w
    hδ.1 hε.1 hY hZ hh hv htw.2.2.2 (hphase δ hδRa ε hε)
    (hmean δ hδRa) hk (hamp δ hδRa) (hamp ε hε) hL
  have hz:y₀-ε=inverseY x:=by dsimp only[ε];ring
  rw[hz] at he
  exact ⟨htw.1,he⟩
end WP.Analysis
