import WPFormalization.HigherOrder.CriticalTransport
import WPFormalization.Statements.CoefficientBounds
import WPFormalization.Analysis.TransportGammaFamily
/-! Actual all-order inverse-cusp coefficients on a common complex domain.
C.4 proves their holomorphy. Given the explicitly stated actual C.3 remainder
upstream, critical coefficient uniqueness proves their vanishing, and one
root-unit neighborhood removes every quotient by A*r simultaneously. The
physical root is identified only below criticality; no value of raw r(y0)
is substituted for the continued branch. No uniform quotient norm bound is
claimed by this analytic extension theorem alone. -/
set_option maxHeartbeats 800000
noncomputable section
namespace WP.HigherOrder.ComplexCanonical
open Set Filter PowerSeries
open scoped Topology

def transportCoefficient (P:PsiTheory)(R:ℂ→ℂ)(p j:ℕ)(z:ℂ):ℂ:=
  PowerSeries.coeff (j+1) ((formalCusp P R z p)⁻¹)

lemma transportCoefficient_analyticOnNhd (Ω:Set ℂ)(P:PsiTheory)(R:ℂ→ℂ)(p j:ℕ)
    (hC:∀n:ℕ,AnalyticOnNhd ℂ (fun z=>cuspCoefficient P R z p n) Ω):
    AnalyticOnNhd ℂ (transportCoefficient P R p j) Ω:=by
  have hF:AnalyticCoefficients Ω (j+1) (fun z=>formalCusp P R z p):=by
    intro n hn
    simpa only[formalCusp,PowerSeries.coeff_mk] using hC n
  have h0:∀z∈Ω,PowerSeries.constantCoeff (formalCusp P R z p)≠0:=by
    intro z hz
    rw[formalCusp_constant]
    exact one_ne_zero
  exact (hF.inv h0) (j+1) le_rfl

lemma transportCoefficient_restrict_closed (Ω:Set ℂ)(hΩ:IsOpen Ω)
    (hcover:∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω)(P:PsiTheory)(R:ℂ→ℂ)
    (hR:AnalyticOnNhd ℂ R Ω)(hR0:R y₀=0)
    (hraw:∀Y∈Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ))
    (hunit:∀z∈Ω,WP.Analysis.complexAUnit z≠0)(p j:ℕ)(Y:ℝ)(hY:Y∈Icc (0:ℝ) y₀):
    transportCoefficient P R p j (Y:ℂ)=(WP.HigherOrder.transportCoefficient P p j Y:ℂ):=by
  have he:formalCusp P R (Y:ℂ) p=ofRealSeries (WP.HigherOrder.formalCusp P Y p):=
    (canonical_formal_series_restrict_closed Ω hΩ hcover R hR hR0 hraw hunit P Y hY).2.1 p
  rw[transportCoefficient,he,←ofRealSeries_inv,ofRealSeries_coeff]
  rfl

lemma transportCoefficient_family_quotient_extension_of_recursiveRemainder
    (P:PsiTheory)(hr:WP.HigherOrder.UniformRecursiveRemainderTarget P):
    ∃V:Set ℂ,IsOpen V ∧ Convex ℝ V ∧ (∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈V) ∧
      ∀p:ℕ,1≤p→∀j:ℕ,1≤j→∃F:ℂ→ℂ,AnalyticOnNhd ℂ F V ∧
        ∀Y∈Ico (0:ℝ) y₀,F (Y:ℂ)=
          ((WP.HigherOrder.transportCoefficient P p j Y/(A Y*r Y):ℝ):ℂ):=by
  obtain ⟨Ω,R,C,B,M,hΩ,hΩconv,hcover,hC,hB,hM,hR,hunit,hraw,hR0,hR',hkernel,hpa,hca,hpr,hcr,hpb,hcb⟩:=WP.coefficient_bounds P
  have hA:AnalyticOnNhd ℂ (kernelA R) Ω:=kernelA_analyticOnNhd Ω hΩ hcover R hR hR0 hraw hunit
  have hAr(Y:ℝ)(hY:Y∈Icc (0:ℝ) y₀):kernelA R (Y:ℂ)=(A Y:ℂ):=
    (actual_kernel_inputs_restrict_closed Ω hΩ hcover R hR hR0 hraw hunit Y hY).1
  have hc:(y₀:ℂ)∈Ω:=hcover y₀ ⟨y₀_pos.le,le_rfl⟩
  have hdR:=WP.Analysis.dslope_analyticOnNhd_complex Ω hΩ R hR y₀ hc
  let U:Set ℂ:={z|z∈Ω ∧ kernelA R z≠0 ∧ dslope R (y₀:ℂ) z≠0}
  have hU:IsOpen U:=by
    rw[isOpen_iff_mem_nhds]
    intro z hz
    filter_upwards [hΩ.mem_nhds hz.1,(hA z hz.1).continuousAt.eventually_ne hz.2.1,
      (hdR z hz.1).continuousAt.eventually_ne hz.2.2] with w hw hAne hRne
    exact ⟨hw,hAne,hRne⟩
  have hUcover:∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈U:=by
    intro Y hY
    refine ⟨hcover Y hY,?_,?_⟩
    · rw[hAr Y hY]
      exact_mod_cast WP.HigherOrder.A_ne_zero_closed Y hY
    · by_cases he:Y=y₀
      · subst Y
        rw[dslope_same,hR']
        norm_num
      · have hYi:Y∈Ico (0:ℝ) y₀:=⟨hY.1,lt_of_le_of_ne hY.2 he⟩
        have hRne:R (Y:ℂ)≠0:=by rw[hraw Y hYi];exact_mod_cast (r_pos Y hYi).ne'
        intro hz
        have hf:=sub_smul_dslope R (y₀:ℂ) (Y:ℂ)
        simp only[hz,smul_zero,hR0,sub_zero] at hf
        exact hRne hf.symm
  obtain ⟨V,hV,hVconv,hVcover,hVU⟩:=WP.Analysis.exists_convex_physical_neighborhood U hU hUcover
  refine ⟨V,hV,hVconv,hVcover,?_⟩
  intro p hp j hj
  let G:ℂ→ℂ:=transportCoefficient P R p j
  have hG:AnalyticOnNhd ℂ G Ω:=transportCoefficient_analyticOnNhd Ω P R p j (fun n=>(hca n p hp).1)
  have hGr(Y:ℝ)(hY:Y∈Icc (0:ℝ) y₀):G (Y:ℂ)=(WP.HigherOrder.transportCoefficient P p j Y:ℂ):=
    transportCoefficient_restrict_closed Ω hΩ hcover P R hR hR0 hraw hunit p j Y hY
  have hG0:G (y₀:ℂ)=0:=by
    rw[hGr y₀ ⟨y₀_pos.le,le_rfl⟩,WP.HigherOrder.transportCoefficient_critical_of_recursiveRemainder P hr p j hp hj]
    rfl
  have hdG:=WP.Analysis.dslope_analyticOnNhd_complex Ω hΩ G hG y₀ hc
  let F:ℂ→ℂ:=fun z=>dslope G (y₀:ℂ) z/(kernelA R z*dslope R (y₀:ℂ) z)
  refine ⟨F,?_,?_⟩
  · intro z hz
    have hzU:=hVU hz
    exact (hdG z hzU.1).div ((hA z hzU.1).mul (hdR z hzU.1))
      (mul_ne_zero hzU.2.1 hzU.2.2)
  · intro Y hYi
    have hYc:Y∈Icc (0:ℝ) y₀:=⟨hYi.1,hYi.2.le⟩
    have hδ:(Y:ℂ)-(y₀:ℂ)≠0:=sub_ne_zero.mpr (by exact_mod_cast ne_of_lt hYi.2)
    have hAa:kernelA R (Y:ℂ)≠0:=by rw[hAr Y hYc];exact_mod_cast WP.HigherOrder.A_ne_zero_closed Y hYc
    have hRa:R (Y:ℂ)≠0:=by rw[hraw Y hYi];exact_mod_cast (r_pos Y hYi).ne'
    have hval:F (Y:ℂ)=G (Y:ℂ)/(kernelA R (Y:ℂ)*R (Y:ℂ)):=by
      dsimp only[F]
      rw[dslope_of_ne G (by exact_mod_cast ne_of_lt hYi.2),dslope_of_ne R (by exact_mod_cast ne_of_lt hYi.2)]
      simp only[slope,hG0,hR0,vsub_eq_sub,sub_zero,smul_eq_mul]
      field_simp[hδ,hAa,hRa]
    rw[hGr Y hYc,hAr Y hYc,hraw Y hYi] at hval
    simpa only[Complex.ofReal_div,Complex.ofReal_mul] using hval
end WP.HigherOrder.ComplexCanonical
