import WPFormalization.Analysis.TransportGammaComplexification
/-! All finite transport quotients use one parameter neighborhood: the domain
is determined only by the kernel data and the unit of the continued first
root. The marking parameter affects only finite algebra, so the critical
removal introduces no p-dependent shrink of the domain. -/
set_option maxHeartbeats 800000
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace WP.Analysis
open WP.HigherOrder
lemma transportGamma_family_quotient_complex_extension :
    ∃ Ω : Set ℂ,IsOpen Ω ∧ (∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) ∧
      ∀ p : ℕ,∃ F : ℂ → ℂ,AnalyticOnNhd ℂ F Ω ∧
        ∀ Y∈Ico (0:ℝ) y₀,F (Y:ℂ)=((transportGamma p Y/(A Y*r Y):ℝ):ℂ) := by
  obtain ⟨U,hU,hconv,hcover,R,Q,Ahat,hR,hQ,hA,hmatch,hmom,hcoeff,hunit,hraw,hR0,hR'⟩ :=
    common_holomorphic_all_kernel_moments
  have hAe : HasPhysicalHolomorphicExtension U A := ⟨Ahat,hA,fun Y hY => (hmatch Y hY).2⟩
  have hAie : HasPhysicalHolomorphicExtension U (fun Y => (A Y)⁻¹) := by
    refine ⟨fun z => (Ahat z)⁻¹,fun z hz => (hA z hz).inv (hunit z hz).2.1,?_⟩
    intro Y hY
    dsimp only
    rw [(hmatch Y hY).2,Complex.ofReal_inv]
  have hQe : HasPhysicalHolomorphicExtension U Theta := ⟨Q,hQ,fun Y hY => (hmatch Y hY).1⟩
  have hMe (j : ℕ) : HasPhysicalHolomorphicExtension U (WP.HigherOrder.kernelMoment j) :=
    ⟨complexKernelMoment R j,(hmom j).2.1,fun Y hY => ((hmom j).2.2 Y hY).2⟩
  have hBe (j : ℕ) : HasPhysicalHolomorphicExtension U (bMoment j) :=
    ⟨complexBMoment R j,(hmom j).1,fun Y hY => ((hmom j).2.2 Y hY).1⟩
  have hθe (n : ℕ) : HasPhysicalHolomorphicExtension U (fun Y => theta Y n) :=
    ⟨complexThetaCoeff R n,(hcoeff n).1,fun Y hY => ((hcoeff n).2.2 Y hY).1⟩
  have hwe (n : ℕ) : HasPhysicalHolomorphicExtension U (fun Y => weight Y n) :=
    ⟨complexWeightCoeff R n,(hcoeff n).2.1,fun Y hY => ((hcoeff n).2.2 Y hY).2⟩
  have hc : (y₀:ℂ)∈U := hcover y₀ ⟨y₀_pos.le,le_rfl⟩
  have hdR := dslope_analyticOnNhd_complex U hU R hR y₀ hc
  let Ω : Set ℂ := {z | z∈U ∧ dslope R (y₀:ℂ) z≠0}
  have hΩU : Ω⊆U := fun z hz => hz.1
  have hΩ : IsOpen Ω := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    filter_upwards [hU.mem_nhds hz.1,(hdR z hz.1).continuousAt.eventually_ne hz.2] with ζ hζ hRζ
    exact ⟨hζ,hRζ⟩
  have hΩcover : ∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω := by
    intro Y hY
    refine ⟨hcover Y hY,?_⟩
    by_cases he : Y=y₀
    · subst Y
      rw [dslope_same,hR']
      norm_num
    · have hYi : Y∈Ico (0:ℝ) y₀ := ⟨hY.1,lt_of_le_of_ne hY.2 he⟩
      have hRne : R (Y:ℂ)≠0 := by rw [hraw Y hYi];exact_mod_cast (r_pos Y hYi).ne'
      intro hzero
      have hf := sub_smul_dslope R (y₀:ℂ) (Y:ℂ)
      simp only [hzero,smul_zero,hR0,sub_zero] at hf
      exact hRne hf.symm
  refine ⟨Ω,hΩ,hΩcover,?_⟩
  intro p
  obtain ⟨G,hG,hGmatch⟩ := transportGamma_hasPhysicalHolomorphicExtension U hAe hAie hQe hMe hBe hθe hwe p
  have hG0 : G (y₀:ℂ)=0 := by rw [hGmatch y₀ ⟨y₀_pos.le,le_rfl⟩,transportGamma_critical];rfl
  have hdG := dslope_analyticOnNhd_complex U hU G hG y₀ hc
  let F : ℂ → ℂ := fun z => dslope G (y₀:ℂ) z/(Ahat z*dslope R (y₀:ℂ) z)
  refine ⟨F,?_,?_⟩
  · intro z hz
    exact (hdG z hz.1).div ((hA z hz.1).mul (hdR z hz.1))
      (mul_ne_zero (hunit z hz.1).2.1 hz.2)
  intro Y hYi
  have hYc : Y∈Icc (0:ℝ) y₀ := ⟨hYi.1,hYi.2.le⟩
  have hδ : (Y:ℂ)-(y₀:ℂ)≠0 := sub_ne_zero.mpr (by exact_mod_cast ne_of_lt hYi.2)
  have hAa : Ahat (Y:ℂ)≠0 := (hunit _ (hcover Y hYc)).2.1
  have hRa : R (Y:ℂ)≠0 := by rw [hraw Y hYi];exact_mod_cast (r_pos Y hYi).ne'
  have hFval : F (Y:ℂ)=G (Y:ℂ)/(Ahat (Y:ℂ)*R (Y:ℂ)) := by
    dsimp only [F]
    rw [dslope_of_ne G (by exact_mod_cast ne_of_lt hYi.2),
      dslope_of_ne R (by exact_mod_cast ne_of_lt hYi.2)]
    simp only [slope,hG0,hR0,vsub_eq_sub,sub_zero,smul_eq_mul]
    field_simp [hδ,hAa,hRa] <;> ring
  rw [hGmatch Y hYc,(hmatch Y hYc).2,hraw Y hYi] at hFval
  simpa only [Complex.ofReal_div,Complex.ofReal_mul] using hFval

end WP.Analysis
