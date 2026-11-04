import WPFormalization.Analysis.KernelJetComplexification
import WPFormalization.HigherOrder.BMoments
/-! The true signed dilaton moments have holomorphic extensions on a single
convex complex neighborhood of the physical interval. The finite Stirling jet
identity is the bridge to the actual absolutely convergent b_d moments. The
same neighborhood carries A, the total weight mass and all inverse-kernel
coefficients, with A and the total mass nonzero throughout the neighborhood.
This does not assert uniform complex geometric coefficient bounds. -/
set_option maxHeartbeats 800000
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace WP.Analysis

lemma barH_jet_one_im_zero (Y : ℝ) (j : ℕ) : (iteratedDeriv j (barH Y) 1).im=0 := by
  have hs := Complex.hasSum_im (WP.HigherOrder.monomial_iteratedDeriv_coeff_hasSum
    (barH Y) (barH_differentiable Y) j)
  have he : (fun n : ℕ => ((n.descFactorial j:ℂ)*WP.coeff (barH Y) n).im)=(fun _ => (0:ℝ)) := by
    funext n
    simp only [Complex.mul_im,Complex.natCast_re,Complex.natCast_im,barH_realCoefficients Y n,
      mul_zero,zero_mul,add_zero]
  rw [he] at hs
  exact hs.unique hasSum_zero

def complexBMoment (R : ℂ → ℂ) (j : ℕ) (z : ℂ) : ℂ :=
  (∑ k∈Finset.range (j+1),(Nat.stirlingSecond (j+1) (k+1):ℂ)*regularizedKernelJet H R k 1 z)/3

lemma complexBMoment_analyticOnNhd (Ω : Set ℂ) (R : ℂ → ℂ)
    (hjet : ∀ k : ℕ,AnalyticOnNhd ℂ (regularizedKernelJet H R k 1) Ω) (j : ℕ) :
    AnalyticOnNhd ℂ (complexBMoment R j) Ω := by
  intro z hz
  apply AnalyticAt.div_const
  apply Finset.analyticAt_fun_sum
  intro k hk
  exact analyticAt_const.mul (hjet k z hz)

lemma complexBMoment_restrict_closed (R : ℂ → ℂ)
    (hjet : ∀ k : ℕ,∀ Y∈Icc (0:ℝ) y₀,regularizedKernelJet H R k 1 (Y:ℂ)=iteratedDeriv k (barH Y) 1)
    (j : ℕ) (Y : ℝ) (hY : Y∈Icc (0:ℝ) y₀) :
    complexBMoment R j (Y:ℂ)=(WP.HigherOrder.bMoment j Y:ℂ) := by
  unfold complexBMoment
  rw [WP.HigherOrder.bMoment_eq_stirling_jets]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [hjet k Y hY]
  congr 1
  apply Complex.ext
  · simp
  · simpa using barH_jet_one_im_zero Y k

lemma exists_convex_physical_neighborhood (U : Set ℂ) (hU : IsOpen U)
    (hcover : ∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈U) :
    ∃ Ω : Set ℂ,IsOpen Ω ∧ Convex ℝ Ω ∧ (∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) ∧ Ω⊆U := by
  let S : Set ℂ := Complex.ofReal '' Icc (0:ℝ) y₀
  have hSc : IsCompact S := isCompact_Icc.image Complex.continuous_ofReal
  have hSv : Convex ℝ S := by
    rintro z ⟨x,hx,rfl⟩ w ⟨y,hy,rfl⟩ a b ha hb hab
    refine ⟨a*x+b*y,(convex_Icc (𝕜:=ℝ) (0:ℝ) y₀) hx hy ha hb hab,?_⟩
    simp only [Complex.ofReal_add,Complex.ofReal_mul,Complex.real_smul]
  have hSU : S⊆U := by
    rintro z ⟨Y,hY,rfl⟩
    exact hcover Y hY
  obtain ⟨δ,hδ,hδU⟩ := hSc.exists_thickening_subset_open hU hSU
  refine ⟨Metric.thickening δ S,Metric.isOpen_thickening,hSv.thickening δ,?_,hδU⟩
  intro Y hY
  exact Metric.self_subset_thickening hδ S ⟨Y,hY,rfl⟩

lemma common_holomorphic_kernel_moments :
    ∃ Ω : Set ℂ,IsOpen Ω ∧ Convex ℝ Ω ∧ (∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) ∧
      ∃ R Q Ahat : ℂ → ℂ,AnalyticOnNhd ℂ R Ω ∧ AnalyticOnNhd ℂ Q Ω ∧ AnalyticOnNhd ℂ Ahat Ω ∧
        (∀ Y∈Icc (0:ℝ) y₀,Q (Y:ℂ)=(((∑'l : ℕ,weight Y l):ℝ):ℂ) ∧ Ahat (Y:ℂ)=(A Y:ℂ)) ∧
        (∀ j : ℕ,AnalyticOnNhd ℂ (complexBMoment R j) Ω ∧
          ∀ Y∈Icc (0:ℝ) y₀,complexBMoment R j (Y:ℂ)=(WP.HigherOrder.bMoment j Y:ℂ)) ∧
        (∀ n : ℕ,AnalyticOnNhd ℂ (complexThetaCoeff R n) Ω ∧ AnalyticOnNhd ℂ (complexWeightCoeff R n) Ω ∧
          ∀ Y∈Icc (0:ℝ) y₀,complexThetaCoeff R n (Y:ℂ)=(theta Y n:ℂ) ∧ complexWeightCoeff R n (Y:ℂ)=(weight Y n:ℂ)) ∧
        (∀ z∈Ω,Q z≠0 ∧ Ahat z≠0 ∧ complexAUnit z≠0) ∧
        (∀ Y∈Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ)) ∧ R y₀=0 ∧ deriv R y₀=-3 := by
  obtain ⟨U,hU,hcover,R,Q,Ahat,hR,hQ,hA,hmatch,hjet,hcoeff,hunit,hraw,hR0,hR'⟩ :=
    common_holomorphic_kernel_jets
  let Ω : Set ℂ := {z | z∈U ∧ Q z≠0 ∧ Ahat z≠0}
  have hΩU : Ω⊆U := fun z hz => hz.1
  have hΩ : IsOpen Ω := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    filter_upwards [hU.mem_nhds hz.1,(hQ z hz.1).continuousAt.eventually_ne hz.2.1,
      (hA z hz.1).continuousAt.eventually_ne hz.2.2] with ζ hζ hQζ hAζ
    exact ⟨hζ,hQζ,hAζ⟩
  have hΩcover : ∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω := by
    intro Y hY
    refine ⟨hcover Y hY,?_,?_⟩
    · rw [(hmatch Y hY).1]
      have hmass : 0<∑'l : ℕ,weight Y l := by
        by_cases he : Y=y₀
        · subst Y
          rw [total_weight_critical_value]
          norm_num
        · have hYi : Y∈Ico (0:ℝ) y₀ := ⟨hY.1,lt_of_le_of_ne hY.2 he⟩
          rw [Theta_eq_neg_two_T_deriv Y hYi]
          have hneg := T_deriv_neg_interior Y hYi
          linarith
      exact_mod_cast hmass.ne'
    · rw [(hmatch Y hY).2]
      have hApos : 0<A Y := div_pos (barH_one_re_pos Y hY) (by norm_num)
      exact_mod_cast hApos.ne'
  obtain ⟨V,hV,hVconv,hVcover,hVΩ⟩ := exists_convex_physical_neighborhood Ω hΩ hΩcover
  have hVU : V⊆U := hVΩ.trans hΩU
  refine ⟨V,hV,hVconv,hVcover,R,Q,Ahat,hR.mono hVU,hQ.mono hVU,hA.mono hVU,hmatch,?_,?_,?_,hraw,hR0,hR'⟩
  · intro j
    refine ⟨complexBMoment_analyticOnNhd V R (fun k => ((hjet k 1).2.1).mono hVU) j,?_⟩
    exact complexBMoment_restrict_closed R (fun k Y hY => ((hjet k 1).2.2 Y hY).2) j
  · intro n
    exact ⟨(hcoeff n).1.mono hVU,(hcoeff n).2.1.mono hVU,(hcoeff n).2.2⟩
  · intro z hz
    have hzΩ := hVΩ hz
    exact ⟨hzΩ.2.1,hzΩ.2.2,hunit z hzΩ.1⟩
end WP.Analysis
