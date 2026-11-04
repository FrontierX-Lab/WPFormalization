import WPFormalization.RandomGeometry.GeneralPlanarOriginalScaleOrderedMoments
import WPFormalization.RandomGeometry.GeneralPlanarLargeSideProbability

/-! The genuine all-type tail on the paper's original sqrt(q) length scale. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.RandomGeometry
open WP.External MeasureTheory Set Filter
open scoped Topology

lemma generalPlanar_original_rescaled_length_le_effective (n : ℕ→ℕ)
    (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop) (t : ℝ) (ht : 0≤t) :
    ∀ᶠg in atTop,t/Real.sqrt (pantsScale g (n g))≤
      (2*(1+t))/Real.sqrt (primitivePlanarEffectiveScale g (n g)) := by
  by_cases ht0 : t=0
  · subst t
    exact Eventually.of_forall (fun _=>by
      simp only [zero_div,add_zero,mul_one]
      exact div_nonneg (by norm_num) (Real.sqrt_nonneg _))
  · filter_upwards [generalPlanar_original_windows_subset_effective_cap n hn 1 (fun _=>0) (fun _=>t)
      (fun _=>le_rfl) (fun _=>ht),
      (WP.Spectral.pantsScale_tendsto_atTop n hn).eventually_gt_atTop (0:ℝ)] with g hsub hq
    have hp : t/Real.sqrt (pantsScale g (n g))∈
        generalPlanarStarScaledWindows 1 (pantsScale g (n g)) (fun _=>0) (fun _=>t) 0 := by
      exact ⟨by simpa using div_pos (lt_of_le_of_ne ht (Ne.symm ht0)) (Real.sqrt_pos.mpr hq),le_rfl⟩
    simpa [Fin.sum_univ_one] using (hsub 0 hp).2

variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)

include C MI in
theorem generalPlanar_original_large_side_probability_uniform (n : ℕ→ℕ)
    (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop) (t : ℝ) (ht : 0≤t) :
    ∀ε : ℝ,0<ε→∃K₀ : ℕ,∀ᶠg : ℕ in atTop,∀K : ℕ,K₀≤K→
      (wpProbability G g (n g)).real
        {X |∃γ : H.Primitive g (n g) X,H.length γ≤t/Real.sqrt (pantsScale g (n g)) ∧
          ∃S : Finset (Fin (n g)),H.planarSide γ=some S ∧ K+2≤S.card}≤ε := by
  intro ε hε
  obtain ⟨K₀,hK₀⟩ := generalPlanar_large_side_probability_uniform H T C MI n hn (2*(1+t))
    (by positivity) ε hε
  refine ⟨K₀,?_⟩
  filter_upwards [hK₀,generalPlanar_original_rescaled_length_le_effective n hn t ht] with g hkg hL
  intro K hK
  letI := wpProbability_isFinite G g (n g)
  apply le_trans ?_ (hkg K hK)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  rintro X ⟨γ,hγ,S,hS,hcard⟩
  exact ⟨γ,hγ.trans hL,S,hS,hcard⟩

end WP.RandomGeometry
