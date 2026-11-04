import WPFormalization.Tight.SpectrumTupleExtensionsGoodMoments
/- Appendix F.4 local actual-spectrum proof. The original normalized WP
measure and the complete primitive tight catalogue are retained; all limits
are proved from the previously formalized geometric moment producers. -/
noncomputable section
universe u v w z
namespace WP.Probability
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Classical

lemma lintegral_off_event_eq_sub {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Set Ω) (hA : MeasurableSet A) (f : Ω→ℝ≥0∞)
    (hfin : (∫⁻ω,if ω∈A then f ω else 0 ∂μ)≠∞) :
    (∫⁻ω,if ω∈A then 0 else f ω ∂μ) =
      (∫⁻ω,f ω ∂μ)-(∫⁻ω,if ω∈A then f ω else 0 ∂μ) := by
  have he : (∫⁻ω,if ω∈A then f ω else 0 ∂μ)=∫⁻ω in A,f ω ∂μ := by
    simpa only [Set.indicator_apply] using lintegral_indicator hA f
  have hc : (∫⁻ω,if ω∈A then 0 else f ω ∂μ)=∫⁻ω in Aᶜ,f ω ∂μ := by
    rw [←lintegral_indicator hA.compl]
    apply lintegral_congr
    intro ω
    by_cases hω : ω∈A <;> simp only [Set.indicator_apply,Set.mem_compl_iff,hω,not_true_eq_false,
      not_false_eq_true,ite_true,ite_false]
  rw [he] at hfin
  rw [he,hc]
  exact setLIntegral_compl hA hfin

lemma lintegral_off_events_tendsto {Ω : ℕ→Type u} [∀j,MeasurableSpace (Ω j)]
    (μ : (j:ℕ)→Measure (Ω j)) (A : (j:ℕ)→Set (Ω j))
    (hA : ∀ᶠj in atTop,MeasurableSet (A j))
    (f : (j:ℕ)→Ω j→ℝ≥0∞) (L : ℝ≥0∞)
    (hgood : Tendsto (fun j=>∫⁻ω,f j ω ∂μ j) atTop (𝓝 L))
    (hbad : Tendsto (fun j=>∫⁻ω,if ω∈A j then f j ω else 0 ∂μ j) atTop (𝓝 0)) :
    Tendsto (fun j=>∫⁻ω,if ω∈A j then 0 else f j ω ∂μ j) atTop (𝓝 L) := by
  have ht:=ENNReal.Tendsto.sub hgood hbad (Or.inr ENNReal.zero_ne_top)
  simp only [tsub_zero] at ht
  apply ht.congr'
  filter_upwards [hA,hbad.eventually (gt_mem_nhds (by simp : (0:ℝ≥0∞)<∞))] with j hj hfin
  exact (lintegral_off_event_eq_sub (μ j) (A j) hj (f j) hfin.ne).symm

end WP.Probability
