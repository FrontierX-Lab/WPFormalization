import WPFormalization.RandomGeometry.BoltzmannWpMixtureObservables
import WPFormalization.Marked.UnmarkedReduction
import WPFormalization.Probability.PointMeasureDilation
noncomputable section
universe u v
namespace WP.BoltzmannWp
open Set MeasureTheory Filter External
open scoped ENNReal Topology
variable {P : PsiTheory}

/-- The deterministic physical multiplier in Corollary 14.5. -/
def physicalScale (μ : ℝ) : ℝ := tightParameterScale (inverseY (parameter μ))

lemma muCritical_pos : 0 < muCritical :=
  div_pos Analysis.xCritical_pos_parameter (by positivity)

lemma physicalScale_pos (μ : ℝ) (hμ : μ∈Ico (0:ℝ) muCritical) :
    0 < physicalScale μ :=
  tightParameterScale_pos _ (inverseY_branch _ (parameter_physical μ hμ)).1

lemma physicalScale_zero : physicalScale 0=1 := by
  rw [physicalScale,parameter,mul_zero,Analysis.inverseY_zero_value,
    tightParameterScale,r_zero_parameter]
  have hp : Real.sqrt (Real.pi^2)=Real.pi := Real.sqrt_sq Real.pi_pos.le
  convert div_self Real.pi_ne_zero using 1
  congr 1
  convert hp using 1 <;> ring

/-- Inversion is locally continuous at the unit scale; the direction is
physical deterministic scale divided by the conditional alpha scale. -/
lemma wpMixture_inverse_scale_in_probability (P:PsiTheory)
    (G:WeilPeterssonGeometry.{u,v} P) (gs:ℕ→ℕ)
    (hg:Tendsto gs atTop atTop) (xs:ℕ→ℝ)
    (hx:∀j,xs j∈Ico (0:ℝ) xCritical) (ε:ℝ) (hε:0<ε) :
    Tendsto (fun j=>wpMixture G (gs j) (xs j)
      {X|ε≤|tightParameterScale (inverseY (xs j))/tightScale ((X.fst:ℝ)/(gs j:ℝ))-1|})
      atTop (𝓝 0) := by
  have hc : ContinuousAt (fun x:ℝ=>x⁻¹) 1 := continuousAt_inv₀ one_ne_zero
  obtain ⟨δ,hδ,hδcontrol⟩ := Metric.continuousAt_iff.mp hc ε hε
  have ht := wpMixture_scale_in_probability P G gs hg xs hx δ hδ
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Eventually.of_forall fun _=>bot_le) _
  apply Eventually.of_forall
  intro j
  apply measure_mono
  intro X hX
  change δ≤|tightScale ((X.fst:ℝ)/(gs j:ℝ))/tightParameterScale (inverseY (xs j))-1|
  by_contra hn
  have hh := hδcontrol (lt_of_not_ge hn)
  simp only [Real.dist_eq,inv_one,inv_div] at hh
  exact (not_lt_of_ge hX) hh

lemma wpMixture_physical_scale_in_probability (P:PsiTheory)
    (G:WeilPeterssonGeometry.{u,v} P) (gs:ℕ→ℕ)
    (hg:Tendsto gs atTop atTop) (μs:ℕ→ℝ)
    (hμ:∀j,μs j∈Ico (0:ℝ) muCritical) (ε:ℝ) (hε:0<ε) :
    Tendsto (fun j=>wpMixture G (gs j) (parameter (μs j))
      {X|ε≤|physicalScale (μs j)/tightScale ((X.fst:ℝ)/(gs j:ℝ))-1|})
      atTop (𝓝 0) :=
  wpMixture_inverse_scale_in_probability P G gs hg (fun j=>parameter (μs j))
    (fun j=>parameter_physical _ (hμ j)) ε hε

lemma wpMixture_parameter_zero (G:WeilPeterssonGeometry.{u,v} P) (g:ℕ) :
    wpMixture G g (parameter 0)=(wpProbability G g 0).map
      (@Sigma.mk ℕ (fun n=>G.Moduli g n (fun _=>0)) 0) := by
  simpa only [parameter,mul_zero] using wpMixture_zero G g

/-- Positive ratio that dilates the conditional spectrum to physical scale. -/
def scaleRatio (g : ℕ) (μ : ℝ) (hμ : μ∈Ico (0:ℝ) muCritical) (n : ℕ) :
    Probability.PositiveScale :=
  ⟨⟨physicalScale μ/tightScale ((n:ℝ)/(g:ℝ)),
    (div_pos (physicalScale_pos μ hμ) (TightConnected.tightScale_pos _ (by positivity))).le⟩,
    by exact_mod_cast (div_pos (physicalScale_pos μ hμ)
      (TightConnected.tightScale_pos ((n:ℝ)/(g:ℝ)) (by positivity)))⟩

lemma scaleRatio_coe (g n : ℕ) (μ : ℝ) (hμ : μ∈Ico (0:ℝ) muCritical) :
    (((scaleRatio g μ hμ n).val):ℝ)=physicalScale μ/tightScale ((n:ℝ)/(g:ℝ)) := rfl

lemma measurable_scaleRatio (G:WeilPeterssonGeometry.{u,v} P) (g : ℕ)
    (μ : ℝ) (hμ : μ∈Ico (0:ℝ) muCritical) :
    Measurable (fun X:Surface G g=>scaleRatio g μ hμ X.fst) :=
  (measurable_of_countable (scaleRatio g μ hμ)).comp
    (Probability.measurable_sigmaFst (Ω:=fun n=>G.Moduli g n (fun _=>0)))

lemma scaleRatio_in_probability (P:PsiTheory) (G:WeilPeterssonGeometry.{u,v} P)
    (gs:ℕ→ℕ) (hg:Tendsto gs atTop atTop) (μs:ℕ→ℝ)
    (hμ:∀j,μs j∈Ico (0:ℝ) muCritical) (ε:ℝ) (hε:0<ε) :
    Tendsto (fun j=>wpMixture G (gs j) (parameter (μs j))
      {X|ε≤|(((scaleRatio (gs j) (μs j) (hμ j) X.fst).val):ℝ)-1|})
      atTop (𝓝 0) :=
  wpMixture_physical_scale_in_probability P G gs hg μs hμ ε hε

lemma physicalScale_tendsto {μs:ℕ→ℝ} {μ:ℝ}
    (hμs:∀j,μs j∈Ico (0:ℝ) muCritical) (hμ:μ∈Ico (0:ℝ) muCritical)
    (ht:Tendsto μs atTop (𝓝 μ)) :
    Tendsto (fun j=>physicalScale (μs j)) atTop (𝓝 (physicalScale μ)) := by
  have hx := parameter_physical μ hμ
  have hy := (Analysis.inverseY_analyticAt_interior _ hx).continuousAt.tendsto.comp
    (ht.const_mul (2*Real.pi^2))
  have hyr : Tendsto (fun j=>inverseY (parameter (μs j))) atTop
      (𝓝[Ico (0:ℝ) y₀] inverseY (parameter μ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hy,Eventually.of_forall (fun j=>(inverseY_branch _ (parameter_physical _ (hμs j))).1)⟩
  have hrOn : ContinuousOn r (Ico (0:ℝ) y₀) :=
    continuousOn_iff_continuous_restrict.mpr Analysis.r_continuous_interior
  have hr := (hrOn _ (inverseY_branch _ hx).1).tendsto.comp hyr
  exact ((hr.const_mul 2).sqrt.div_const Real.pi)
end WP.BoltzmannWp
