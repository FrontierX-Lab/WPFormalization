import WPFormalization.Critical.SeparatingNonPantsEstimate
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import WPFormalization.Critical.MixedIntersectingDomination

/- Actual bad-event estimates. A measurable dominating count is essential for
outer-measure Markov bounds; no measurability of arbitrary geometric relations
is presumed. The separating non-pants count below has genuine MI measurability. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.Critical
open WP.External WP.RandomGeometry MeasureTheory Filter Set
open scoped ENNReal Topology

lemma bad_event_probability_tendsto_zero_of_measurable_majorant
    {Ω : ℕ → Type u} [∀g, MeasurableSpace (Ω g)]
    (μ : (g : ℕ) → Measure (Ω g)) (A : (g : ℕ) → Set (Ω g))
    (M : (g : ℕ) → Ω g → ℝ≥0∞)
    (hM : ∀ᶠg in atTop, AEMeasurable (M g) (μ g))
    (hbound : ∀ᶠg in atTop, ∀X∈A g, 1≤M g X)
    (hmean : Tendsto (fun g => ∫⁻X, M g X ∂μ g) atTop (𝓝 0)) :
    Tendsto (fun g => μ g (A g)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmean
  · exact Filter.Eventually.of_forall (fun _ => bot_le)
  · filter_upwards [hM,hbound] with g hg hb
    exact meas_le_lintegral₀ hg hb

variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {H : HyperbolicCurveGeometry.{u,v,w} G}
  (T : MulticurveTopology.{u,v,w,z} G H) {g n : ℕ}

def HasShortSeparatingNonPants (L : ℝ) (X : G.Moduli g n (fun _ => 0)) : Prop :=
  ∃γ : H.Primitive g n X, IsSeparatingNonPants T γ ∧ H.length γ≤L

lemma one_le_separatingNonPantsCount_of_bad (L : ℝ)
    (X : G.Moduli g n (fun _ => 0)) (hX : HasShortSeparatingNonPants T L X) :
    1 ≤ separatingNonPantsCount T X L := by
  rcases hX with ⟨γ,hγ,hL⟩
  exact ENNReal.le_tsum (f := fun _ : SeparatingNonPantsCurve T X L => (1:ℝ≥0∞))
    ⟨γ,hγ,hL⟩

lemma shortSeparatingNonPants_probability_le (MI : MirzakhaniIntegration G H T)
    (hg : 1≤g) (L : ℝ) :
    wpProbability G g n {X | HasShortSeparatingNonPants T L X} ≤
      ∫⁻X,separatingNonPantsCount T X L ∂wpProbability G g n :=
  meas_le_lintegral₀ (separatingNonPantsCount_measurable T MI hg L).aemeasurable
    (fun X hX => one_le_separatingNonPantsCount_of_bad T L X hX)

lemma critical_shortSeparatingNonPants_probability_tendsto_zero
    (MI : MirzakhaniIntegration G H T) (L : ℝ) (hL : 0≤L)
    (n : ℕ→ℕ) (c : ℝ) (hc : 0<c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c)) :
    Tendsto (fun g => wpProbability G g (n g)
      {X | HasShortSeparatingNonPants T L X}) atTop (𝓝 0) := by
  apply bad_event_probability_tendsto_zero_of_measurable_majorant
    (fun g => wpProbability G g (n g)) _
    (fun _ X => separatingNonPantsCount T X L)
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with g hg
    exact (separatingNonPantsCount_measurable T MI hg L).aemeasurable
  · exact Eventually.of_forall (fun _ X hX =>
      one_le_separatingNonPantsCount_of_bad T L X hX)
  · exact critical_separatingNonPantsCount_tendsto_zero T MI L hL n c hc hn

lemma critical_shortSeparatingNonPants_probability_real_tendsto_zero
    (MI : MirzakhaniIntegration G H T) (L : ℝ) (hL : 0≤L)
    (n : ℕ→ℕ) (c : ℝ) (hc : 0<c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c)) :
    Tendsto (fun g => (wpProbability G g (n g)).real
      {X | HasShortSeparatingNonPants T L X}) atTop (𝓝 0) := by
  simpa only [Measure.real, ENNReal.toReal_zero, Function.comp_def] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (critical_shortSeparatingNonPants_probability_tendsto_zero T MI L hL n c hc hn)

lemma separatingNonPantsCount_eq_zero_of_no_bad (L : ℝ)
    (X : G.Moduli g n (fun _ => 0)) (hX : ¬HasShortSeparatingNonPants T L X) :
    separatingNonPantsCount T X L=0 := by
  apply ENNReal.tsum_eq_zero.mpr
  intro γ
  exact False.elim (hX ⟨γ.val,γ.property⟩)

lemma short_simple_nonseparating_or_pants_of_no_bad (L : ℝ)
    (X : G.Moduli g n (fun _ => 0)) (hX : ¬HasShortSeparatingNonPants T L X)
    (γ : H.Primitive g n X) (hs : H.simple γ) (hl : H.length γ≤L) :
    IsNonseparating T γ ∨ ∃S : Finset (Fin n),H.planarSide γ=some S ∧ S.card=2 := by
  by_cases hN : IsNonseparating T γ
  · exact Or.inl hN
  · exact Or.inr (by_contra (fun hp => hX ⟨γ,⟨hs,hN,hp⟩,hl⟩))

def HasIntersectingShortPants (L : ℝ) (X : G.Moduli g n (fun _ => 0)) : Prop :=
  ∃γ δ : H.Primitive g n X, γ≠δ ∧ γ∈H.shortPlanar X 2 L ∧
    δ∈H.shortPlanar X 2 L ∧ ¬T.disjoint γ δ

lemma one_le_allShortIntersecting_count_of_pants_bad (L : ℝ)
    (X : G.Moduli g n (fun _ => 0)) (hX : HasIntersectingShortPants T L X) :
    1 ≤ allShortIntersectingSimpleTupleCount T X 2 L := by
  rcases hX with ⟨γ,δ,hne,hγ,hδ,hnd⟩
  obtain ⟨hγL,S,hS,_⟩ := (H.mem_shortPlanar X 2 L γ).mp hγ
  obtain ⟨hδL,U,hU,_⟩ := (H.mem_shortPlanar X 2 L δ).mp hδ
  let curves : Fin 2 → H.Primitive g n X := ![γ,δ]
  have hinj : Function.Injective curves := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [curves]
  have hs : ∀i,H.simple (curves i) := by
    intro i
    fin_cases i
    · exact H.planar_simple γ S hS
    · exact H.planar_simple δ U hU
  have hl : ∀i,H.length (curves i)≤L := by intro i;fin_cases i <;> assumption
  have hd : ¬∀i j,i≠j → T.disjoint (curves i) (curves j) := by
    intro hh
    exact hnd (hh 0 1 (by decide))
  exact ENNReal.le_tsum (f := fun _ : ShortIntersectingSimpleTuple T X 2 L =>
    (1:ℝ≥0∞)) ⟨curves,hinj,hs,hl,hd⟩

/- Internal consumer, not a G3 producer. The measurable actual cut-family
majorant and its vanishing mean still have to be provided by the G3 proof. -/
lemma intersectingShortPants_probability_tendsto_zero_of_majorant
    (L : ℝ) (n : ℕ→ℕ)
    (M : (g : ℕ) → G.Moduli g (n g) (fun _ => 0) → ℝ≥0∞)
    (hM : ∀ᶠg in atTop, AEMeasurable (M g) (wpProbability G g (n g)))
    (hdom : ∀ᶠg in atTop, ∀X,allShortIntersectingSimpleTupleCount T X 2 L ≤ M g X)
    (hmean : Tendsto (fun g => ∫⁻X,M g X ∂wpProbability G g (n g))
      atTop (𝓝 0)) :
    Tendsto (fun g => wpProbability G g (n g)
      {X | HasIntersectingShortPants T L X}) atTop (𝓝 0) := by
  apply bad_event_probability_tendsto_zero_of_measurable_majorant
    (fun g => wpProbability G g (n g)) _ M hM _ hmean
  filter_upwards [hdom] with g hg X hX
  exact (one_le_allShortIntersecting_count_of_pants_bad T L X hX).trans (hg X)

end WP.Critical
