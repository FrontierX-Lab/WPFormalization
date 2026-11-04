import WPFormalization.RandomGeometry.PrimitiveNonseparatingMoments
import WPFormalization.Spectral.PantsScaleGrowth

/-! Genuine nonseparating competitors disappear on every bounded rescaled
window, uniformly over cusp density. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.RandomGeometry
open WP.External MeasureTheory Set Filter
open scoped Topology ENNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    {H : HyperbolicCurveGeometry.{u,v,w} G} (T : MulticurveTopology.{u,v,w,z} G H)
    (MI : MirzakhaniIntegration G H T) {g n : ℕ}

lemma primitiveNonseparatingWindowSum_eq_card (X : G.Moduli g n (fun _=>0))
    (L : ℝ) (hL : 0≤L) : primitiveNonseparatingWindowSum T X L=
      (Nat.card {γ : H.Primitive g n X //H.length γ≤L ∧ WP.Critical.IsNonseparating T γ}:ℝ≥0∞) := by
  rw [primitiveNonseparatingWindowSum_eq_actual T X L hL]
  change curveNNLengthMeasure H X 1 _ (Iic (Real.toNNReal L))=_
  rw [curveNNLengthMeasure_Iic H X 1 (by norm_num)]
  simp only [Real.coe_toNNReal L hL,div_one]

lemma primitiveNonseparatingWindowSum_ge_one_of_exists (X : G.Moduli g n (fun _=>0))
    (L : ℝ) (hL : 0≤L)
    (hγ : ∃γ : H.Primitive g n X,H.length γ≤L ∧ WP.Critical.IsNonseparating T γ) :
    1≤primitiveNonseparatingWindowSum T X L := by
  let A := {γ : H.Primitive g n X //H.length γ≤L ∧ WP.Critical.IsNonseparating T γ}
  let f : A→{γ : H.Primitive g n X //γ∈H.shortPrimitive X L} :=
    fun γ=>⟨γ.val,(H.mem_shortPrimitive X L γ.val).mpr γ.property.1⟩
  haveI : Finite A := Finite.of_injective f (by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun z : {γ : H.Primitive g n X //γ∈H.shortPrimitive X L}=>z.val) h)
  obtain ⟨γ,hγ⟩ := hγ
  haveI : Nonempty A := ⟨⟨γ,hγ⟩⟩
  have hp : 1≤Nat.card A := Nat.card_pos
  rw [primitiveNonseparatingWindowSum_eq_card T X L hL]
  exact_mod_cast hp

include MI in
lemma primitiveNonseparating_probability_le_mean (L : ℝ) (hL : 0≤L) :
    wpProbability G g n {X |∃γ : H.Primitive g n X,
      H.length γ≤L ∧ WP.Critical.IsNonseparating T γ}≤
      ∫⁻X : G.Moduli g n (fun _=>0),primitiveNonseparatingWindowSum T X L ∂wpProbability G g n := by
  exact meas_le_lintegral₀ (primitiveNonseparatingWindowSum_measurable T MI L).aemeasurable
    (fun X hX=>primitiveNonseparatingWindowSum_ge_one_of_exists T X L hL hX)

include MI in
theorem primitiveNonseparating_probability_uniform_upper :
    ∃N : ℕ,∀g : ℕ,N≤g→∀n : ℕ,∀L : ℝ,0≤L→
      (wpProbability G g n).real {X |∃γ : H.Primitive g n X,
        H.length γ≤L ∧ WP.Critical.IsNonseparating T γ}≤Real.exp L*L^2 := by
  obtain ⟨N,hN⟩ := primitive_nonseparating_volume_ratio_bound P
  refine ⟨max 3 N,?_⟩
  intro g hg n L hL
  obtain ⟨hV,hR⟩ := hN g ((le_max_right _ _).trans hg) n
  have hi := (primitiveNonseparating_probability_le_mean T MI (g:=g) (n:=n) L hL).trans
    (primitiveNonseparating_probability_lintegral_upper T MI (g:=g) (n:=n)
      ((le_max_left _ _).trans hg) L hL hV)
  have hbd : Real.exp L*(volumeModel P (g-1) (n+2)/volumeModel P g n)*(L^2/2)≤Real.exp L*L^2 := by
    have hp := mul_le_mul_of_nonneg_left hR (mul_nonneg (Real.exp_pos L).le (sq_nonneg L))
    nlinarith
  have h := hi.trans (ENNReal.ofReal_le_ofReal hbd)
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simpa only [Measure.real,ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos L).le (sq_nonneg L))] using hr

include MI in
theorem primitiveNonseparating_probability_tendsto_zero (n : ℕ→ℕ)
    (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop) (t : ℝ) (ht : 0≤t) :
    Tendsto (fun g=>(wpProbability G g (n g)).real
      {X |∃γ : H.Primitive g (n g) X,H.length γ≤t/Real.sqrt (pantsScale g (n g)) ∧
        WP.Critical.IsNonseparating T γ}) atTop (𝓝 0) := by
  obtain ⟨N,hN⟩ := primitiveNonseparating_probability_uniform_upper T MI
  have hL : Tendsto (fun g=>t/Real.sqrt (pantsScale g (n g))) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using
      (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
        (WP.Spectral.pantsScale_tendsto_atTop n hn))).const_mul t
  have hbound := hL.rexp.mul (hL.pow 2)
  simp only [Real.exp_zero,zero_pow (by norm_num : 2≠0),mul_zero] at hbound
  apply squeeze_zero' (Eventually.of_forall (fun _=>ENNReal.toReal_nonneg)) ?_ hbound
  filter_upwards [eventually_ge_atTop N] with g hg
  exact hN g hg (n g) _ (div_nonneg ht (Real.sqrt_nonneg _))

end WP.RandomGeometry
