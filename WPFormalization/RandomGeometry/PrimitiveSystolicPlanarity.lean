import WPFormalization.RandomGeometry.PrimitiveMinimum
import WPFormalization.RandomGeometry.PrimitiveNonplanarRare
import WPFormalization.RandomGeometry.PantsMinimumLaw

/-! Every actual systolic primitive is planar with probability tending to one.
The argument combines the actual bounded-window nonplanar estimate with the
already proved two-cusp-pants void law; it needs no limiting cusp density. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)

def IsSystolicPrimitive {g n : ℕ} {X : G.Moduli g n (fun _=>0)} (γ : H.Primitive g n X) : Prop :=
  ENNReal.ofReal (H.length γ)=primitiveMinimumLength H X

lemma primitiveMinimumLength_le_pantsMinimumLength {g n : ℕ} (X : G.Moduli g n (fun _=>0)) :
    primitiveMinimumLength H X≤pantsMinimumLength H X := by
  apply le_iInf
  intro γ
  exact iInf_le _ γ.val

lemma primitive_systolic_nonplanar_subset {g n : ℕ} (t : ℝ) (ht : 0≤t) (hq : 0<pantsScale g n) :
    {X : G.Moduli g n (fun _=>0)|∃γ : H.Primitive g n X,IsSystolicPrimitive H γ ∧H.planarSide γ=none}⊆
      {X |ENNReal.ofReal t<ENNReal.ofReal (Real.sqrt (pantsScale g n))*pantsMinimumLength H X} ∪
      {X |∃γ : H.Primitive g n X,H.length γ≤t/Real.sqrt (pantsScale g n) ∧H.planarSide γ=none} := by
  rintro X ⟨γ,hγ,hno⟩
  by_cases hshort : H.length γ≤t/Real.sqrt (pantsScale g n)
  · exact Or.inr ⟨γ,hshort,hno⟩
  · left
    have hs := Real.sqrt_pos.mpr hq
    have hl : t<Real.sqrt (pantsScale g n)*H.length γ := by
      have hh := (div_lt_iff₀ hs).mp (lt_of_not_ge hshort)
      simpa only [mul_comm] using hh
    have hi := primitiveMinimumLength_le_pantsMinimumLength H X
    change ENNReal.ofReal (H.length γ)=primitiveMinimumLength H X at hγ
    rw [←hγ] at hi
    have hh := mul_le_mul' (le_refl (ENNReal.ofReal (Real.sqrt (pantsScale g n)))) hi
    rw [←ENNReal.ofReal_mul hs.le] at hh
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht).mpr hl |>.trans_le hh

include C MI in
theorem primitive_systolic_nonplanar_probability_tendsto_zero
    (n : ℕ→ℕ) (hn : Tendsto (fun g:ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop) :
    Tendsto (fun g=>(wpProbability G g (n g)).real {X |∃γ : H.Primitive g (n g) X,
      IsSystolicPrimitive H γ ∧H.planarSide γ=none}) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hevent := Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds (by positivity : (0:ℝ)<ε/2))
  obtain ⟨t,ht,hsmall⟩ := ((eventually_ge_atTop (1:ℝ)).and hevent).exists
  have htexp : Real.exp (-(t^2))<ε := by
    have ht2 : t≤t^2 := by nlinarith
    exact (Real.exp_le_exp.mpr (neg_le_neg ht2)).trans_lt (hsmall.trans (by linarith))
  have hlim := (pants_minimum_length_limit G H T C MI n hn t (by linarith)).add
    (primitiveNonplanar_probability_tendsto_zero T C MI n hn t (by linarith))
  simp only [add_zero] at hlim
  filter_upwards [hlim.eventually (gt_mem_nhds htexp),
    (WP.Spectral.pantsScale_tendsto_atTop n hn).eventually_gt_atTop (0:ℝ)] with g hbound hq
  letI := wpProbability_isFinite G g (n g)
  have hle := (measureReal_mono (μ:=wpProbability G g (n g)) (primitive_systolic_nonplanar_subset H t (by linarith) hq)).trans
    (measureReal_union_le _ _)
  simpa only [Real.dist_eq,sub_zero,Measure.real,abs_of_nonneg ENNReal.toReal_nonneg] using hle.trans_lt hbound

end WP.RandomGeometry
