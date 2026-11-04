import WPFormalization.External.ShortLoopStraighteningGeometry
noncomputable section
set_option maxHeartbeats 0
universe u v
namespace WP.Critical.ShortConfiguration
open Set WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortLoopStraighteningGeometry
open scoped ENNReal

/- Actual metric variation estimate, derived from the quotient Lipschitz
property and the one-period axis parametrization. -/
lemma primitiveLoop_length_le (B : BorderedGeometry.{u,v}) (γ:B.curves.Primitive) :
    (primitiveLoop B γ).length ≤ ENNReal.ofReal (B.curves.length γ) := by
  let g : unitInterval→ℝ := fun t => (t:ℝ)*B.curves.length γ
  have hp : 0<B.curves.length γ := (B.curves.representative γ).period_pos
  have hm : MonotoneOn g univ := by
    intro a ha b hb hab
    exact mul_le_mul_of_nonneg_right hab hp.le
  have hv : eVariationOn g univ=ENNReal.ofReal (B.curves.length γ) := by
    have he := hm.eVariationOn_eq (a:=0) (b:=1) (mem_univ _) (mem_univ _)
    have hI : Icc (0:unitInterval) 1=univ := Set.eq_univ_of_forall (fun t=>⟨t.property.1,t.property.2⟩)
    simpa [g,hI] using he
  have hc := (curveParam_lipschitz B γ).lipschitzOnWith.comp_eVariationOn_le
    (g:=g) (s:=univ) (fun t ht=>mem_univ (g t))
  change eVariationOn (curveParam B γ ∘ g) univ ≤ _
  simpa [hv] using hc

lemma primitiveLoop_positiveHomotopyLength (B : BorderedGeometry.{u,v})
    (hcomplete:B.surface.domain=univ) (H:LoopStraighteningClassics B hcomplete)
    (γ:B.curves.Primitive) : (primitiveLoop B γ).PositiveHomotopyLength := by
  exact ⟨B.curves.length γ,(B.curves.representative γ).period_pos,
    fun f hf=>H.length_minimal γ f hf⟩

lemma primitiveLoop_length_eq (B : BorderedGeometry.{u,v})
    (hcomplete:B.surface.domain=univ) (H:LoopStraighteningClassics B hcomplete)
    (γ:B.curves.Primitive) :
    (primitiveLoop B γ).length = ENNReal.ofReal (B.curves.length γ) := by
  apply le_antisymm (primitiveLoop_length_le B γ)
  apply H.length_minimal γ (primitiveLoop B γ)
  exact Or.inl ⟨ContinuousMap.HomotopyWith.refl _ (primitiveLoop B γ).closed⟩

lemma primitiveLoop_simple (B : BorderedGeometry.{u,v}) (γ:B.curves.Primitive)
    (hγ:SimpleTrace B γ) : (primitiveLoop B γ).Simple := by
  intro a ha b hb he
  have hp : 0<B.curves.length γ := (B.curves.representative γ).period_pos
  have hma : (a:ℝ)*B.curves.length γ∈Ico 0 (B.curves.length γ) := by
    constructor
    · exact mul_nonneg a.property.1 hp.le
    · exact (mul_lt_mul_of_pos_right (show (a:ℝ)<1 from ha.2) hp).trans_eq (one_mul _)
  have hmb : (b:ℝ)*B.curves.length γ∈Ico 0 (B.curves.length γ) := by
    constructor
    · exact mul_nonneg b.property.1 hp.le
    · exact (mul_lt_mul_of_pos_right (show (b:ℝ)<1 from hb.2) hp).trans_eq (one_mul _)
  have hab : (a:ℝ)*B.curves.length γ=(b:ℝ)*B.curves.length γ := hγ hma hmb he
  exact Subtype.ext (mul_right_cancel₀ hp.ne' hab)

lemma primitiveLoop_trace (B : BorderedGeometry.{u,v}) (γ:B.curves.Primitive) :
    (primitiveLoop B γ).trace = B.curves.trace γ := by
  ext p
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨_,⟨(t:ℝ)*B.curves.length γ,rfl⟩,rfl⟩
  · intro hp
    obtain ⟨t,ht,he⟩:=trace_has_period_parameter B γ p hp
    have hpos:0<B.curves.length γ := (B.curves.representative γ).period_pos
    let a:unitInterval:=⟨t/B.curves.length γ,⟨div_nonneg ht.1 hpos.le,(div_lt_one hpos).mpr ht.2 |>.le⟩⟩
    refine ⟨a,?_⟩
    change curveParam B γ ((t/B.curves.length γ)*B.curves.length γ)=p
    rw [div_mul_cancel₀ t hpos.ne']
    exact he

end WP.Critical.ShortConfiguration
