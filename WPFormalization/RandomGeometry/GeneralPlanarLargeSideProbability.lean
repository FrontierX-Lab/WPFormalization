import WPFormalization.RandomGeometry.GeneralPlanarTypeTailAsymptotics
import WPFormalization.RandomGeometry.GeneralPlanarTypeTailEvents

/-! The uniform tail in terms of the actual geometry, without a count-defined
surrogate event or omission of the maximal possible side size. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open WP.External MeasureTheory Set Filter
open scoped Topology
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)

include C MI in
theorem generalPlanar_large_side_probability_uniform (n : ℕ→ℕ)
    (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (t : ℝ) (ht : 0≤t) :
    ∀ε : ℝ,0<ε→∃K₀ : ℕ,∀ᶠg : ℕ in atTop,∀K : ℕ,K₀≤K→
      (wpProbability G g (n g)).real
        {X | ∃γ : H.Primitive g (n g) X,
          H.length γ≤t/Real.sqrt (primitivePlanarEffectiveScale g (n g)) ∧
          ∃S : Finset (Fin (n g)),H.planarSide γ=some S ∧ K+2≤S.card}≤ε := by
  simpa only [generalPlanar_type_tail_pos_iff H] using
    generalPlanar_type_tail_probability_uniform H T C MI n hn t ht

end WP.RandomGeometry
