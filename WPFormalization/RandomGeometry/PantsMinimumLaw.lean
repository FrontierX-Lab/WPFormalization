import WPFormalization.RandomGeometry.PantsMinimum
import WPFormalization.RandomGeometry.PantsPrefixPoisson
import WPFormalization.Probability.PoissonVoidProbability

/-! The shortest actual two-cusp pants length has the original exponential
void law at the exact physical square-root scale, including threshold zero. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
variable {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P)
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)

include C MI in
theorem pants_minimum_length_limit (n : ℕ → ℕ)
    (hnfast : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop atTop)
    (t : ℝ) (ht : 0≤t) :
    Tendsto (fun g => (wpProbability G g (n g)).real
      {X : G.Moduli g (n g) (fun _ => 0) |
        ENNReal.ofReal t < ENNReal.ofReal (Real.sqrt (pantsScale g (n g)))*
          pantsMinimumLength H X}) atTop (𝓝 (Real.exp (-(t^2)))) := by
  let tNN : ℝ≥0 := ⟨t,ht⟩
  have hmeas : ∀g, Measurable (fun X : G.Moduli g (n g) (fun _ => 0) =>
      fun _ : Fin 1 => (pantsLengthPointProcess H X).count ℝ≥0 (nnrealPrefixWindow tNN)) := by
    intro g
    exact measurable_pi_lambda (fun _ : Fin 1 =>
      pantsLengthPointProcess_prefix_count_measurable G H tNN)
  have hv := poisson_void_probability_tendsto
    (fun g => wpProbability G g (n g))
    (fun g (X : G.Moduli g (n g) (fun _ => 0)) (_ : Fin 1) =>
      (pantsLengthPointProcess H X).count ℝ≥0 (nnrealPrefixWindow tNN))
    (fun _ : Fin 1 => Real.toNNReal ((tNN : ℝ)^2))
    (Eventually.of_forall hmeas)
    (pants_prefix_counts_poisson G H T C MI n hnfast tNN) (0 : Fin 1)
  simp only [Real.coe_toNNReal _ (sq_nonneg (tNN : ℝ))] at hv
  apply hv.congr'
  filter_upwards [pantsLengthScale_eventually_eq_sqrt n hnfast] with g hscale
  apply congrArg (fun B => (wpProbability G g (n g)).real B)
  ext X
  change (pantsLengthPointProcess H X).count ℝ≥0 (nnrealPrefixWindow tNN)=0 ↔ _
  rw [pantsLengthPointProcess_prefix_count_eq_minimum_void H X tNN,hscale]
  rw [←ENNReal.ofReal_coe_nnreal]
  rfl

end WP.RandomGeometry
