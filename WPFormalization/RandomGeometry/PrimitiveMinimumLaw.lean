import WPFormalization.RandomGeometry.PrimitiveMinimum
import WPFormalization.RandomGeometry.PrimitivePoissonProcess
import WPFormalization.RandomGeometry.PantsPrefixPoisson
import WPFormalization.Probability.PoissonVoidProbability

/-! The shortest actual primitive has the exact original-scale void law.
The definition assigns infinity to an empty actual curve catalog. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)

include C MI in
lemma primitive_prefix_counts_poisson
    (n : ℕ→ℕ) (hn : Tendsto (fun g:ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (l : ℝ≥0∞) (hl : Tendsto (fun g:ℕ=>ENNReal.ofReal ((n g:ℝ)/g)) atTop (𝓝 l)) (t : ℝ≥0) :
    LawConverges (fun g=>wpProbability G g (n g))
      (fun g X (_ : Fin 1)=>(primitiveLengthPointProcess H X).count ℝ≥0 (nnrealPrefixWindow t))
      (productPoissonMeasure (fun _ : Fin 1=>Real.toNNReal ((t:ℝ)^2*generalPlanarTotalWeight P (planarDensitySaddle l)))) id := by
  have hh := primitive_Ioc_window_counts_poisson H T C MI n hn (fun _ : Fin 1=>0) (fun _=>t)
    (fun _=>bot_le) (fun i j hij=>(hij (Subsingleton.elim _ _)).elim) l hl
  have hv : (fun g (X : G.Moduli g (n g) (fun _=>0)) (_ : Fin 1)=>
      (primitiveLengthPointProcess H X).count ℝ≥0 (nnrealPrefixWindow t))=
      fun g (X : G.Moduli g (n g) (fun _=>0))=>windowCountVector ℝ≥0
      (fun _ : Fin 1=>lengthIocWindow 0 t) (primitiveLengthPointProcess H X) := by
    funext g X i
    exact pointMeasure_prefix_count_eq_Ioc_zero _ (primitiveLengthPointProcess_singleton_zero H X) t
  rw [hv]
  have hr : windowRates ℝ≥0 (generalPlanarDensityLengthIntensity P l) (fun _ : Fin 1=>lengthIocWindow 0 t)=
      fun _ : Fin 1=>Real.toNNReal ((t:ℝ)^2*generalPlanarTotalWeight P (planarDensitySaddle l)) := by
    funext i
    simp only [windowRates,lengthIocWindow,general_planar_density_length_intensity_Ioc,
      NNReal.coe_zero,zero_pow two_ne_zero,sub_zero,ENNReal.ofReal,ENNReal.toNNReal_coe]
  rw [hr] at hh
  exact hh

include C MI in
theorem primitive_minimum_length_limit
    (n : ℕ→ℕ) (hn : Tendsto (fun g:ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (l : ℝ≥0∞) (hl : Tendsto (fun g:ℕ=>ENNReal.ofReal ((n g:ℝ)/g)) atTop (𝓝 l)) (t : ℝ) (ht : 0≤t) :
    Tendsto (fun g=>(wpProbability G g (n g)).real {X : G.Moduli g (n g) (fun _=>0)|
      ENNReal.ofReal t<ENNReal.ofReal (Real.sqrt (pantsScale g (n g)))*primitiveMinimumLength H X})
      atTop (𝓝 (Real.exp (-generalPlanarTotalWeight P (planarDensitySaddle l)*t^2))) := by
  let tNN : ℝ≥0 := ⟨t,ht⟩
  have hmeas : ∀g,Measurable (fun X : G.Moduli g (n g) (fun _=>0)=>fun _ : Fin 1=>
      (primitiveLengthPointProcess H X).count ℝ≥0 (nnrealPrefixWindow tNN)) := by
    intro g
    exact measurable_pi_lambda (fun _ : Fin 1=>primitiveLengthPointProcess_prefix_count_measurable H tNN)
  have hv := poisson_void_probability_tendsto (fun g=>wpProbability G g (n g))
    (fun g (X : G.Moduli g (n g) (fun _=>0)) (_ : Fin 1)=>
      (primitiveLengthPointProcess H X).count ℝ≥0 (nnrealPrefixWindow tNN))
    (fun _ : Fin 1=>Real.toNNReal ((tNN:ℝ)^2*generalPlanarTotalWeight P (planarDensitySaddle l)))
    (Eventually.of_forall hmeas) (primitive_prefix_counts_poisson H T C MI n hn l hl tNN) (0:Fin 1)
  have hW := general_planar_total_weight_nonneg P _ (planar_density_saddle_mem l).1
  have he : -(((tNN:ℝ)^2*generalPlanarTotalWeight P (planarDensitySaddle l)).toNNReal:ℝ)=
      -generalPlanarTotalWeight P (planarDensitySaddle l)*t^2 := by
    rw [Real.coe_toNNReal _ (mul_nonneg (sq_nonneg _) hW)]
    change -(t^2*generalPlanarTotalWeight P (planarDensitySaddle l))=
      -generalPlanarTotalWeight P (planarDensitySaddle l)*t^2
    ring
  rw [he] at hv
  apply hv.congr'
  filter_upwards [pantsLengthScale_eventually_eq_sqrt n hn] with g hg
  apply congrArg (fun B=>(wpProbability G g (n g)).real B)
  ext X
  change (primitiveLengthPointProcess H X).count ℝ≥0 (nnrealPrefixWindow tNN)=0 ↔_
  rw [primitiveLengthPointProcess_prefix_count_eq_minimum_void H X tNN,hg]
  rw [←ENNReal.ofReal_coe_nnreal]
  rfl

end WP.RandomGeometry
