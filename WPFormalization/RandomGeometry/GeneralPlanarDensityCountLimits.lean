import WPFormalization.RandomGeometry.GeneralPlanarFactorialMomentLimits
import WPFormalization.RandomGeometry.GeneralPlanarDensitySaddle
import WPFormalization.RandomGeometry.GeneralPlanarDensityWeights

/-! Density-parametrized actual planar count limits. The scale here is the
exact coefficient saddle scale q*, whose ratio to the paper's q tends to one. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)

def generalPlanarDensityWindowRates {ι : Type*} (P : PsiTheory)
    (k : ι→ℕ) (lo hi : ι→ℝ) (l : ℝ≥0∞) : ι→ℝ≥0 :=
  fun j=>Real.toNNReal (generalPlanarTypeWeight P (k j) (planarDensitySaddle l)*((hi j)^2-(lo j)^2))

lemma generalPlanar_density_window_rates_eq {ι : Type*} (P : PsiTheory)
    (k : ι→ℕ) (hk : ∀j,2≤k j) (lo hi : ι→ℝ) (l : ℝ≥0∞) :
    generalPlanarDensityWindowRates P k lo hi l=
      generalPlanarFamilyRates P k lo hi (planarDensitySaddle l) := by
  funext j
  simp only [generalPlanarDensityWindowRates,generalPlanarFamilyRates,generalPlanarFamilyRate,
    general_planar_type_weight_formula P (k j) (hk j)]

include C MI in
theorem generalPlanar_density_mixed_factorial_limits {d : ℕ}
    (k : Fin d→ℕ) (hk : ∀j,2≤k j) (n : ℕ→ℕ)
    (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (lo hi : Fin d→ℝ) (hlo : ∀j,0≤lo j) (hab : ∀j,lo j≤hi j)
    (hdis : Pairwise (fun j m=>k j≠k m ∨ Disjoint (Ioc (lo j) (hi j)) (Ioc (lo m) (hi m))))
    (l : ℝ≥0∞) (hl : Tendsto (fun g : ℕ=>ENNReal.ofReal ((n g:ℝ)/g)) atTop (𝓝 l)) :
    MixedFactorialMomentLimit (fun g=>wpProbability G g (n g))
      (fun g=>generalPlanarFamilyCounts H g (n g) k lo hi)
      (generalPlanarDensityWindowRates P k lo hi l) := by
  rw [generalPlanar_density_window_rates_eq P k hk]
  intro a
  exact generalPlanar_fixed_mixed_windows_lintegral_moments H T C MI k hk a n hn lo hi hlo hab hdis
    _ (planar_density_saddle_mem l).1 (primitive_saddle_tendsto_density_fast n hn l hl)

include C MI in
theorem generalPlanar_density_type_window_counts_poisson {d : ℕ}
    (k : Fin d→ℕ) (hk : ∀j,2≤k j) (n : ℕ→ℕ)
    (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (lo hi : Fin d→ℝ) (hlo : ∀j,0≤lo j) (hab : ∀j,lo j≤hi j)
    (hdis : Pairwise (fun j m=>k j≠k m ∨ Disjoint (Ioc (lo j) (hi j)) (Ioc (lo m) (hi m))))
    (l : ℝ≥0∞) (hl : Tendsto (fun g : ℕ=>ENNReal.ofReal ((n g:ℝ)/g)) atTop (𝓝 l)) :
    LawConverges (fun g=>wpProbability G g (n g))
      (fun g=>generalPlanarFamilyCounts H g (n g) k lo hi)
      (productPoissonMeasure (generalPlanarDensityWindowRates P k lo hi l)) id := by
  rw [generalPlanar_density_window_rates_eq P k hk]
  exact generalPlanar_fixed_type_window_counts_poisson H T C MI k hk n hn lo hi hlo hab hdis
    _ (planar_density_saddle_mem l).1 (primitive_saddle_tendsto_density_fast n hn l hl)

end WP.RandomGeometry
