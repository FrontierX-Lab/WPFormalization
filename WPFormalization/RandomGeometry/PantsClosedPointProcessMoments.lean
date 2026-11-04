import WPFormalization.RandomGeometry.PantsLengthPointProcess
import WPFormalization.RandomGeometry.PantsClosedFactorialMomentLimits
import WPFormalization.RandomGeometry.CurveClosedPointCounts
import WPFormalization.RandomGeometry.PantsPointProcessMoments
import WPFormalization.RandomGeometry.QuadraticLengthIntensity

/-! Mixed factorial moments of the genuine actual length point process. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

lemma nnreal_Icc_pairwise_disjoint_real {ι : Type*} (lo hi : ι → ℝ≥0)
    (hdis : Pairwise (fun j k => Disjoint (Icc (lo j) (hi j)) (Icc (lo k) (hi k)))) :
    Pairwise (fun j k => Disjoint (Icc (lo j : ℝ) (hi j : ℝ))
      (Icc (lo k : ℝ) (hi k : ℝ))) := by
  intro j k hjk
  apply Set.disjoint_left.mpr
  intro x hxj hxk
  let y : ℝ≥0 := ⟨x, (lo j).property.trans hxj.1⟩
  exact Set.disjoint_left.mp (hdis hjk) (show y ∈ Icc (lo j) (hi j) from hxj)
    (show y ∈ Icc (lo k) (hi k) from hxk)

lemma quadraticLengthIntensity_Icc (a b : ℝ≥0) :
    quadraticLengthIntensity (Icc a b)=ENNReal.ofReal ((b : ℝ)^2-(a : ℝ)^2) :=
  (measure_congr (Ioc_ae_eq_Icc (μ:=quadraticLengthIntensity))).symm.trans
    (quadraticLengthIntensity_Ioc a b)

variable {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P)
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)

include C MI in
lemma pants_point_process_Icc_mixed_moments {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (n : ℕ → ℕ)
    (hnfast : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop atTop)
    (lo hi : ι → ℝ≥0) (horder : ∀j,lo j≤hi j)
    (hdis : Pairwise (fun j k => Disjoint (Icc (lo j) (hi j)) (Icc (lo k) (hi k)))) :
    Tendsto (fun g => ∫⁻X : G.Moduli g (n g) (fun _ => 0),
      ∏j, (((pantsLengthPointProcess H X).count ℝ≥0 (lengthIccWindow (lo j) (hi j))).descFactorial
        (a j) : ℝ≥0∞) ∂wpProbability G g (n g)) atTop
      (𝓝 (∏j, ENNReal.ofReal ((hi j : ℝ)^2-(lo j : ℝ)^2)^(a j))) := by
  have hh := pants_fixed_mixed_Icc_lintegral_moments_of_fast_cusps G H T C MI a n hnfast
    (fun j => (lo j : ℝ)) (fun j => (hi j : ℝ)) (fun j => (lo j).property)
    (fun j => show (lo j : ℝ)≤(hi j : ℝ) from horder j)
    (nnreal_Icc_pairwise_disjoint_real lo hi hdis)
  apply hh.congr'
  filter_upwards [pantsLengthScale_eventually_eq_sqrt n hnfast] with g hscale
  apply lintegral_congr_ae
  apply Eventually.of_forall
  intro X
  apply Finset.prod_congr rfl
  intro j _
  by_cases haj : a j=0
  · simp only [haj,Nat.descFactorial_zero]
  · have hcut : (hi j : ℝ)/pantsLengthScale g (n g) ≤
        pantsMixedScaledWindowCap a (pantsScale g (n g)) (fun j => (hi j : ℝ)) := by
      rw [hscale]
      exact pants_mixed_window_upper_le_cap a _ (fun j => (hi j : ℝ))
        (fun j => (hi j).property) j (Nat.pos_of_ne_zero haj)
    have hc := planarLengthPointMeasure_Icc_count_eq_windowCount H X
      (pantsLengthScale g (n g)) (pantsLengthScale_pos g (n g)) _ (lo j) (hi j) hcut
    change _ = (((planarLengthPointMeasure H X (pantsLengthScale g (n g))
      (pantsLengthScale_pos g (n g)) 2).count ℝ≥0 (lengthIccWindow (lo j) (hi j))).descFactorial
        (a j) : ℝ≥0∞)
    rw [hc,hscale]

include C MI in
lemma pants_point_process_Icc_mixedFactorialMomentLimit (d : ℕ) (n : ℕ → ℕ)
    (hnfast : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop atTop)
    (lo hi : Fin d → ℝ≥0) (horder : ∀j,lo j≤hi j)
    (hdis : Pairwise (fun j k => Disjoint (Icc (lo j) (hi j)) (Icc (lo k) (hi k)))) :
    MixedFactorialMomentLimit (fun g => wpProbability G g (n g))
      (fun g X => windowCountVector ℝ≥0 (fun j => lengthIccWindow (lo j) (hi j))
        (pantsLengthPointProcess H X))
      (windowRates ℝ≥0 quadraticLengthIntensity (fun j => lengthIccWindow (lo j) (hi j))) := by
  intro a
  simpa only [windowCountVector,windowRates_coe,quadraticLengthIntensity_Icc,lengthIccWindow]
    using pants_point_process_Icc_mixed_moments G H T C MI a n hnfast lo hi horder hdis

end WP.RandomGeometry
