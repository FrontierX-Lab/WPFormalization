import WPFormalization.RandomGeometry.PantsLengthPointProcess
import WPFormalization.RandomGeometry.PantsFactorialMomentLimits
import WPFormalization.RandomGeometry.QuadraticLengthIntensity

/-! Mixed factorial moments of the genuine actual length point process. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

lemma nnreal_Ioc_pairwise_disjoint_real {ι : Type*} (lo hi : ι → ℝ≥0)
    (hdis : Pairwise (fun j k => Disjoint (Ioc (lo j) (hi j)) (Ioc (lo k) (hi k)))) :
    Pairwise (fun j k => Disjoint (Ioc (lo j : ℝ) (hi j : ℝ))
      (Ioc (lo k : ℝ) (hi k : ℝ))) := by
  intro j k hjk
  apply Set.disjoint_left.mpr
  intro x hxj hxk
  let y : ℝ≥0 := ⟨x, (lo j).property.trans hxj.1.le⟩
  exact Set.disjoint_left.mp (hdis hjk) (show y ∈ Ioc (lo j) (hi j) from hxj)
    (show y ∈ Ioc (lo k) (hi k) from hxk)

lemma pants_mixed_window_upper_le_cap {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (q : ℝ) (hi : ι → ℝ) (hhi : ∀j,0≤hi j)
    (j : ι) (haj : 0<a j) :
    hi j/Real.sqrt q ≤ pantsMixedScaledWindowCap a q hi := by
  classical
  let i : Fin (∑j,a j) := mixedSlotsEquiv a ⟨j,⟨0,haj⟩⟩
  have hs := Finset.single_le_sum
    (fun k (_ : k ∈ Finset.univ) => hhi ((mixedSlotsEquiv a).symm k).1)
    (Finset.mem_univ i)
  have he : ((mixedSlotsEquiv a).symm i).1=j := by simp [i]
  rw [he] at hs
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg q)
  change hi j ≤ 1+∑k : Fin (∑j,a j),hi ((mixedSlotsEquiv a).symm k).1
  linarith

variable {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P)
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)

include C MI in
lemma pants_point_process_Ioc_mixed_moments {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (n : ℕ → ℕ)
    (hnfast : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop atTop)
    (lo hi : ι → ℝ≥0) (horder : ∀j,lo j≤hi j)
    (hdis : Pairwise (fun j k => Disjoint (Ioc (lo j) (hi j)) (Ioc (lo k) (hi k)))) :
    Tendsto (fun g => ∫⁻X : G.Moduli g (n g) (fun _ => 0),
      ∏j, (((pantsLengthPointProcess H X).count ℝ≥0 (lengthIocWindow (lo j) (hi j))).descFactorial
        (a j) : ℝ≥0∞) ∂wpProbability G g (n g)) atTop
      (𝓝 (∏j, ENNReal.ofReal ((hi j : ℝ)^2-(lo j : ℝ)^2)^(a j))) := by
  have hh := pants_fixed_mixed_Ioc_lintegral_moments_of_fast_cusps G H T C MI a n hnfast
    (fun j => (lo j : ℝ)) (fun j => (hi j : ℝ)) (fun j => (lo j).property)
    (fun j => show (lo j : ℝ)≤(hi j : ℝ) from horder j)
    (nnreal_Ioc_pairwise_disjoint_real lo hi hdis)
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
    have hc := planarLengthPointMeasure_Ioc_count_eq_windowCount H X
      (pantsLengthScale g (n g)) (pantsLengthScale_pos g (n g)) _ (lo j) (hi j) hcut
    change _ = (((planarLengthPointMeasure H X (pantsLengthScale g (n g))
      (pantsLengthScale_pos g (n g)) 2).count ℝ≥0 (lengthIocWindow (lo j) (hi j))).descFactorial
        (a j) : ℝ≥0∞)
    rw [hc,hscale]

include C MI in
lemma pants_point_process_Ioc_mixedFactorialMomentLimit (d : ℕ) (n : ℕ → ℕ)
    (hnfast : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop atTop)
    (lo hi : Fin d → ℝ≥0) (horder : ∀j,lo j≤hi j)
    (hdis : Pairwise (fun j k => Disjoint (Ioc (lo j) (hi j)) (Ioc (lo k) (hi k)))) :
    MixedFactorialMomentLimit (fun g => wpProbability G g (n g))
      (fun g X => windowCountVector ℝ≥0 (fun j => lengthIocWindow (lo j) (hi j))
        (pantsLengthPointProcess H X))
      (windowRates ℝ≥0 quadraticLengthIntensity (fun j => lengthIocWindow (lo j) (hi j))) := by
  intro a
  simpa only [windowCountVector,windowRates_coe,quadraticLengthIntensity_Ioc,lengthIocWindow]
    using pants_point_process_Ioc_mixed_moments G H T C MI a n hnfast lo hi horder hdis

end WP.RandomGeometry
