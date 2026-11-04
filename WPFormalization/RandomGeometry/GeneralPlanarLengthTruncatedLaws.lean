import WPFormalization.RandomGeometry.GeneralPlanarLengthProjectionCounts
import WPFormalization.RandomGeometry.GeneralPlanarMarkedMoments
import WPFormalization.RandomGeometry.GeneralPlanarDensityLengthRates
import WPFormalization.Probability.FinitePoissonSums

/-! Finite type truncations of actual length counts have the independent
Poisson laws with the summed original cusp-type rates. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)

def generalPlanarLengthTruncatedCounts {g n d : ℕ} (K : ℕ) (lo hi : Fin d→ℝ≥0)
    (X : G.Moduli g n (fun _=>0)) : Fin d→ℕ :=
  fun j=>∑k : Fin (K+2),(planarLengthPointMeasure H X (pantsLengthScale g n)
    (pantsLengthScale_pos g n) k.val).count ℝ≥0 (lengthIocWindow (lo j) (hi j))

lemma generalPlanarLengthTruncatedCounts_measurable {g n d : ℕ} (K : ℕ) (lo hi : Fin d→ℝ≥0) :
    Measurable (generalPlanarLengthTruncatedCounts H (g:=g) (n:=n) K lo hi) := by
  apply Measurable.of_eval
  intro j
  exact Finset.measurable_sum _ (fun k _=>generalPlanarLengthPointMeasure_Ioc_count_measurable H _
    (pantsLengthScale_pos g n) k.val (lo j) (hi j))

lemma generalPlanar_flat_marked_disjoint {d K : ℕ} (e : Fin (d*K)≃Fin d×Fin K) (lo hi : Fin d→ℝ≥0)
    (hdis : Pairwise (fun j m=>Disjoint (Ioc (lo j) (hi j)) (Ioc (lo m) (hi m)))) :
    Pairwise (fun a b=>(e a).2.val≠(e b).2.val ∨
      Disjoint (Ioc (lo (e a).1) (hi (e a).1)) (Ioc (lo (e b).1) (hi (e b).1))) := by
  intro a b hab
  by_cases hf : (e a).1=(e b).1
  · left
    intro he
    apply hab
    apply e.injective
    exact Prod.ext hf (Fin.ext he)
  · exact Or.inr (hdis hf)

include C MI in
theorem generalPlanar_length_truncated_counts_poisson {d : ℕ} (K : ℕ)
    (n : ℕ→ℕ) (hn : Tendsto (fun g:ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (lo hi : Fin d→ℝ≥0) (hab : ∀j,lo j≤hi j)
    (hdis : Pairwise (fun j m=>Disjoint (Ioc (lo j) (hi j)) (Ioc (lo m) (hi m))))
    (l : ℝ≥0∞) (hl : Tendsto (fun g:ℕ=>ENNReal.ofReal ((n g:ℝ)/g)) atTop (𝓝 l)) :
    LawConverges (fun g=>wpProbability G g (n g))
      (fun g=>generalPlanarLengthTruncatedCounts H (g:=g) (n:=n g) K lo hi)
      (productPoissonMeasure (fun j=>generalPlanarDensityLengthTruncatedRate P l K
        (Real.toNNReal ((hi j:ℝ)^2-(lo j:ℝ)^2)))) id := by
  let e : Fin (d*(K+2))≃Fin d×Fin (K+2) := finProdFinEquiv.symm
  let k : Fin (d*(K+2))→ℕ := fun i=>(e i).2.val
  let low := fun i=>lo (e i).1
  let high := fun i=>hi (e i).1
  let X := fun g (X : G.Moduli g (n g) (fun _=>0))=>windowCountVector (ℝ≥0×ℕ)
    (fun i=>generalPlanarTypeWindow (k i) (lengthIocWindow (low i) (high i))) (generalPlanarMarkedLengthPointProcess H X)
  let rates := windowRates (ℝ≥0×ℕ) (generalPlanarDensityIntensity P l)
    (fun i=>generalPlanarTypeWindow (k i) (lengthIocWindow (low i) (high i)))
  have hm := generalPlanar_marked_Ioc_mixed_factorials H T C MI k n hn low high
    (fun i=>hab _) (generalPlanar_flat_marked_disjoint e lo hi hdis) l hl
  have hx : ∀g,Measurable (X g) := by
    intro g
    apply Measurable.of_eval
    intro i
    simp only [X,windowCountVector,generalPlanarMarkedLengthPointProcess_rectangle_count]
    exact generalPlanarLengthPointMeasure_Ioc_count_measurable H _ (pantsLengthScale_pos g (n g)) _ _ _
  have hLaw : LawConverges (fun g=>wpProbability G g (n g)) X (productPoissonMeasure rates) id := by
    apply factorial_moments_poisson_nonneg
    · exact WP.Spectral.wpProbability_eventually_probability P G n
        ((pants_fast_cusps_tendsto_atTop n hn).eventually_ge_atTop 1)
    · exact Eventually.of_forall (fun g=>(hx g).aemeasurable)
    · exact hm
  have hs := lawConverges_flat_poisson_block_sums (fun g=>wpProbability G g (n g)) X e rates hLaw
  have hXsum : (fun g (ω : G.Moduli g (n g) (fun _=>0)) j=>∑a : Fin (K+2),X g ω (e.symm (j,a)))=
      fun g=>generalPlanarLengthTruncatedCounts H (g:=g) (n:=n g) K lo hi := by
    funext g ω j
    simp only [X,windowCountVector,generalPlanarMarkedLengthPointProcess_rectangle_count,
      k,low,high,e.apply_symm_apply,generalPlanarLengthTruncatedCounts]
  have hrsum : (fun j=>∑a : Fin (K+2),rates (e.symm (j,a)))=
      fun j=>generalPlanarDensityLengthTruncatedRate P l K (Real.toNNReal ((hi j:ℝ)^2-(lo j:ℝ)^2)) := by
    funext j
    apply Finset.sum_congr rfl
    intro a _
    have hd : 0≤(hi j:ℝ)^2-(lo j:ℝ)^2 := by
      nlinarith [(lo j).property,(hi j).property,show (lo j:ℝ)≤(hi j:ℝ) from hab j]
    simp only [rates,windowRates,generalPlanarTypeWindow,lengthIocWindow,k,low,high,e.apply_symm_apply,
      general_planar_density_intensity_Ioc,ENNReal.ofReal,ENNReal.toNNReal_coe,
      Real.coe_toNNReal _ hd]
  rw [hXsum,hrsum] at hs
  exact hs

end WP.RandomGeometry
