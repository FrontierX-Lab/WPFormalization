import WPFormalization.Probability.SigmaMixture
import WPFormalization.RandomGeometry.BoltzmannCuspConvergence
import WPFormalization.External.HyperbolicCurveGeometry
import WPFormalization.Geometry.Bridge
import WPFormalization.Volumes.DiagonalChainAlgebra

noncomputable section
universe u v
namespace WP.BoltzmannWp
open Set MeasureTheory Filter External
open scoped ENNReal Topology
variable {P : PsiTheory}

/-- The actual disjoint union of WP moduli spaces, with the cusp count retained. -/
abbrev Surface (G : WeilPeterssonGeometry.{u,v} P) (g : ℕ) :=
  Sigma (fun n : ℕ => G.Moduli g n (fun _ => 0))

def countPMF (P : PsiTheory) (g : ℕ) (x : ℝ) : PMF ℕ :=
  (BoltzmannCusp.extendedLaw P g x : Measure ℕ).toPMF

lemma countPMF_toMeasure (P : PsiTheory) (g : ℕ) (x : ℝ) :
    (countPMF P g x).toMeasure=(BoltzmannCusp.extendedLaw P g x:Measure ℕ) :=
  Measure.toPMF_toMeasure _

/-- Actual WP conditional sampling with the genuine normalized coefficient law.
For the finitely many genera where positivity is not yet proved, this remains
a measure; probability and the original Boltzmann interpretation are proved
uniformly for every sufficiently large genus below. -/
def wpMixture (G : WeilPeterssonGeometry.{u,v} P) (g : ℕ) (x : ℝ) :
    Measure (Surface G g) :=
  Probability.sigmaMixture (countPMF P g x) (fun n=>wpProbability G g n)

lemma wpMixture_apply (G : WeilPeterssonGeometry.{u,v} P) (g : ℕ) (x : ℝ)
    (s : Set (Surface G g)) (hs : MeasurableSet s) :
    wpMixture G g x s=∑'n,countPMF P g x n*wpProbability G g n ((@Sigma.mk ℕ (fun m=>G.Moduli g m (fun _=>0)) n)⁻¹' s) :=
  Probability.sigmaMixture_apply _ _ s hs

lemma cuspVolume_positive_eventually (P : PsiTheory) (G : WeilPeterssonGeometry.{u,v} P) :
    ∃ N : ℕ,∀ g≥N,∀ n : ℕ,0<cuspVolume G g n := by
  obtain ⟨N,hN⟩ := TightConnected.connected_unmarked_positive_eventually P
  refine ⟨N+2,?_⟩
  intro g hg n
  rw [Geometry.cuspVolume_eq_volumeModel P G g n (by unfold Stable;omega)]
  by_cases hn : n=0
  · subst n
    have hp:=hN g (by omega) 0 ⟨le_rfl,Analysis.xCritical_pos_parameter⟩
    have he:=marked_realCoeff_volume P g 0 0
    simp only [iteratedDeriv_zero,Nat.zero_add,Nat.factorial_zero,Nat.cast_one,mul_one] at he
    have hc : 0<realCoeff (Phi P g) 0 := by simpa only [markedF,realCoeff,coeff,
      iteratedDeriv_zero,Nat.factorial_zero,Nat.cast_one,div_one,Complex.ofReal_zero] using hp
    rw [he] at hc
    exact (div_pos_iff_of_pos_right (by positivity : 0<(2*Real.pi^2)^dimension g 0)).mp hc
  · exact diagonal_volume_pos_nonempty P g n (by omega) (by unfold Stable;omega)

lemma wpProbability_probability_eventually (P : PsiTheory) (G : WeilPeterssonGeometry.{u,v} P) :
    ∃ N : ℕ,∀ g≥N,∀ n : ℕ,IsProbabilityMeasure (wpProbability G g n) := by
  obtain ⟨N,hN⟩ := cuspVolume_positive_eventually P G
  refine ⟨N+2,?_⟩
  intro g hg n
  apply wpProbability_isProbabilityMeasure G g n (by unfold Stable;omega)
  intro hz
  have hp:=hN g (by omega) n
  simpa only [cuspVolume,wpVolume,hz,ENNReal.toReal_zero,lt_self_iff_false] using hp

lemma wpMixture_probability_eventually (P : PsiTheory) (G : WeilPeterssonGeometry.{u,v} P) :
    ∃ N : ℕ,∀ g≥N,∀ x : ℝ,IsProbabilityMeasure (wpMixture G g x) := by
  obtain ⟨N,hN⟩ := wpProbability_probability_eventually P G
  refine ⟨N,?_⟩
  intro g hg x
  letI : ∀n,IsProbabilityMeasure (wpProbability G g n) := fun n=>hN g hg n
  exact Probability.sigmaMixture_isProbabilityMeasure _ _

lemma wpMixture_count_marginal_eventually (P : PsiTheory) (G : WeilPeterssonGeometry.{u,v} P) :
    ∃ N : ℕ,∀ g≥N,∀ x : ℝ,
      (wpMixture G g x).map Sigma.fst=(BoltzmannCusp.extendedLaw P g x:Measure ℕ) := by
  obtain ⟨N,hN⟩ := wpProbability_probability_eventually P G
  refine ⟨N,?_⟩
  intro g hg x
  letI : ∀n,IsProbabilityMeasure (wpProbability G g n) := fun n=>hN g hg n
  exact (Probability.sigmaMixture_map_fst _ _).trans (countPMF_toMeasure P g x)

lemma wpMixture_count_weights_eventually (P : PsiTheory) (G : WeilPeterssonGeometry.{u,v} P) :
    ∃ N : ℕ,∀ g≥N,∀ x∈Ico (0:ℝ) xCritical,∀ n : ℕ,
      wpMixture G g x {X|X.fst=n}=ENNReal.ofReal (BoltzmannCusp.weight P g x n) := by
  obtain ⟨N₁,hN₁⟩ := wpMixture_count_marginal_eventually P G
  obtain ⟨N₂,hN₂⟩ := BoltzmannCusp.extendedLaw_original_weights_eventually P
  refine ⟨N₁+N₂,?_⟩
  intro g hg x hx n
  have he := congrArg (fun μ:Measure ℕ=>μ {n}) (hN₁ g (by omega) x)
  rw [Measure.map_apply Probability.measurable_sigmaFst (measurableSet_singleton n)] at he
  exact he.trans (hN₂ g (by omega) x hx n)
end WP.BoltzmannWp
namespace WP.BoltzmannWp
open Set MeasureTheory Filter External
open scoped ENNReal Topology
variable {P : PsiTheory}
lemma countPMF_zero_apply (P:PsiTheory) (g n:ℕ) :
    countPMF P g 0 n=if n=0 then 1 else 0 := by
  rw [countPMF,Measure.toPMF_apply,BoltzmannCusp.extendedLaw_zero]
  by_cases hn : n=0 <;> simp [hn,eq_comm]
lemma wpMixture_zero (G:WeilPeterssonGeometry.{u,v} P) (g:ℕ) :
    wpMixture G g 0=(wpProbability G g 0).map
      (@Sigma.mk ℕ (fun n=>G.Moduli g n (fun _=>0)) 0) := by
  ext s hs
  rw [wpMixture_apply G g 0 s hs,Measure.map_apply (Probability.measurable_sigmaMk 0) hs]
  simp only [countPMF_zero_apply,ite_mul,one_mul,zero_mul]
  simp
lemma wpMixture_count_preimage_eventually (P:PsiTheory) (G:WeilPeterssonGeometry.{u,v} P) :
    ∃ N:ℕ,∀ g≥N,∀ x:ℝ,∀ s:Set ℕ,
      wpMixture G g x (Sigma.fst⁻¹' s)=(BoltzmannCusp.extendedLaw P g x:Measure ℕ) s := by
  obtain ⟨N,hN⟩ := wpMixture_count_marginal_eventually P G
  refine ⟨N,?_⟩
  intro g hg x s
  have he:=congrArg (fun μ:Measure ℕ=>μ s) (hN g hg x)
  rw [Measure.map_apply Probability.measurable_sigmaFst (Set.to_countable s).measurableSet] at he
  exact he
lemma wpMixture_scale_in_probability (P:PsiTheory) (G:WeilPeterssonGeometry.{u,v} P)
    (gs:ℕ→ℕ) (hg:Tendsto gs atTop atTop) (xs:ℕ→ℝ)
    (hx:∀j,xs j∈Ico (0:ℝ) xCritical) (ε:ℝ) (hε:0<ε) :
    Tendsto (fun j=>wpMixture G (gs j) (xs j)
      {X|ε≤|tightScale ((X.fst:ℝ)/(gs j:ℝ))/tightParameterScale (inverseY (xs j))-1|})
      atTop (𝓝 0) := by
  obtain ⟨N,hN⟩ := wpMixture_count_preimage_eventually P G
  apply (BoltzmannCusp.extendedLaw_scale_in_probability P gs hg xs hx ε hε).congr'
  filter_upwards [hg.eventually_ge_atTop N] with j hj
  exact (hN (gs j) hj (xs j) _).symm
end WP.BoltzmannWp
