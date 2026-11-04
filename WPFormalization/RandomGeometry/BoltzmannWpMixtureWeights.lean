import WPFormalization.RandomGeometry.BoltzmannCuspConvergence
import WPFormalization.Geometry.Bridge
import WPFormalization.Volumes.VolumeRatiosEndpoints
noncomputable section
universe u v
namespace WP.BoltzmannWp
open Set MeasureTheory Filter External
open scoped Topology
variable {P : PsiTheory}

def muCritical : ℝ := xCritical/(2*Real.pi^2)
def parameter (μ : ℝ) : ℝ := (2*Real.pi^2)*μ

def rawWeight (G : WeilPeterssonGeometry.{u,v} P) (g : ℕ) (μ : ℝ) (n : ℕ) : ℝ :=
  cuspVolume G g n*μ^n/(n.factorial:ℝ)

def partition (G : WeilPeterssonGeometry.{u,v} P) (g : ℕ) (μ : ℝ) : ℝ :=
  ∑' n:ℕ,rawWeight G g μ n

lemma parameter_physical (μ : ℝ) (hμ : μ∈Ico (0:ℝ) muCritical) :
    parameter μ∈Ico (0:ℝ) xCritical := by
  have hp : 0<2*Real.pi^2 := by positivity
  refine ⟨mul_nonneg hp.le hμ.1,?_⟩
  have hh := (lt_div_iff₀ hp).mp hμ.2
  simpa only [parameter,mul_comm] using hh

lemma rawWeight_eq_coeff (G : WeilPeterssonGeometry.{u,v} P) (g : ℕ) (hg : 2≤g)
    (μ : ℝ) (n : ℕ) :
    rawWeight G g μ n=(2*Real.pi^2)^dimension g 0*
      (realCoeff (Phi P g) n*(parameter μ)^n) := by
  have he := marked_realCoeff_volume P g 0 n
  simp only [iteratedDeriv_zero,Nat.add_zero] at he
  have hd : dimension g n=dimension g 0+n := by unfold dimension;omega
  rw [rawWeight,Geometry.cuspVolume_eq_volumeModel P G g n (by unfold Stable;omega),he,hd]
  unfold parameter
  rw [pow_add,mul_pow]
  field_simp
  <;>ring

lemma rawWeight_hasSum (G : WeilPeterssonGeometry.{u,v} P) (g : ℕ) (hg : 2≤g)
    (μ : ℝ) (hμ : μ∈Ico (0:ℝ) muCritical) :
    HasSum (rawWeight G g μ) ((2*Real.pi^2)^dimension g 0*markedF P g 0 (parameter μ)) := by
  have hx := parameter_physical μ hμ
  have hs := TightConnected.connected_real_taylor_hasSum _ (parameter μ)
    (marked_generating_hasSum P g 0 ((parameter μ:ℝ):ℂ)
      (by rw [Complex.norm_of_nonneg hx.1];exact hx.2))
  change HasSum _ (markedF P g 0 (parameter μ)) at hs
  convert hs.mul_left ((2*Real.pi^2)^dimension g 0) using 1
  funext n
  exact rawWeight_eq_coeff G g hg μ n

lemma partition_eq_phi (G : WeilPeterssonGeometry.{u,v} P) (g : ℕ) (hg : 2≤g)
    (μ : ℝ) (hμ : μ∈Ico (0:ℝ) muCritical) :
    partition G g μ=(2*Real.pi^2)^dimension g 0*markedF P g 0 (parameter μ) :=
  (rawWeight_hasSum G g hg μ hμ).tsum_eq

lemma normalized_rawWeight_eq (G : WeilPeterssonGeometry.{u,v} P) (g : ℕ) (hg : 2≤g)
    (μ : ℝ) (hμ : μ∈Ico (0:ℝ) muCritical)
    (hf : markedF P g 0 (parameter μ)≠0) (n : ℕ) :
    rawWeight G g μ n/partition G g μ=BoltzmannCusp.weight P g (parameter μ) n := by
  rw [rawWeight_eq_coeff G g hg μ n,partition_eq_phi G g hg μ hμ]
  unfold BoltzmannCusp.weight
  field_simp

lemma partition_positive_eventually (P : PsiTheory) (G : WeilPeterssonGeometry.{u,v} P) :
    ∃ N:ℕ,∀ g≥N,∀ μ∈Ico (0:ℝ) muCritical,0<partition G g μ := by
  obtain ⟨N,hN⟩ := TightConnected.connected_unmarked_positive_eventually P
  refine ⟨N+2,?_⟩
  intro g hg μ hμ
  rw [partition_eq_phi G g (by omega) μ hμ]
  exact mul_pos (by positivity) (hN g (by omega) _ (parameter_physical μ hμ))
end WP.BoltzmannWp
