import WPFormalization.RandomGeometry.GeneralPlanarStarVolume
import WPFormalization.RandomGeometry.PantsFixedOrderAsymptoticsWindows

/-! Actual finite-dimensional physical boundary integrals for fixed planar types. -/
noncomputable section
namespace WP.RandomGeometry
open MeasureTheory Set

/-- The root and every planar leaf use their actual physical boundary vector. -/
def generalPlanarStarVolumeIntegrand (P : PsiTheory) (g n r : ℕ) (k : Fin r → ℕ)
    (x : Fin r → ℝ) : ℝ :=
  boundaryVolumeModel P g (n-(∑i,k i)+r) (generalPlanarStarRootLengths n r k x) *
    ∏i,boundaryVolumeModel P 0 (k i+1) (generalPlanarStarLeafLengths (k i) (x i))

def generalPlanarStarWindowIntegral (P : PsiTheory) (g n r : ℕ) (k : Fin r → ℕ)
    (I : Fin r → Set ℝ) : ℝ :=
  ∫ x : Fin r → ℝ in {x | ∀i,x i ∈ I i},
    generalPlanarStarVolumeIntegrand P g n r k x * ∏i,x i

/-- Ordered curve slots, with only within-leaf cusp-label permutations removed. -/
def generalPlanarStarWindowCut (P : PsiTheory) (g n r : ℕ) (k : Fin r → ℕ)
    (I : Fin r → Set ℝ) : ℝ :=
  ((n.descFactorial (∑i,k i):ℝ)/(volumeModel P g n * ∏i,((k i).factorial:ℝ))) *
    generalPlanarStarWindowIntegral P g n r k I

/-- The same physical Jacobian and exact label normalization at zero boundary. -/
def generalPlanarStarWindowBase (P : PsiTheory) (g n r : ℕ) (k : Fin r → ℕ)
    (I : Fin r → Set ℝ) : ℝ :=
  ((n.descFactorial (∑i,k i):ℝ)/(volumeModel P g n * ∏i,((k i).factorial:ℝ))) *
    (volumeModel P g (n-(∑i,k i)+r) * ∏i,volumeModel P 0 (k i+1)) * pantsWindowWeight r I

lemma generalPlanarStarRootLengths_continuous (n r : ℕ) (k : Fin r → ℕ) :
    Continuous (generalPlanarStarRootLengths n r k) := by
  apply continuous_pi
  intro j
  refine Fin.addCases (fun a => ?_) (fun i => ?_) j
  · simp only [generalPlanarStarRootLengths,Fin.append_left]
    fun_prop
  · simp only [generalPlanarStarRootLengths,Fin.append_right]
    fun_prop

lemma generalPlanarStarLeafLengths_continuous (k : ℕ) :
    Continuous (generalPlanarStarLeafLengths k) := by
  apply continuous_pi
  intro j
  refine Fin.addCases (fun a => ?_) (fun i => ?_) j
  · simp only [generalPlanarStarLeafLengths,Fin.append_left]
    fun_prop
  · simp only [generalPlanarStarLeafLengths,Fin.append_right]
    fun_prop

lemma general_planar_boundary_polynomial_continuous (P : PsiTheory) (g n : ℕ) :
    Continuous (boundaryVolumeModel P g n) := by
  unfold boundaryVolumeModel
  fun_prop

lemma generalPlanarStarVolumeIntegrand_continuous (P : PsiTheory) (g n r : ℕ)
    (k : Fin r → ℕ) : Continuous (generalPlanarStarVolumeIntegrand P g n r k) := by
  unfold generalPlanarStarVolumeIntegrand
  apply Continuous.mul
  · exact (general_planar_boundary_polynomial_continuous P g _).comp
      (generalPlanarStarRootLengths_continuous n r k)
  · apply continuous_finset_prod
    intro i _
    exact (general_planar_boundary_polynomial_continuous P 0 _).comp
      ((generalPlanarStarLeafLengths_continuous (k i)).comp (continuous_apply i))

lemma generalPlanarStarWindowIntegral_integrable (P : PsiTheory) (g n r : ℕ)
    (k : Fin r → ℕ) (I : Fin r → Set ℝ) (L : ℝ)
    (hI : ∀i,I i ⊆ Icc 0 L) :
    IntegrableOn (fun x => generalPlanarStarVolumeIntegrand P g n r k x * ∏i,x i)
      {x | ∀i,x i ∈ I i} := by
  exact pants_window_integrable_continuous r I L hI _
    ((generalPlanarStarVolumeIntegrand_continuous P g n r k).mul (by fun_prop))

end WP.RandomGeometry
