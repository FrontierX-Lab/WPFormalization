import WPFormalization.Volumes.BoundaryBoxBridge
import WPFormalization.Marked.ExternalStringBoundary

/-! The proved external string flow has exactly the original boundary-volume
coefficients, including arbitrarily many additional zero boundary lengths. -/
noncomputable section
namespace WP.BoundaryConvolution
open Set Filter
open scoped Topology

lemma externalOddWeight_zero_prefix (q p : ℕ) (b : Fin p → ℕ) :
    externalOddWeight (List.replicate q 0 ++ List.ofFn b) =
      ∏ i, (oddFactorial (b i):ℝ) := by
  have hodd : oddFactorial 0=1 := by norm_num [oddFactorial]
  simp [externalOddWeight,List.map_append,List.map_ofFn,List.prod_ofFn,hodd]

lemma stringBoundaryAmplitude_zero_eq_boundary_scaled (P : PsiTheory) (g q p : ℕ)
    (L : Fin p → ℝ) :
    stringBoundaryAmplitude P g (fun i => (L i)^2/(4*Real.pi^2)) q 0 =
      boundaryVolumeModel P g (q+p) (Fin.append (fun _ : Fin q => 0) L) /
        (2*Real.pi^2)^(dimension g (q+p)) := by
  have hh := boundaryVolumeModel_zero_prefix_scaled_box P g q p
    (dimension g (q+p)) le_rfl L
  unfold stringBoundaryAmplitude externalStringAmplitude externalMarkedAmplitude
  simp only [realTranslationWeight_zero,externalOddWeight_zero_prefix]
  exact hh.symm

lemma boundaryVolumeModel_real_egf (P : PsiTheory) (g p : ℕ) (hg : 2 ≤ g)
    (hp : 1 ≤ p) (L : Fin p → ℝ) (x : ℝ) (hx : x ∈ Ico 0 xCritical) :
    HasSum (fun q : ℕ =>
      boundaryVolumeModel P g (q+p) (Fin.append (fun _ : Fin q => 0) L) /
        ((2*Real.pi^2)^(dimension g (q+p))*(q.factorial:ℝ))*x^q)
      (stringBoundaryAmplitude P g (fun i => (L i)^2/(4*Real.pi^2)) 0 (inverseY x)) := by
  have hs := stringBoundaryAmplitude_real_hasSum P g hg hp
    (fun i => (L i)^2/(4*Real.pi^2)) (by intro i; positivity) x hx
  convert hs using 1
  ext q
  rw [stringBoundaryAmplitude_zero_eq_boundary_scaled]
  ring

end WP.BoundaryConvolution
