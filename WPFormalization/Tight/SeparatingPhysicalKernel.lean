import WPFormalization.Tight.SeparatingCutKernel
import WPFormalization.Tight.SeparatingNormalization
import WPFormalization.Geometry.Bridge

noncomputable section
namespace WP.TightSeparating
open Set Filter Finset PositiveConvolution External
open scoped Topology BigOperators

lemma unmarked_realCoeff_volume (P : PsiTheory) (g n : ℕ) :
    realCoeff (Phi P g) n = volumeModel P g n/
      ((2*Real.pi^2)^(dimension g n)*(n.factorial : ℝ)) := by
  rw [realCoeff,WP.coeff,Phi_iteratedDeriv_zero]
  have he : ((shifted P g (List.replicate n 0) 0 : ℂ)/(n.factorial : ℂ)).re =
      shifted P g (List.replicate n 0) 0/(n.factorial : ℝ) := by norm_cast
  rw [he]
  simp only [volumeModel,mixedBracket,List.sum_replicate,nsmul_zero,pow_zero,one_mul,
    deficit,List.length_replicate,Nat.sub_zero]
  field_simp [Real.pi_ne_zero]

/-- The true physical kernel/geometric volume ratio equals the canonical
coefficient ratio with precisely the P^(-k) integration cost. -/
lemma tight_cut_kernel_volume_ratio {P : PsiTheory} {G : WeilPeterssonGeometry P}
    (T : TightRegions G) (BZ : BuddZonneveldTransform G T)
    (g k n : ℕ) (D : MulticurveCutData 0 k)
    (hk : 1 ≤ k) (hg : 2 ≤ g) (hconn : D.ConnectedWithin univ)
    (hs : ∀ i, Stable (D.genus i) (D.boundaryCount i))
    (heuler : (∑ i, D.genus i)+k+1=g+D.components)
    (x : Fin k → ℝ) (hx : ∀ i, 0 ≤ x i) :
    D.tightCutKernel T (fun i => Fin.elim0 i) (fun _ : Fin n => 0) x / cuspVolume G g n =
      (realCoeff (cutProductG P D.genus D.boundaryCount
        (D.tightProtectedLengths (fun i => Fin.elim0 i) x)) n/realCoeff (Phi P g) n)/
          (2*Real.pi^2)^k := by
  have hdim : dimension g n=dimension g 0+n := by unfold dimension;omega
  have hV : cuspVolume G g n =
      ((2*Real.pi^2)^(dimension g 0+n)*(n.factorial : ℝ))*realCoeff (Phi P g) n := by
    rw [Geometry.cuspVolume_eq_volumeModel P G g n (by unfold Stable;omega),
      unmarked_realCoeff_volume,hdim]
    field_simp
  rw [hV,div_mul_eq_div_div,
    tight_cut_kernel_coefficient T BZ g k n D hk hg hconn hs heuler x hx]
  ring

/-- The box integration/Jacobian removes the entire remaining parameter r.
This is the scalar form used after the actual orbit integral has been bounded. -/
lemma separating_physical_box_cancellation (Y : ℝ) (hY : Y ∈ Ico (0 : ℝ) y₀)
    (k : ℕ) (C L : ℝ) :
    (C*(r Y)^k/(2*Real.pi^2)^k)*(L/tightParameterScale Y)^(2*k) =
      C*L^(2*k)/(4 : ℝ)^k := by
  rw [div_pow]
  have he := separating_physical_normalization Y hY k
  calc
    _ = (C*L^(2*k))*((r Y)^k/((2*Real.pi^2)^k*tightParameterScale Y^(2*k))) := by ring
    _ = _ := by rw [he];ring

end WP.TightSeparating
