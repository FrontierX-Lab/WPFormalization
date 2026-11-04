import WPFormalization.JT.AbelKernel
import WPFormalization.JT.AbelSinh
import WPFormalization.JT.AbelCritical

/-! The complete Abel density identity and cubic critical edge of §15.1.
Maxfield--Turiaci (2021), Eq. (3.50), at alpha=0 and 2 gamma=1 supplies the
physical interpretation of the defining Abel integral.  No matrix model or
all-genus summation is constructed here, and no physical-model identity is
assumed in any of the following mathematical deductions. -/
noncomputable section
namespace WP.JT
open MeasureTheory Filter Set Asymptotics
open scoped Topology

lemma abel_density_undeformed (E : ℝ) (hE : 0 ≤ E) :
    abelDensity 0 E = Real.sinh (2 * Real.pi * Real.sqrt E) / (4 * Real.pi^2) := by
  have he := abel_density_kernel 0 E hE
  simp only [edgeEnergy, neg_zero, zero_div, zero_add, Complex.ofReal_zero] at he
  rw [he]
  exact kernel_density_zero_parameter E hE

lemma abel_density_critical :
    (fun q : ℝ => abelDensity y₀ (edgeEnergy y₀ + q) -
      (Real.pi * Analysis.criticalB / 3) * q ^ (3/2 : ℝ))
      =O[𝓝[>] (0 : ℝ)] (fun q : ℝ => q ^ (5/2 : ℝ)) := by
  apply critical_kernel_density_isBigO.congr' ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with q hq
    rw [abel_density_kernel y₀ q (le_of_lt hq)]
    rfl
  · exact Filter.Eventually.of_forall fun _ => rfl

lemma abel_density_critical_bound :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ q ∈ Icc (0 : ℝ) δ,
      |abelDensity y₀ (edgeEnergy y₀ + q) -
        (Real.pi * Analysis.criticalB / 3) * q ^ (3/2 : ℝ)| ≤ C * q ^ (5/2 : ℝ) := by
  obtain ⟨C,δ,hC,hδ,hbound⟩ := critical_kernel_density_bound
  refine ⟨C,δ,hC,hδ,?_⟩
  intro q hq
  rw [abel_density_kernel y₀ q hq.1]
  exact hbound q hq

@[blueprint "eq:jt-abel-critical-edge"]
theorem jt_abel_critical_edge : AbelDensityConclusion :=
  ⟨abel_density_intervalIntegrable, abel_density_kernel_at,
    abel_density_undeformed, Analysis.criticalB_pos, abel_density_critical⟩

end WP.JT
