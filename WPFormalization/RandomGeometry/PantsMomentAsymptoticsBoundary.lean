import WPFormalization.Volumes.BoundaryPolynomial

/-! A uniform short-boundary comparison from the actual mixed-intersection
polynomial. This uses the already proved marked profile bounds, not a new
geometric or moment axiom. -/
noncomputable section
namespace WP.RandomGeometry
open Set Filter
open scoped Topology

lemma pants_sinh_le_mul_exp (u : ℝ) : Real.sinh u ≤ u*Real.exp u := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-2*u)) (Real.exp_pos u).le
  have he : Real.exp (-2*u)*Real.exp u = Real.exp (-u) := by
    rw [←Real.exp_add]
    congr 1
    ring
  rw [he] at h
  rw [Real.sinh_eq]
  nlinarith

lemma pants_boundaryFactor_zero_le_exp (L : ℝ) (hL : 0 ≤ L) :
    boundaryFactor 0 L ≤ Real.exp (L/2) := by
  rw [(boundary_factor_endpoints L).1]
  by_cases hzero : L=0
  · simp [hzero]
  · rw [if_neg hzero]
    apply (div_le_iff₀ (by positivity : 0 < L/2)).2
    simpa only [mul_comm] using pants_sinh_le_mul_exp (L/2)

/-- The classical boundary comparison is here a proved consequence of the
actual volume polynomial, uniformly in every genus g≥1 and cusp count n≥1. -/
lemma pants_boundary_volume_bounds (P : PsiTheory) (g n : ℕ)
    (hg : 1 ≤ g) (hn : 1 ≤ n) (L : Fin n → ℝ) (hL : ∀ i, 0 ≤ L i) :
    1 ≤ boundaryVolumeModel P g n L/volumeModel P g n ∧
      boundaryVolumeModel P g n L/volumeModel P g n ≤ Real.exp ((∑ i, L i)/2) := by
  classical
  constructor
  · rw [boundaryVolumeModel_div_eq_profile_sum]
    have hz : (fun _ : Fin n => 0) ∈ degreeTuples g n := by
      rw [mem_degreeTuples_iff]
      simp
    have hs := Finset.single_le_sum
      (s := degreeTuples g n)
      (f := fun d => profile P g (List.ofFn d) 0*boundaryDegreeWeight n L d)
      (fun d _ => mul_nonneg (profile_zero_bounds P g n hg hn d).1
        (boundaryDegreeWeight_nonneg n L d)) hz
    have he : profile P g (List.ofFn (fun _ : Fin n => 0)) 0 = 1 := by
      rw [List.ofFn_const]
      exact profile_replicate_zero P g n hn (by unfold Stable;omega) 0 ⟨le_rfl,y₀_pos.le⟩
    rw [he] at hs
    simpa [boundaryDegreeWeight] using hs
  · have hloss : 0 ≤ ∑' d, boundaryProfileLoss P g n L d := by
      apply tsum_nonneg
      intro d
      exact mul_nonneg (by linarith [(profile_zero_bounds P g n hg hn d).2])
        (boundaryDegreeWeight_nonneg n L d)
    rw [boundaryProfileLoss_tsum_eq P g n hg hn L] at hloss
    have hprod : (∏ i, boundaryFactor 0 (L i)) ≤ ∏ i, Real.exp (L i/2) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact (boundaryFactor_pos 0 (L i)).le
      · intro i _
        exact pants_boundaryFactor_zero_le_exp (L i) (hL i)
    have hexp : (∏ i, Real.exp (L i/2)) = Real.exp ((∑ i, L i)/2) := by
      rw [←Real.exp_sum,Finset.sum_div]
    rw [hexp] at hprod
    linarith

end WP.RandomGeometry
