import WPFormalization.External.WeilPeterssonGeometry

/-! Geometric-to-numerical bridges from mature external identities.
Every geometric family remains an explicit parameter. No instance is chosen.
The finite numerical mixed transform is proved upstream. The geometric classes,
classical KMZ relation and volume polynomial remain explicit external parameters.
-/
noncomputable section
universe u v
namespace WP.Geometry
open WP.External

/- The classical cohomological mixed bracket matches the fixed numerical model.
No asymptotic or positivity assumption is introduced. -/
theorem geometricBracket_eq_model (P : PsiTheory) (R : IntersectionRealization.{u} P)
    (g n : ℕ) (d : Fin n → ℕ) (hst : Stable g n)
    (hd : ∑ i, d i ≤ dimension g n) :
    geometricBracket (R.classes g n) d = mixedBracket P g (List.ofFn d) := by
  have hm := mixed_transform P g (List.ofFn d)
    (by simpa only [List.length_ofFn] using hst)
    (by simpa only [List.sum_ofFn, List.length_ofFn] using hd)
  have hk := R.kappa_psi_transform g n d hst hd
  have ho : (∏ i : Fin n, (oddFactorial (d i) : ℝ)) =
      ((List.ofFn d).map (fun k => (oddFactorial k : ℝ))).prod := by
    simp only [List.map_ofFn, List.prod_ofFn, Function.comp_apply]
  unfold geometricBracket
  rw [if_pos ⟨hst, hd⟩]
  dsimp only
  rw [hk, ho]
  change _ = mixedBracket P g (List.ofFn d)
  have hscale : (4 : ℝ)^(List.ofFn d).sum *
      (2*Real.pi^2)^(deficit g (List.ofFn d)) ≠ 0 := by
    positivity
  change mixedBracket P g (List.ofFn d) /
    ((4 : ℝ)^(List.ofFn d).sum*(2*Real.pi^2)^(deficit g (List.ofFn d))) =
      ((List.ofFn d).map (fun k => (oddFactorial k : ℝ))).prod *
      kappaPsiSum P g (List.ofFn d) at hm
  have heq := (div_eq_iff hscale).mp hm
  calc
    _ = ((List.ofFn d).map (fun k => (oddFactorial k : ℝ))).prod *
        kappaPsiSum P g (List.ofFn d) *
        ((4 : ℝ)^(∑ i, d i)*(2*Real.pi^2)^(dimension g n-∑ i, d i)) := by ring
    _ = mixedBracket P g (List.ofFn d) := by
      simpa only [List.sum_ofFn, List.length_ofFn, deficit] using heq.symm

/- The boundary polynomial is transported, rather than redefining geometric volume
as the numerical polynomial. The finite polynomial law itself is a classical field. -/
theorem wpVolume_eq_boundaryVolumeModel (P : PsiTheory) (G : WeilPeterssonGeometry.{u,v} P)
    (g n : ℕ) (L : Fin n → ℝ) (hst : Stable g n) (hL : ∀ i, 0 ≤ L i) :
    wpVolume G g n L = boundaryVolumeModel P g n L := by
  rw [wpVolume, G.volume_polynomial g n L hst hL]
  unfold boundaryVolumeModel
  apply Finset.sum_congr rfl
  intro d hd
  have hdegree : ∑ i, d i ≤ dimension g n := by
    exact (Finset.mem_filter.mp hd).2
  rw [geometricBracket_eq_model P G.toIntersectionRealization g n d hst hdegree]

/- Evaluation of the finite boundary polynomial at the cusp vector. -/
theorem boundaryVolumeModel_zero (P : PsiTheory) (g n : ℕ) :
    boundaryVolumeModel P g n (fun _ => 0) = volumeModel P g n := by
  let z : Fin n → ℕ := fun _ => 0
  have hz : z ∈ degreeTuples g n := by
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_image.mpr
      exact ⟨(fun _ => (0 : Fin (dimension g n+1))), Finset.mem_univ _, rfl⟩
    · simp [z]
  unfold boundaryVolumeModel
  rw [Finset.sum_eq_single z]
  · simp [z, volumeModel]
  · intro d hd hdz
    have hi : ∃ i, d i ≠ 0 := by
      by_contra! h
      apply hdz
      funext i
      exact h i
    obtain ⟨i, hi⟩ := hi
    have hp : (∏ j : Fin n, (0 : ℝ)^(2*d j) /
        ((4 : ℝ)^(d j)*(2*d j+1).factorial)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
    simp [hp]
  · exact fun h => (h hz).elim

theorem cuspVolume_eq_volumeModel (P : PsiTheory) (G : WeilPeterssonGeometry.{u,v} P)
    (g n : ℕ) (hst : Stable g n) : cuspVolume G g n = volumeModel P g n := by
  rw [cuspVolume, wpVolume_eq_boundaryVolumeModel P G g n _ hst (by simp),
    boundaryVolumeModel_zero]

end WP.Geometry
