import WPFormalization.RandomGeometry.GeneralPlanarMarkedPointProcess
import WPFormalization.RandomGeometry.GeneralPlanarOriginalAllTypeMoments
import WPFormalization.RandomGeometry.PantsPointProcessMoments

/-! Genuine mixed factorial moments for every rational marked window, at the
original scale, including absent types, zero rates and the origin. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)

lemma generalPlanar_Ioc_marked_windows_disjoint {d : ℕ} (k : Fin d→ℕ) (lo hi : Fin d→ℝ≥0)
    (hdis : Pairwise (fun j m=>k j≠k m ∨ Disjoint (Ioc (lo j) (hi j)) (Ioc (lo m) (hi m)))) :
    Pairwise (fun j m=>k j≠k m ∨ Disjoint (Ioc (lo j:ℝ) (hi j:ℝ)) (Ioc (lo m:ℝ) (hi m:ℝ))) := by
  intro j m hjm
  rcases hdis hjm with hk|hd
  · exact Or.inl hk
  · right
    apply Set.disjoint_left.mpr
    intro x hx hy
    let y : ℝ≥0 := ⟨x,(lo j).property.trans hx.1.le⟩
    exact Set.disjoint_left.mp hd (show y∈Ioc (lo j) (hi j) from hx) (show y∈Ioc (lo m) (hi m) from hy)

include C MI in
lemma generalPlanar_marked_Ioc_mixed_factorials {d : ℕ} (k : Fin d→ℕ)
    (n : ℕ→ℕ) (hn : Tendsto (fun g:ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (lo hi : Fin d→ℝ≥0) (hab : ∀j,lo j≤hi j)
    (hdis : Pairwise (fun j m=>k j≠k m ∨ Disjoint (Ioc (lo j) (hi j)) (Ioc (lo m) (hi m))))
    (l : ℝ≥0∞) (hl : Tendsto (fun g:ℕ=>ENNReal.ofReal ((n g:ℝ)/g)) atTop (𝓝 l)) :
    MixedFactorialMomentLimit (fun g=>wpProbability G g (n g))
      (fun g X=>windowCountVector (ℝ≥0×ℕ) (fun j=>generalPlanarTypeWindow (k j) (lengthIocWindow (lo j) (hi j)))
        (generalPlanarMarkedLengthPointProcess H X))
      (windowRates (ℝ≥0×ℕ) (generalPlanarDensityIntensity P l)
        (fun j=>generalPlanarTypeWindow (k j) (lengthIocWindow (lo j) (hi j)))) := by
  have hm := generalPlanar_original_all_type_mixed_factorial_limits H T C MI k n hn
    (fun j=>(lo j:ℝ)) (fun j=>(hi j:ℝ)) (fun j=>(lo j).property) (fun j=>hab j)
    (generalPlanar_Ioc_marked_windows_disjoint k lo hi hdis) l hl
  have hr : generalPlanarDensityWindowRates P k (fun j=>(lo j:ℝ)) (fun j=>(hi j:ℝ)) l=
      windowRates (ℝ≥0×ℕ) (generalPlanarDensityIntensity P l)
        (fun j=>generalPlanarTypeWindow (k j) (lengthIocWindow (lo j) (hi j))) := by
    funext j
    simp only [windowRates,generalPlanarTypeWindow,lengthIocWindow,
      general_planar_density_intensity_Ioc,generalPlanarDensityWindowRates,
      ENNReal.ofReal,ENNReal.toNNReal_coe,generalPlanarDensityTypeWeight,mul_comm]
  rw [hr] at hm
  intro a
  apply (hm a).congr'
  filter_upwards [pantsLengthScale_eventually_eq_sqrt n hn] with g hscale
  apply lintegral_congr_ae
  apply Eventually.of_forall
  intro X
  apply Finset.prod_congr rfl
  intro j _
  have hcut : (hi j:ℝ)/pantsLengthScale g (n g)≤
      pantsScaledWindowCap (pantsScale g (n g)) (fun j=>(hi j:ℝ)) := by
    rw [hscale]
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    have hs : (hi j:ℝ)≤∑i,(hi i:ℝ) := Finset.single_le_sum
      (fun i (_:i∈Finset.univ)=>show 0≤(hi i:ℝ) from (hi i).property) (Finset.mem_univ j)
    change (hi j:ℝ)≤1+∑i,(hi i:ℝ)
    linarith
  have hc := generalPlanarLengthPointMeasure_Ioc_count_eq_windowCount H X
    (pantsLengthScale g (n g)) (pantsLengthScale_pos g (n g)) (k j)
    (pantsScaledWindowCap (pantsScale g (n g)) (fun j=>(hi j:ℝ))) (lo j) (hi j) hcut
  simp only [windowCountVector,generalPlanarMarkedLengthPointProcess_rectangle_count]
  rw [hc]
  simp only [hscale,generalPlanarOriginalFamilyCounts,generalPlanarOriginalFamilyWindows]

lemma generalPlanar_marked_rational_canonical_disjoint {d : ℕ} (k : Fin d→ℕ) (a b : Fin d→ℚ)
    (hdis : DisjointWindows (ℝ≥0×ℕ) (fun j=>generalPlanarTypeWindow (k j) (nnrealRationalWindow (a j) (b j)))) :
    Pairwise (fun j m=>k j≠k m ∨ Disjoint
      (Ioc (min (Real.toNNReal (a j)) (Real.toNNReal (b j))) (Real.toNNReal (b j)))
      (Ioc (min (Real.toNNReal (a m)) (Real.toNNReal (b m))) (Real.toNNReal (b m)))) := by
  intro j m hjm
  by_cases hk : k j=k m
  · right
    have hd := (general_planar_type_window_disjoint_iff (k j) (k m) _ _).mp (hdis hjm) hk
    rw [←nnreal_rational_window_sdiff_zero,←nnreal_rational_window_sdiff_zero]
    exact hd.mono sdiff_subset sdiff_subset
  · exact Or.inl hk

include C MI in
lemma generalPlanar_marked_rational_mixed_factorials {d : ℕ} (k : Fin d→ℕ)
    (n : ℕ→ℕ) (hn : Tendsto (fun g:ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (a b : Fin d→ℚ)
    (hdis : DisjointWindows (ℝ≥0×ℕ) (fun j=>generalPlanarTypeWindow (k j) (nnrealRationalWindow (a j) (b j))))
    (l : ℝ≥0∞) (hl : Tendsto (fun g:ℕ=>ENNReal.ofReal ((n g:ℝ)/g)) atTop (𝓝 l)) :
    MixedFactorialMomentLimit (fun g=>wpProbability G g (n g))
      (fun g X=>windowCountVector (ℝ≥0×ℕ) (fun j=>generalPlanarTypeWindow (k j) (nnrealRationalWindow (a j) (b j)))
        (generalPlanarMarkedLengthPointProcess H X))
      (windowRates (ℝ≥0×ℕ) (generalPlanarDensityIntensity P l)
        (fun j=>generalPlanarTypeWindow (k j) (nnrealRationalWindow (a j) (b j)))) := by
  let lo := fun j=>min (Real.toNNReal (a j)) (Real.toNNReal (b j))
  let hi := fun j=>Real.toNNReal (b j)
  have hvec : (fun g (X : G.Moduli g (n g) (fun _=>0))=>windowCountVector (ℝ≥0×ℕ)
      (fun j=>generalPlanarTypeWindow (k j) (nnrealRationalWindow (a j) (b j))) (generalPlanarMarkedLengthPointProcess H X))=
      fun g (X : G.Moduli g (n g) (fun _=>0))=>windowCountVector (ℝ≥0×ℕ)
      (fun j=>generalPlanarTypeWindow (k j) (lengthIocWindow (lo j) (hi j))) (generalPlanarMarkedLengthPointProcess H X) := by
    funext g X j
    simp only [windowCountVector,generalPlanarMarkedLengthPointProcess_rectangle_count]
    exact pointMeasure_count_rational_window_eq_canonical_Ioc _
      (curveNNLengthMeasure_singleton_zero H X _ (pantsLengthScale_pos g (n g)) _) (a j) (b j)
  have hr : windowRates (ℝ≥0×ℕ) (generalPlanarDensityIntensity P l)
      (fun j=>generalPlanarTypeWindow (k j) (nnrealRationalWindow (a j) (b j)))=
      windowRates (ℝ≥0×ℕ) (generalPlanarDensityIntensity P l)
      (fun j=>generalPlanarTypeWindow (k j) (lengthIocWindow (lo j) (hi j))) := by
    funext j
    apply congrArg ENNReal.toNNReal
    change generalPlanarDensityIntensity P l ((nnrealRationalWindow (a j) (b j)).carrier×ˢ{k j})=
      generalPlanarDensityIntensity P l (Ioc (lo j) (hi j)×ˢ{k j})
    rw [general_planar_density_intensity_rect,general_planar_density_intensity_rect,
      measure_rational_window_eq_canonical_Ioc _ (measure_singleton _) (a j) (b j)]
  rw [hvec,hr]
  exact generalPlanar_marked_Ioc_mixed_factorials H T C MI k n hn lo hi
    (fun j=>min_le_right _ _) (generalPlanar_marked_rational_canonical_disjoint k a b hdis) l hl

include C MI in
lemma generalPlanar_marked_semiring_mixed_factorials
    (n : ℕ→ℕ) (hn : Tendsto (fun g:ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (l : ℝ≥0∞) (hl : Tendsto (fun g:ℕ=>ENNReal.ofReal ((n g:ℝ)/g)) atTop (𝓝 l))
    (d : ℕ) (B : Fin d→RelCompactBorelWindow (ℝ≥0×ℕ))
    (hB : ∀i,B i∈generalPlanarRationalWindows) (hdis : DisjointWindows (ℝ≥0×ℕ) B) :
    MixedFactorialMomentLimit (fun g=>wpProbability G g (n g))
      (fun g X=>windowCountVector (ℝ≥0×ℕ) B (generalPlanarMarkedLengthPointProcess H X))
      (windowRates (ℝ≥0×ℕ) (generalPlanarDensityIntensity P l) B) := by
  choose z hz using hB
  have he : B=fun j=>generalPlanarTypeWindow (z j).1 (nnrealRationalWindow (z j).2.1 (z j).2.2) := by
    funext j
    exact (hz j).symm
  subst B
  exact generalPlanar_marked_rational_mixed_factorials H T C MI
    (fun j=>(z j).1) n hn (fun j=>(z j).2.1) (fun j=>(z j).2.2) hdis l hl

end WP.RandomGeometry
