import WPFormalization.RandomGeometry.GeneralPlanarStarIntegralBoundary

/-! Fixed-type boundary integrals have a genuinely vanishing absolute error. -/
noncomputable section
namespace WP.RandomGeometry
open MeasureTheory Set Filter
open scoped Topology

lemma general_planar_star_window_integral_bounds (P : PsiTheory) (g n r : ℕ)
    (k : Fin r → ℕ) (hg : 1 ≤ g) (hm : 1 ≤ n-(∑i,k i)+r) (hk : ∀i,2 ≤ k i)
    (I : Fin r → Set ℝ) (hI : ∀i,MeasurableSet (I i)) (L : ℝ)
    (hIL : ∀i,I i ⊆ Icc 0 L) :
    (volumeModel P g (n-(∑i,k i)+r)*∏i,volumeModel P 0 (k i+1))*pantsWindowWeight r I ≤
      generalPlanarStarWindowIntegral P g n r k I ∧
    generalPlanarStarWindowIntegral P g n r k I ≤
      generalPlanarStarBoundaryCorrection P r k L *
        ((volumeModel P g (n-(∑i,k i)+r)*∏i,volumeModel P 0 (k i+1))*pantsWindowWeight r I) := by
  let C := volumeModel P g (n-(∑i,k i)+r)*∏i,volumeModel P 0 (k i+1)
  let S := generalPlanarStarBoundaryCorrection P r k L
  have hb : IntegrableOn (fun x : Fin r → ℝ => C*∏i,x i) {x | ∀i,x i ∈ I i} :=
    pants_window_integrable_continuous r I L hIL _ (by fun_prop)
  have hu : IntegrableOn (fun x : Fin r → ℝ => S*C*∏i,x i) {x | ∀i,x i ∈ I i} :=
    pants_window_integrable_continuous r I L hIL _ (by fun_prop)
  have hi := generalPlanarStarWindowIntegral_integrable P g n r k I L hIL
  have hpoint : ∀ᵐ x ∂volume.restrict {x : Fin r → ℝ | ∀i,x i ∈ I i},
      C*∏i,x i ≤ generalPlanarStarVolumeIntegrand P g n r k x*∏i,x i ∧
      generalPlanarStarVolumeIntegrand P g n r k x*∏i,x i ≤ S*C*∏i,x i := by
    have hset : MeasurableSet {x : Fin r → ℝ | ∀i,x i ∈ I i} := by
      have he : {x : Fin r → ℝ | ∀i,x i ∈ I i}=Set.univ.pi I := by ext x;simp
      rw [he]
      exact MeasurableSet.univ_pi hI
    filter_upwards [ae_restrict_mem hset] with x hx
    have hx0 : ∀i,0 ≤ x i := fun i => (hIL i (hx i)).1
    have hxL : ∀i,x i ≤ L := fun i => (hIL i (hx i)).2
    have hw : 0 ≤ ∏i,x i := Finset.prod_nonneg (fun i _ => hx0 i)
    have hp := general_planar_star_integrand_bounds P g n r k hg hm hk x L hx0 hxL
    exact ⟨mul_le_mul_of_nonneg_right hp.1 hw,mul_le_mul_of_nonneg_right hp.2 hw⟩
  constructor
  · have h := integral_mono_ae hb hi (hpoint.mono fun _ hx => hx.1)
    simpa only [generalPlanarStarWindowIntegral,pantsWindowWeight,integral_const_mul,C] using h
  · have h := integral_mono_ae hi hu (hpoint.mono fun _ hx => hx.2)
    simpa only [generalPlanarStarWindowIntegral,pantsWindowWeight,integral_const_mul,C,S,mul_assoc] using h

lemma general_planar_star_window_cut_bounds (P : PsiTheory) (g n r : ℕ)
    (k : Fin r → ℕ) (hg : 1 ≤ g) (hn : 1 ≤ n) (hm : 1 ≤ n-(∑i,k i)+r)
    (hk : ∀i,2 ≤ k i) (I : Fin r → Set ℝ) (hI : ∀i,MeasurableSet (I i))
    (L : ℝ) (hIL : ∀i,I i ⊆ Icc 0 L) :
    generalPlanarStarWindowBase P g n r k I ≤ generalPlanarStarWindowCut P g n r k I ∧
      generalPlanarStarWindowCut P g n r k I ≤
        generalPlanarStarBoundaryCorrection P r k L*generalPlanarStarWindowBase P g n r k I := by
  have hv : 0 < volumeModel P g n :=
    diagonal_volume_pos_nonempty P g n hn (by unfold Stable;omega)
  have ha : 0 ≤ (n.descFactorial (∑i,k i):ℝ)/(volumeModel P g n*∏i,((k i).factorial:ℝ)) := by
    positivity
  have hb := general_planar_star_window_integral_bounds P g n r k hg hm hk I hI L hIL
  unfold generalPlanarStarWindowBase generalPlanarStarWindowCut
  constructor
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb.1 ha
  · have h := mul_le_mul_of_nonneg_left hb.2 ha
    convert h using 1 <;> ring

/-- Internal absolute transfer: the bounded-base input is proved from the
actual fixed-type prefactor at the scaled-window application below. -/
lemma general_planar_star_window_cut_difference (P : PsiTheory) (r : ℕ) (k : Fin r → ℕ)
    (hk : ∀i,2 ≤ k i) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (I : ℕ → Fin r → Set ℝ) (L : ℕ → ℝ) (hL : Tendsto L atTop (𝓝 0))
    (hI : ∀ᶠ g in atTop,∀i,MeasurableSet (I g i))
    (hIL : ∀ᶠ g in atTop,∀i,I g i ⊆ Icc 0 (L g))
    (hb : IsBoundedUnder (· ≤ ·) atTop (fun g => ‖generalPlanarStarWindowBase P g (n g) r k (I g)‖)) :
    Tendsto (fun g => generalPlanarStarWindowCut P g (n g) r k (I g) -
      generalPlanarStarWindowBase P g (n g) r k (I g)) atTop (𝓝 0) := by
  have he := (general_planar_star_boundary_correction_tendsto P r k hk L hL).sub_const 1
  simp only [sub_self] at he
  have ht := he.zero_mul_isBoundedUnder_le hb
  have hbound : ∀ᶠ g in atTop,
      generalPlanarStarWindowBase P g (n g) r k (I g) ≤ generalPlanarStarWindowCut P g (n g) r k (I g) ∧
      generalPlanarStarWindowCut P g (n g) r k (I g) ≤
        generalPlanarStarBoundaryCorrection P r k (L g)*generalPlanarStarWindowBase P g (n g) r k (I g) := by
    filter_upwards [eventually_ge_atTop (1:ℕ),hn.eventually_ge_atTop ((∑i,k i)+1),hI,hIL]
      with g hg hng hIg hILg
    exact general_planar_star_window_cut_bounds P g (n g) r k hg (by omega) (by omega)
      hk (I g) hIg (L g) hILg
  apply squeeze_zero' (hbound.mono fun g h => sub_nonneg.mpr h.1) ?_ ht
  filter_upwards [hbound] with g hg
  linarith only [hg.2]

end WP.RandomGeometry
