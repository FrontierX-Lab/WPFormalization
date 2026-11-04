import WPFormalization.RandomGeometry.GeneralPlanarStarIntegralBounds
import WPFormalization.RandomGeometry.PrimitivePlanarTypeComparison
import WPFormalization.External.BoundaryVolumeComparison

/-! Uniform one-star boundary control from the sourced stable genus-zero
boundary-volume comparison, keeping its geometry parameter explicit. -/
noncomputable section
universe u v
namespace WP.RandomGeometry
open WP.External MeasureTheory Set

lemma general_planar_one_star_window_weight (L : ℝ) (hL : 0≤L) :
    pantsWindowWeight 1 (fun _ => Icc 0 L)=L^2/2 := by
  rw [pants_window_weight_eq_product]
  simp only [Fin.prod_univ_one]
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le hL,integral_id]
  simp

lemma general_planar_one_star_window_base_eq (P : PsiTheory) (g n k : ℕ)
    (L : ℝ) (hL : 0≤L) :
    generalPlanarStarWindowBase P g n 1 (fun _ => k) (fun _ => Icc 0 L)=
      primitivePlanarFirstBase P g n k L := by
  rw [generalPlanarStarWindowBase,general_planar_one_star_window_weight L hL]
  simp only [Fin.sum_univ_one,Fin.prod_univ_one]
  rw [Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul]
  have hk : (k.factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero k
  unfold primitivePlanarFirstBase
  field_simp

lemma general_planar_one_star_correction_upper (P : PsiTheory)
    (G : WeilPeterssonGeometry.{u,v} P) (k : ℕ) (hk : 2≤k) (L : ℝ) (hL : 0≤L) :
    generalPlanarStarBoundaryCorrection P 1 (fun _ => k) L≤Real.exp L := by
  have hv : 0<volumeModel P 0 (k+1) :=
    diagonal_volume_pos_nonempty P 0 (k+1) (by omega) (by unfold Stable;omega)
  have hs : Stable 0 (k+1) := by unfold Stable;omega
  have hb := wpVolume_genus_zero_boundary_upper P G (k+1) (by omega)
    (generalPlanarStarLeafLengths k L) (generalPlanarStarLeafLengths_nonneg k L hL)
  rw [WP.Geometry.wpVolume_eq_boundaryVolumeModel P G 0 (k+1) _ hs
    (generalPlanarStarLeafLengths_nonneg k L hL),
    WP.Geometry.cuspVolume_eq_volumeModel P G 0 (k+1) hs] at hb
  have hsum : (∑j,generalPlanarStarLeafLengths k L j)=L := by
    simp [generalPlanarStarLeafLengths,Fin.sum_univ_add]
  rw [hsum] at hb
  have hr : boundaryVolumeModel P 0 (k+1) (generalPlanarStarLeafLengths k L)/
      volumeModel P 0 (k+1)≤Real.exp (L/2) := (div_le_iff₀ hv).mpr hb
  unfold generalPlanarStarBoundaryCorrection generalPlanarStarLeafCorrection
  simp only [Nat.cast_one,one_mul,Fin.prod_univ_one]
  calc
    _≤Real.exp (L/2)*Real.exp (L/2) := mul_le_mul_of_nonneg_left hr (Real.exp_pos _).le
    _=Real.exp L := by rw [←Real.exp_add];congr 1;ring

/-- Uniform over all planar side sizes through k=n, including the one-cusp
root. The only additional classical input is the sourced stable genus-zero
boundary-volume comparison; its genuine geometry object remains explicit. -/
theorem general_planar_one_star_window_cut_upper (P : PsiTheory)
    (G : WeilPeterssonGeometry.{u,v} P) (g n k : ℕ) (hg : 2≤g) (hn : 2≤n)
    (hk : 2≤k) (_hkn : k≤n) (L : ℝ) (hL : 0≤L) :
    generalPlanarStarWindowCut P g n 1 (fun _ => k) (fun _ => Icc 0 L)≤
      Real.exp L*primitivePlanarFirstBase P g n k L := by
  have hm : 1≤n-(∑_i : Fin 1,k)+1 := by simp only [Fin.sum_univ_one];omega
  have hb := (general_planar_star_window_cut_bounds P g n 1 (fun _ => k)
    (by omega) (by omega) hm (fun _ => hk) (fun _ => Icc 0 L)
    (fun _ => measurableSet_Icc) L (fun _ => fun _ h => h)).2
  have hc := general_planar_one_star_correction_upper P G k hk L hL
  have hbase : 0≤primitivePlanarFirstBase P g n k L := by
    have hv0 : 0<volumeModel P 0 (k+1) :=
      diagonal_volume_pos_nonempty P 0 (k+1) (by omega) (by unfold Stable;omega)
    have hvr : 0<volumeModel P g (n-k+1) :=
      diagonal_volume_pos_nonempty P g (n-k+1) (by omega) (by unfold Stable;omega)
    have hvn : 0<volumeModel P g n :=
      diagonal_volume_pos_nonempty P g n (by omega) (by unfold Stable;omega)
    unfold primitivePlanarFirstBase
    positivity
  rw [general_planar_one_star_window_base_eq P g n k L hL] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right hc hbase)

end WP.RandomGeometry
