import WPFormalization.Statements.VolumeRatios
import WPFormalization.Analysis.VolumeProfileRegular
import WPFormalization.Volumes.DiagonalChainAlgebra

/-! The all-cusp nonseparating volume ratio is uniformly bounded. This is a
local consequence of the proved uniform volume-ratio theorem. -/
noncomputable section
namespace WP.RandomGeometry
open Filter Set
open scoped Topology

lemma primitive_profileB_ge_one (l : ℝ) (hl : 0≤l) : 1≤profileB l := by
  have hY := (Analysis.densityY_spec l hl).1
  have hr := r_pos _ hY
  have hu := Analysis.r_le_pi _ hY
  rw [Analysis.volume_profile_B_physical l hl,Analysis.volumeProfileBPhysical]
  apply (one_le_div (mul_pos (by norm_num) hr)).mpr
  nlinarith [hY.1]

lemma primitive_nonseparating_volume_ratio_bound (P : PsiTheory) :
    ∃N : ℕ,∀g : ℕ,N≤g→∀n : ℕ,
      0<volumeModel P g n ∧ volumeModel P (g-1) (n+2)/volumeModel P g n≤2 := by
  obtain ⟨C,hC,N,hbound⟩ := volume_ratios P
  obtain ⟨M,hM⟩ := exists_nat_gt (2*C)
  refine ⟨max 2 (max N M),?_⟩
  intro g hg n
  have hg2 : 2≤g := (le_max_left _ _).trans hg
  have hgN : N≤g := (le_max_left _ _).trans ((le_max_right _ _).trans hg)
  have hgM : M≤g := (le_max_right _ _).trans ((le_max_right _ _).trans hg)
  have hgR : (0:ℝ)<g := by exact_mod_cast (show 0<g by omega)
  have hCM : 2*C<(g:ℝ) := hM.trans_le (by exact_mod_cast hgM)
  have he := (abs_le.mp ((hbound g hgN).1 n).1).1
  have hB := primitive_profileB_ge_one ((n:ℝ)/g) (by positivity)
  have hchild := diagonal_volume_pos_nonempty P (g-1) (n+2) (by omega) (by unfold Stable;omega)
  have hsmall : C/(g:ℝ)≤1/2 := (div_le_iff₀ hgR).mpr (by linarith)
  have hnorm : (1:ℝ)/2≤(volumeModel P g n/volumeModel P (g-1) (n+2))/profileB ((n:ℝ)/g) := by
    linarith
  have hprof : 0<profileB ((n:ℝ)/g) := by linarith
  have hrat : (1:ℝ)/2≤volumeModel P g n/volumeModel P (g-1) (n+2) := by
    have hp := (le_div_iff₀ hprof).mp hnorm
    linarith
  have hpar : 0<volumeModel P g n := by
    have hm := (le_div_iff₀ hchild).mp hrat
    linarith
  refine ⟨hpar,?_⟩
  apply (div_le_iff₀ hpar).mpr
  have hm := (le_div_iff₀ hchild).mp hrat
  linarith

end WP.RandomGeometry
