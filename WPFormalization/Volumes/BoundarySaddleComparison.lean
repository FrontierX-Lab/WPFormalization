import WPFormalization.Volumes.BoundaryCharacteristicL1
import WPFormalization.Volumes.BoundarySaddle
import WPFormalization.Volumes.BoundarySequentialComparison
import WPFormalization.Volumes.BoundaryPrefixUniform
import WPFormalization.Marked.ExternalBoundaryDensityContinuity
noncomputable section
namespace WP.BoundaryConvolution
open Set Filter MeasureTheory
open scoped Topology

lemma boundary_prefix_sequential_positive (P:PsiTheory)(p:ℕ)(hp:1≤p)(L₀:ℝ)(hL₀:0≤L₀)
    (gs qs:ℕ→ℕ)(Ls:ℕ→Fin p→ℝ)
    (hg:Tendsto gs atTop atTop)(hq:Tendsto qs atTop atTop)
    (hg2:∀j,2≤gs j)(hq1:∀j,1≤qs j)(hL:∀j i,Ls j i∈Icc 0 L₀) :
    Tendsto (fun j=>boundaryPrefixError P p (gs j) (qs j) (Ls j)) atTop (𝓝 0) := by
  let xs:ℕ→ℝ:=fun j=>boundarySaddle (gs j) p (qs j)
  have hs (j:ℕ):xs j∈Ioo (0:ℝ) xCritical ∧
      (complexity (gs j) p:ℝ)*Psi (xs j)=(qs j:ℝ) ∧
      inverseY (xs j)=densityY (2*(qs j:ℝ)/(complexity (gs j) p:ℝ)):=
    boundarySaddle_spec (gs j) p (qs j) (hg2 j) (hq1 j)
  have hmu:Tendsto (fun j=>(complexity (gs j) p:ℝ)*Psi (xs j)) atTop atTop:=by
    have he:(fun j=>(complexity (gs j) p:ℝ)*Psi (xs j))=(fun j=>(qs j:ℝ)):=by
      funext j
      exact (hs j).2.1
    rw [he]
    exact tendsto_natCast_atTop_atTop.comp hq
  have hL1:=boundary_characteristic_l1_tendsto P p hp L₀ hL₀ gs hg xs (fun j=>(hs j).1) Ls hL hmu
  have hratio:=boundary_volume_ratio_tendsto_of_l1 P p hp L₀ hL₀ gs qs xs Ls hg
    (fun j=>(hs j).1) hL hmu (fun j=>(hs j).2.1) hL1
  have hdens:=boundaryFactor_product_density_shift_tendsto p L₀ gs (fun j=>qs j+p) Ls hg
    (fun j=>by omega) hL
  have hconvert (j:ℕ):inverseY (xs j)=
      densityY (2*(((qs j+p:ℕ):ℝ)-(p:ℝ))/(2*(gs j:ℝ)-2+p)):=by
    rw [(hs j).2.2,boundary_effective_density_eq (gs j) p (qs j) (hg2 j)]
  have hprod:=hratio.mul hdens
  simp only [one_mul] at hprod
  have htarget:Tendsto (fun j=>boundaryPrefixError P p (gs j) (qs j) (Ls j)+1) atTop (𝓝 1):=by
    apply hprod.congr'
    apply Eventually.of_forall
    intro j
    dsimp only
    rw [←hconvert j]
    unfold boundaryPrefixError
    have hb:(∏i,boundaryFactor (inverseY (xs j)) (Ls j i))≠0:=
      Finset.prod_ne_zero_iff.mpr (fun i hi=>(boundaryFactor_pos _ _).ne')
    field_simp [hb]
    <;>ring
  have ht:=htarget.sub_const 1
  simpa only [add_sub_cancel_right,sub_self] using ht

lemma boundary_prefix_sequential (P:PsiTheory)(p:ℕ)(hp:1≤p)(L₀:ℝ)(hL₀:0≤L₀)
    (gs qs:ℕ→ℕ)(Ls:ℕ→Fin p→ℝ)
    (hg:Tendsto gs atTop atTop)(hq:Tendsto qs atTop atTop)(hL:∀j i,Ls j i∈Icc 0 L₀) :
    Tendsto (fun j=>boundaryPrefixError P p (gs j) (qs j) (Ls j)) atTop (𝓝 0) := by
  let gs':ℕ→ℕ:=fun j=>max 2 (gs j)
  let qs':ℕ→ℕ:=fun j=>max 1 (qs j)
  have hg':Tendsto gs' atTop atTop:=tendsto_atTop_mono (fun j=>le_max_right _ _) hg
  have hq':Tendsto qs' atTop atTop:=tendsto_atTop_mono (fun j=>le_max_right _ _) hq
  have ht:=boundary_prefix_sequential_positive P p hp L₀ hL₀ gs' qs' Ls hg' hq'
    (fun j=>le_max_left _ _) (fun j=>le_max_left _ _) hL
  apply ht.congr'
  filter_upwards [hg.eventually_ge_atTop 2,hq.eventually_ge_atTop 1] with j hj hqj
  simp only [gs',qs',max_eq_right hj,max_eq_right hqj]

end WP.BoundaryConvolution
