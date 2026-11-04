import WPFormalization.Tight.ShiftedPolynomial
import WPFormalization.Statements.Intensities
import WPFormalization.Analysis.VolumeProfileShifts
import WPFormalization.Volumes.BoundaryDensityShift
import WPFormalization.Volumes.BoundarySaddle
/-! Relative tight-length scale comparison at the genuine connected-cut saddle.
The weighted logarithmic density bound retains unbounded n/g; it does not
replace the relative comparison by absolute continuity at the critical endpoint. -/
noncomputable section
namespace WP.TightConnected
open Set Filter
open scoped Topology

lemma tightScale_pos (l:ℝ)(hl:0≤l):0<tightScale l :=
  tightParameterScale_pos _ (Analysis.densityY_spec l hl).1

lemma tightScale_log_profileB (l:ℝ)(hl:0≤l):
    Real.log (tightScale l)= -(Real.log (profileB l))/2 := by
  have hr:=r_pos _ (Analysis.densityY_spec l hl).1
  rw [tightScale,Real.log_div (Real.sqrt_pos.mpr (by positivity:0<2*r (densityY l))).ne'
    Real.pi_ne_zero,Real.log_sqrt (by positivity:0≤2*r (densityY l)),
    Analysis.volume_profile_B_physical l hl,Analysis.volumeProfileBPhysical,
    Real.log_div (pow_ne_zero _ Real.pi_ne_zero) (mul_pos (by norm_num) hr).ne',Real.log_pow]
  ring

lemma tightScale_log_comparison (l m : ℝ) (hl : 0 ≤ l) (hm : 0 ≤ m) :
    |Real.log (tightScale l)-Real.log (tightScale m)|≤2*|l-m|/(1+min l m) := by
  rw [tightScale_log_profileB l hl,tightScale_log_profileB m hm,
    show -Real.log (profileB l)/2- -Real.log (profileB m)/2 =
      -(Real.log (profileB l)-Real.log (profileB m))/2 by ring,
    abs_div,abs_neg,abs_of_nonneg (by norm_num:0≤(2:ℝ))]
  have hh:=Analysis.volume_profile_B_log_comparison l m hl hm
  have ht:=div_le_div_of_nonneg_right hh (by norm_num:0≤(2:ℝ))
  convert ht using 1 <;>ring

/-- The paper's saddle for n>=2, chosen using Phi_g' at index n-1. -/
def connectedSaddle (g n:ℕ):ℝ:=BoundaryConvolution.boundarySaddle g 1 (n-1)

lemma connectedSaddle_spec (g n:ℕ)(hg:2≤g)(hn:2≤n):
    connectedSaddle g n∈Ioo (0:ℝ) xCritical ∧
      (complexity g 1:ℝ)*Psi (connectedSaddle g n)=(n:ℝ)-1 ∧
      inverseY (connectedSaddle g n)=densityY (2*((n:ℝ)-1)/(2*(g:ℝ)-1)) := by
  have hh:=BoundaryConvolution.boundarySaddle_spec g 1 (n-1) hg (by omega)
  have hc:(complexity g 1:ℝ)=2*(g:ℝ)-1:=by
    unfold complexity
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hncast:((n-1:ℕ):ℝ)=(n:ℝ)-1:=by rw [Nat.cast_sub (by omega)];norm_num
  simpa only [connectedSaddle,hncast,hc] using hh

lemma connectedSaddle_scale_log_bound (g n:ℕ)(hg:3≤g)(hn:2≤n):
    |Real.log (tightParameterScale (inverseY (connectedSaddle g n)))-
      Real.log (tightScale ((n:ℝ)/(g:ℝ)))|≤36/(g:ℝ) := by
  have hs:=connectedSaddle_spec g n (by omega) hn
  rw [hs.2.2]
  change |Real.log (tightScale (2*((n:ℝ)-1)/(2*(g:ℝ)-1)))-
    Real.log (tightScale ((n:ℝ)/(g:ℝ)))|≤_
  have hgr:(3:ℝ)≤g:=by exact_mod_cast hg
  have hnr:(2:ℝ)≤n:=by exact_mod_cast hn
  have hl:0≤2*((n:ℝ)-1)/(2*(g:ℝ)-1):=div_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
  have hm:0≤(n:ℝ)/(g:ℝ):=by positivity
  have he:=tightScale_log_comparison _ _ hl hm
  have hd:=BoundaryConvolution.boundary_density_relative_shift 1 g n (by omega) (by omega)
  norm_num only [Nat.cast_one] at hd
  have hd': |2*((n:ℝ)-1)/(2*(g:ℝ)-1)-(n:ℝ)/(g:ℝ)|/
      (1+min (2*((n:ℝ)-1)/(2*(g:ℝ)-1)) ((n:ℝ)/(g:ℝ)))≤18/(g:ℝ):=by
    convert hd using 1 <;>ring
  apply he.trans
  convert mul_le_mul_of_nonneg_left hd' (by norm_num : 0≤(2:ℝ)) using 1 <;>ring

lemma connectedSaddle_scale_ratio_tendsto (gs ns:ℕ→ℕ)
    (hg:Tendsto gs atTop atTop)(hg3:∀j,3≤gs j)(hn2:∀j,2≤ns j):
    Tendsto (fun j=>tightParameterScale (inverseY (connectedSaddle (gs j) (ns j)))/
      tightScale ((ns j:ℝ)/(gs j:ℝ))) atTop (𝓝 1) := by
  have hgr:Tendsto (fun j=>(gs j:ℝ)) atTop atTop:=tendsto_natCast_atTop_atTop.comp hg
  have herr:Tendsto (fun j=>(36:ℝ)/(gs j:ℝ)) atTop (𝓝 0):=hgr.const_div_atTop _
  have hlog:Tendsto (fun j=>Real.log (tightParameterScale (inverseY (connectedSaddle (gs j) (ns j))))-
      Real.log (tightScale ((ns j:ℝ)/(gs j:ℝ)))) atTop (𝓝 0):=by
    apply squeeze_zero_norm' _ herr
    apply Eventually.of_forall
    intro j
    simpa only [Real.norm_eq_abs] using connectedSaddle_scale_log_bound (gs j) (ns j) (hg3 j) (hn2 j)
  have ht:=Real.continuous_exp.continuousAt.tendsto.comp hlog
  simp only [Real.exp_zero] at ht
  apply ht.congr'
  apply Eventually.of_forall
  intro j
  have hs:=(connectedSaddle_spec (gs j) (ns j) (by have:=hg3 j;omega) (hn2 j)).1
  have ha:=tightParameterScale_pos _ (inverseY_branch _ ⟨hs.1.le,hs.2⟩).1
  have hb:=tightScale_pos ((ns j:ℝ)/(gs j:ℝ)) (by positivity)
  dsimp only [Function.comp_def]
  rw [Real.exp_sub,Real.exp_log ha,Real.exp_log hb]

end WP.TightConnected
