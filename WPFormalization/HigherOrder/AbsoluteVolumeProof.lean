import WPFormalization.HigherOrder.IntroAbsoluteNumerical
import WPFormalization.HigherOrder.UnmarkedFirstCorrection
/-! Original Theorem 11.1 assembly. The uniform upper estimate still
depends on unfinished Theorem 10.2 via IntroAbsoluteNumerical. The sharp
fixed-n=0 lower limit is proved separately using the registered classical
first correction with its normalization identified locally. Thus this
whole theorem remains INCOMPLETE until the canonical extraction is proved. -/
noncomputable section
namespace WP.HigherOrder
open Filter
open scoped Topology
lemma absolute_volume_proof (P:PsiTheory):
    (∃C:ℝ,0<C ∧ ∃G:ℕ,∀g:ℕ,G≤g→∀n:ℕ,
      |volumeModel P g n/leadingVolume g n-1|≤C/g) ∧
    (7/12-17/(6*Real.pi^2)≤Filter.liminf
      (fun g:ℕ=>(g:ℝ)*⨆n:ℕ,|volumeModel P g n/leadingVolume g n-1|) atTop) ∧
    0<7/12-17/(6*Real.pi^2):=by
  obtain ⟨C,B,c,hC,hB,hc,N,hN,_,_,⟨D,hD,hfirst⟩,_⟩:=intro_absolute_numerical_assembly P
  refine ⟨⟨D,hD,N,hfirst⟩,?_,first_correction_lower_constant_pos⟩
  let S:ℕ→ℝ:=fun g=>(g:ℝ)*⨆n:ℕ,|volumeModel P g n/leadingVolume g n-1|
  change 7/12-17/(6*Real.pi^2)≤Filter.liminf S atTop
  have hupper:∀ᶠg:ℕ in atTop,S g≤D:=by
    filter_upwards[eventually_ge_atTop (max N 1)] with g hg
    have hgN:N≤g:=(le_max_left _ _).trans hg
    have hg1:1≤g:=(le_max_right _ _).trans hg
    have hg0:(0:ℝ)<g:=by exact_mod_cast (show 0<g by omega)
    have hsup:(⨆n:ℕ,|volumeModel P g n/leadingVolume g n-1|)≤D/(g:ℝ):=
      ciSup_le (fun n=>hfirst g hgN n)
    dsimp[S]
    calc
      _≤(g:ℝ)*(D/(g:ℝ)):=mul_le_mul_of_nonneg_left hsup hg0.le
      _=D:=by field_simp
  have hcob:atTop.IsCoboundedUnder (·≥·) S:=isCoboundedUnder_ge_of_eventually_le atTop hupper
  have hcomp:∀ᶠg:ℕ in atTop,
      (g:ℝ)*|volumeModel P g 0/leadingVolume g 0-1|≤S g:=by
    filter_upwards[eventually_ge_atTop N] with g hg
    have hbdd:BddAbove (Set.range (fun n:ℕ=>|volumeModel P g n/leadingVolume g n-1|)):=by
      refine ⟨D/(g:ℝ),?_⟩
      rintro y ⟨n,rfl⟩
      exact hfirst g hg n
    exact mul_le_mul_of_nonneg_left (le_ciSup hbdd 0) (Nat.cast_nonneg g)
  have hlim:=unmarked_abs_first_correction_limit P
  apply le_of_forall_pos_le_add
  intro ε hε
  have hlow:∀ᶠg:ℕ in atTop,7/12-17/(6*Real.pi^2)-ε≤S g:=by
    have he:=hlim.eventually (eventually_gt_nhds (show
      7/12-17/(6*Real.pi^2)-ε<7/12-17/(6*Real.pi^2) by linarith))
    filter_upwards[he,hcomp] with g hg hc
    linarith
  have he:=Filter.le_liminf_of_le hcob hlow
  linarith
end WP.HigherOrder
