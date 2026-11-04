import WPFormalization.Coefficients.AdjacentBulkSecants
/-! Choosing actual integer secant lengths floor(g^(5/8)) and floor(g^(3/4))
yields the two quantitative bulk logarithmic rates, including the top
bounded-codimension range. All constants precede genus and degree. -/
noncomputable section
namespace WP.Analysis
open Filter
open scoped Topology
lemma eventually_floor_power_window (a b s:ℝ)(ha:0<a)(hab:a<b)(hs:0<s) :
    ∀ᶠg:ℕ in atTop,
      let l:=⌊Real.rpow (g:ℝ) a⌋₊
      1 ≤ l ∧ 2*(l:ℝ) ≤ s*Real.rpow (g:ℝ) b ∧
      Real.rpow (g:ℝ) a/2 ≤ l ∧ (l:ℝ) ≤ Real.rpow (g:ℝ) a := by
  have hta:Tendsto (fun g:ℕ=>Real.rpow (g:ℝ) a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have htb:Tendsto (fun g:ℕ=>Real.rpow (g:ℝ) (b-a)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hab)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hta.eventually (eventually_ge_atTop 2),htb.eventually (eventually_ge_atTop (2/s)),eventually_ge_atTop 1] with g hga hgb hg
  dsimp only
  have hgr:(0:ℝ)<g := by exact_mod_cast (show 0<g by omega)
  have hnon:0 ≤ Real.rpow (g:ℝ) a := Real.rpow_nonneg hgr.le _
  have hf:Real.rpow (g:ℝ) a-1< (⌊Real.rpow (g:ℝ) a⌋₊:ℝ) := Nat.sub_one_lt_floor _
  have hl : 1 ≤ ⌊Real.rpow (g:ℝ) a⌋₊ := (Nat.le_floor_iff hnon).mpr (by norm_num only[Nat.cast_one];linarith)
  refine ⟨hl,?_,by linarith,Nat.floor_le hnon⟩
  have hr:Real.rpow (g:ℝ) b=Real.rpow (g:ℝ) a*Real.rpow (g:ℝ) (b-a) := by
    have he : Real.rpow (g:ℝ) (a+(b-a))=Real.rpow (g:ℝ) a*Real.rpow (g:ℝ) (b-a) := Real.rpow_add hgr _ _
    convert he using 1
    congr 1
    ring
  rw [hr]
  have he : 2 ≤ Real.rpow (g:ℝ) (b-a)*s := (div_le_iff₀ hs).mp hgb
  nlinarith only [Nat.floor_le hnon,mul_le_mul_of_nonneg_left he hnon]
end WP.Analysis
namespace WP.Coefficients
open Filter
lemma adjacentLogRatio_scaled_power_rate (P:PsiTheory) (a b s:ℝ)
    (ha:0<a)(hab:a<b)(hs:0<s)(hexp:(1/2:ℝ)-a=a-b) :
    ∃C:ℝ,0<C ∧∃G:ℕ,∀g≥G,∀k:ℕ,s*Real.rpow (g:ℝ) b ≤ k→k<3*g-2→
      |adjacentLogRatio P g k-Real.log (adjacentProfileQ ((k:ℝ)/g))| ≤
        C*Real.rpow (g:ℝ) ((1/2:ℝ)-a) := by
  obtain ⟨D,hD,hbulk⟩:=adjacentLogRatio_full_bulk_secant_bound P
  have he:∀ᶠg:ℕ in atTop,∀k:ℕ,s*Real.rpow (g:ℝ) b ≤ k→k<3*g-2→
      |adjacentLogRatio P g k-Real.log (adjacentProfileQ ((k:ℝ)/g))| ≤
        (D*(2+1/s))*Real.rpow (g:ℝ) ((1/2:ℝ)-a) := by
    filter_upwards [Analysis.eventually_floor_power_window a b s ha hab hs,eventually_ge_atTop 1] with g hg hg1
    intro k hk hkN
    let l:ℕ:=⌊Real.rpow (g:ℝ) a⌋₊
    have hgr:(0:ℝ)<g:=by exact_mod_cast (show 0<g by omega)
    have hkr:(0:ℝ)<k:=(mul_pos hs (Real.rpow_pos_of_pos hgr b)).trans_le hk
    have hlNat:1≤l:=hg.1
    have hlr:(0:ℝ)<l:=by exact_mod_cast (show 0<l by omega)
    have h2l:2*l ≤ k:=by exact_mod_cast (hg.2.1.trans hk)
    have hf:=hbulk g hg1 k l hg.1 h2l hkN
    have hpowa:0<Real.rpow (g:ℝ) a:=Real.rpow_pos_of_pos hgr a
    have hp := Real.rpow_nonneg hgr.le ((1/2:ℝ)-a)
    have hfirst:Real.sqrt (g:ℝ)/l ≤ 2*Real.rpow (g:ℝ) ((1/2:ℝ)-a) := by
      calc _  ≤  Real.sqrt (g:ℝ)/(Real.rpow (g:ℝ) a/2) :=
             div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (half_pos hpowa) hg.2.2.1
           _ = _ := by
             have he : Real.rpow (g:ℝ) ((1/2:ℝ)-a)=Real.rpow (g:ℝ) (1/2:ℝ)/Real.rpow (g:ℝ) a := Real.rpow_sub hgr _ _
             have heS : Real.sqrt (g:ℝ)=Real.rpow (g:ℝ) (1/2:ℝ) := Real.sqrt_eq_rpow _
             rw[he,heS]
             ring
    have hsecond:(l:ℝ)/k ≤ (1/s)*Real.rpow (g:ℝ) ((1/2:ℝ)-a) := by
      calc _  ≤  Real.rpow (g:ℝ) a/(k:ℝ) := div_le_div_of_nonneg_right hg.2.2.2 hkr.le
           _  ≤  Real.rpow (g:ℝ) a/(s*Real.rpow (g:ℝ) b) :=
             div_le_div_of_nonneg_left hpowa.le (mul_pos hs (Real.rpow_pos_of_pos hgr b)) hk
           _ = _ := by
             have he : Real.rpow (g:ℝ) (a-b)=Real.rpow (g:ℝ) a/Real.rpow (g:ℝ) b := Real.rpow_sub hgr _ _
             rw[hexp,he]
             ring
    calc _  ≤  D*(Real.sqrt (g:ℝ)/l+(l:ℝ)/k) := hf
         _  ≤  D*(2*Real.rpow (g:ℝ) ((1/2:ℝ)-a)+(1/s)*Real.rpow (g:ℝ) ((1/2:ℝ)-a)) :=
           mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hD.le
         _ = _ := by ring
  obtain ⟨G,hG⟩:=eventually_atTop.mp he
  exact ⟨D*(2+1/s),by positivity,G,hG⟩

lemma adjacentLogRatio_three_quarter_rate (P:PsiTheory) :
    ∃C:ℝ,0<C ∧∃G:ℕ,∀g≥G,∀k:ℕ,Real.rpow (g:ℝ) (3/4:ℝ) ≤ k→k<3*g-2→
      |adjacentLogRatio P g k-Real.log (adjacentProfileQ ((k:ℝ)/g))| ≤ C*Real.rpow (g:ℝ) (-1/8:ℝ) := by
  simpa only[Real.rpow_eq_pow,one_mul,show (1/2:ℝ)-5/8=-1/8 by norm_num] using
    adjacentLogRatio_scaled_power_rate P (5/8) (3/4) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma adjacentLogRatio_positive_density_rate (P:PsiTheory) (ε:ℝ)(hε:0<ε) :
    ∃C:ℝ,0<C ∧∃G:ℕ,∀g≥G,∀k:ℕ,ε*(g:ℝ) ≤ k→k<3*g-2→
      |adjacentLogRatio P g k-Real.log (adjacentProfileQ ((k:ℝ)/g))| ≤ C*Real.rpow (g:ℝ) (-1/4:ℝ) := by
  simpa only[Real.rpow_eq_pow,Real.rpow_one,show (1/2:ℝ)-3/4=-1/4 by norm_num] using
    adjacentLogRatio_scaled_power_rate P (3/4) 1 ε (by norm_num) (by norm_num) hε (by norm_num)
end WP.Coefficients
