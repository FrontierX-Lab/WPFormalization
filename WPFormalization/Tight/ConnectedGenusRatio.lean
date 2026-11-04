import WPFormalization.Tight.SeparatingUnmarked
noncomputable section
namespace WP.TightConnected
open Set Filter
open scoped Topology

lemma connected_model_genus_identity (g p k : ℕ) (hg : k+2≤g)
    (Y : ℝ) (hY : Y∈Ico 0 y₀) :
    markedModel (g-k) (p+2*k) Y=(4*r Y)^k*markedModel g p Y := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : g-(k+1)=(g-k)-1 := by omega
    have hp : p+2*(k+1)=(p+2*k)+2 := by omega
    rw [he,hp,Analysis.ratioModel_genus_identity (g-k) (p+2*k) (by omega) Y hY,
      ih (by omega),pow_succ]
    ring

lemma connected_marked_leading_relative_error (P : PsiTheory) (p : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∃ G : ℕ, ∀ g≥G, ∀ Y∈Ico (0:ℝ) y₀,
      |Real.pi*markedF P g p (XR Y)/markedModel g p Y-1|≤C/(g:ℝ) := by
  by_cases hp : p=0
  · subst p
    exact TightSeparating.unmarked_leading_relative_error P
  obtain ⟨C,H,hC,hH,hCH,hbound⟩ := marked_leading_relative_error P p (by omega)
  obtain ⟨N,hN⟩ := exists_nat_ge H
  refine ⟨C,hC,N+2,?_⟩
  intro g hg Y hY
  have hg2 : 2≤g := by omega
  have hcg : g≤complexity g p := by unfold complexity;omega
  have hlarge : H≤(complexity g p:ℝ) := hN.trans (by exact_mod_cast (show N≤complexity g p by omega))
  have hx : XR Y∈Ico (0:ℝ) xCritical :=
    ⟨XR_nonneg_interior Y hY,XR_strictMonoOn hY.2.le (by simp) hY.2⟩
  have hh := hbound g hlarge (XR Y) hx
  unfold markedLeadingError at hh
  rw [Analysis.inverseY_eq_of_root (XR Y) Y hY.2.le rfl] at hh
  exact hh.trans (div_le_div_of_nonneg_left hC.le (by exact_mod_cast (show 0<g by omega))
    (by exact_mod_cast hcg))

lemma connected_fixed_genus_ratio_error (P : PsiTheory) (k : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∃ G : ℕ, ∀ g≥G, ∀ Y∈Ico (0:ℝ) y₀,
      |markedF P (g-k) (2*k) (XR Y)/((4*r Y)^k*markedF P g 0 (XR Y))-1|≤C/(g:ℝ) := by
  obtain ⟨A,hA,Ga,ha⟩ := connected_marked_leading_relative_error P (2*k)
  obtain ⟨B,hB,Gb,hb⟩ := TightSeparating.unmarked_leading_relative_error P
  obtain ⟨N,hN⟩ := exists_nat_ge (2*B)
  refine ⟨2*(2*A+B),by positivity,2*k+Ga+Gb+N+2,?_⟩
  intro g hg Y hY
  have hg2 : 2≤g := by omega
  have hgr : 0<(g:ℝ) := by exact_mod_cast (show 0<g by omega)
  have hgkr : 0<((g-k:ℕ):ℝ) := by exact_mod_cast (show 0<g-k by omega)
  have hden : B/(g:ℝ)≤1/2 := by
    apply (div_le_iff₀ hgr).mpr
    have hNg : (N:ℝ)≤g := by exact_mod_cast (show N≤g by omega)
    linarith
  have ha' : |Real.pi*markedF P (g-k) (2*k) (XR Y)/markedModel (g-k) (2*k) Y-1|≤(2*A)/(g:ℝ) := by
    apply (ha (g-k) (by omega) Y hY).trans
    apply (div_le_div_iff₀ hgkr hgr).mpr
    have hhalf : (g:ℝ)≤2*((g-k:ℕ):ℝ) := by exact_mod_cast (show g≤2*(g-k) by omega)
    nlinarith
  have hb' := hb g (by omega) Y hY
  have hq := volume_ratio_error_quotient _ _ (2*A) B (g:ℝ) hgr ha' hb' hden
  have hF : markedF P g 0 (XR Y)≠0 := by
    intro hz
    rw [hz,mul_zero,zero_div,zero_sub,abs_neg,abs_one] at hb'
    linarith
  have hM : markedModel g 0 Y≠0 := (markedModel_pos_parameter g 0 (by unfold Stable;omega) Y hY).ne'
  have hr : r Y≠0 := (r_pos Y hY).ne'
  have hid : (Real.pi*markedF P (g-k) (2*k) (XR Y)/markedModel (g-k) (2*k) Y)/
      (Real.pi*markedF P g 0 (XR Y)/markedModel g 0 Y)=
      markedF P (g-k) (2*k) (XR Y)/((4*r Y)^k*markedF P g 0 (XR Y)) := by
    rw [show 2*k=0+2*k by omega,connected_model_genus_identity g 0 k (by omega) Y hY]
    field_simp [hM,hF,hr,Real.pi_ne_zero]
  rwa [hid] at hq

lemma connected_fixed_genus_ratio_tendsto (P : PsiTheory) (k : ℕ)
    (gs : ℕ→ℕ) (hg : Tendsto gs atTop atTop) (Ys : ℕ→ℝ)
    (hY : ∀j,Ys j∈Ico 0 y₀) :
    Tendsto (fun j=>markedF P (gs j-k) (2*k) (XR (Ys j))/
      ((4*r (Ys j))^k*markedF P (gs j) 0 (XR (Ys j)))) atTop (𝓝 1) := by
  obtain ⟨C,hC,G,hbound⟩ := connected_fixed_genus_ratio_error P k
  have hr : Tendsto (fun j=>C/(gs j:ℝ)) atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop.comp hg).const_div_atTop C
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun j=>norm_nonneg _)) _ hr
  filter_upwards [hg.eventually_ge_atTop G] with j hj
  simpa only [Real.norm_eq_abs] using hbound (gs j) hj (Ys j) (hY j)
end WP.TightConnected
