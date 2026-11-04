import WPFormalization.Tight.ConnectedPoissonCuts
import WPFormalization.Tight.ConnectedCoefficientScaleTransport
import WPFormalization.Tight.ConnectedScaleTransfer
import WPFormalization.Tight.ConnectedDensityDefinitions

noncomputable section
namespace WP.TightConnected
open Set Filter TightMoments
open scoped Topology

/-- The fixed-cusp-count branch on the equivalent density scale. The original
`c/(2g-2)` reference theorem remains `connected_coefficient_ratio_bounded`. -/
lemma connected_density_coefficient_ratio_bounded (P : PsiTheory) (k n : ℕ)
    (c : ℝ) (hc : 0<c) (B : ℝ) (hB : 0≤B)
    (gs : ℕ→ℕ) (hg : Tendsto gs atTop atTop)
    (ts : ℕ→Fin (2*k)→ℝ) (ht : ∀ j i,ts j i∈Icc (0:ℝ) B) :
    Tendsto (fun j=>connectedDensityCoefficientRatio P k (gs j) n (ts j)) atTop (𝓝 1) := by
  let xs : ℕ→ℝ := fun j=>c/(complexity (gs j) 0:ℝ)
  let Ys : ℕ→ℝ := fun j=>inverseY (xs j)
  let Zs : ℕ→ℝ := fun j=>densityY ((n:ℝ)/(gs j:ℝ))
  let αs : ℕ→ℝ := fun j=>tightParameterScale (Ys j)
  let αd : ℕ→ℝ := fun j=>tightScale ((n:ℝ)/(gs j:ℝ))
  have hx : ∀ᶠ j in atTop,xs j∈Ico (0:ℝ) xCritical :=
    connected_small_weight_eventually _ (connected_complexity_tendsto gs hg) c hc.le
  have hY : ∀ᶠ j in atTop,Ys j∈Ico (0:ℝ) y₀ := hx.mono (fun j hj=>(inverseY_branch _ hj).1)
  have hZ : ∀ j,Zs j∈Ico (0:ℝ) y₀ := fun j=>(Analysis.densityY_spec _ (by positivity)).1
  have hαd : ∀ j,0<αd j := fun j=>tightScale_pos _ (by positivity)
  have hαs : ∀ᶠ j in atTop,0<αs j := hY.mono (fun j hj=>tightParameterScale_pos _ hj)
  have hq : Tendsto (fun j=>αs j/αd j) atTop (𝓝 1) :=
    connected_bounded_poisson_scale_ratio_tendsto gs hg n c hc
  have hrs : ∀ᶠ j in atTop,(4*r (Ys j))≠0 :=
    hY.mono (fun j hj=>(mul_pos (by norm_num) (r_pos _ hj)).ne')
  have hrd : ∀ᶠ j in atTop,(4*r (Zs j))≠0 :=
    Eventually.of_forall (fun j=>(mul_pos (by norm_num) (r_pos _ (hZ j))).ne')
  have hr : Tendsto (fun j=>(4*r (Ys j))/(4*r (Zs j))) atTop (𝓝 1) := by
    have hh := hq.pow 2
    simp only [one_pow] at hh
    apply hh.congr'
    filter_upwards [hY] with j hj
    have hscale : αd j=tightParameterScale (Zs j) := rfl
    change (αs j/αd j)^2=(4*r (Ys j))/(4*r (Zs j))
    rw [hscale,←connected_r_ratio_eq_scale_square _ _ hj (hZ j)]
    field_simp
  have hsource := connected_coefficient_ratio_bounded P k n c hc (2*B) (by positivity) gs hg
    (connectedTransportScaledLengths (fun j=>αs j/αd j) ts)
    (connectedTransportScaledLengths_box (2*k) B hB (fun j=>αs j/αd j) ts ht)
  have hlimit := connected_coefficient_scale_transport k B hB
    (fun j L=>realCoeff (momentTightG P (gs j-k) (2*k) L) n)
    (fun j=>realCoeff (Phi P (gs j)) n)
    (fun j=>4*r (Ys j)) (fun j=>4*r (Zs j)) αs αd hαd hαs hrs hrd hq hr ts ht hsource
  exact hlimit

end WP.TightConnected
