import WPFormalization.Tight.ConnectedFourierScaledTail
import WPFormalization.Tight.ConnectedGaussianCore
import WPFormalization.Analysis.GaussianL1Criterion
import WPFormalization.Marked.LogGrowth
noncomputable section
namespace WP.TightConnected
open Set Filter MeasureTheory
open scoped Topology

lemma tight_characteristic_l1_tendsto (P:PsiTheory)(p:ℕ)(hp:1≤p)(L₀:ℝ)(hL₀:0≤L₀)
    (gs:ℕ→ℕ)(hg:Tendsto gs atTop atTop)(xs:ℕ→ℝ)
    (hx:∀j,xs j∈Ioo (0:ℝ) xCritical)(Ls:ℕ→Fin p→ℝ)(hL:∀j i,0≤Ls j i ∧ tightParameterScale (inverseY (xs j))*Ls j i≤L₀)
    (hmu:Tendsto (fun j=>(complexity (gs j) p:ℝ)*Psi (xs j)) atTop atTop) :
    Tendsto (fun j=>∫t:ℝ,‖scaledTightFourier P (gs j) p (Ls j) (xs j) t-
      Complex.exp (-(t:ℂ)^2/2)‖) atTop (𝓝 0) := by
  obtain ⟨c,C,hc,hC,htail⟩:=scaledTightFourier_uniform_tail P
  apply Analysis.gaussian_characteristic_l1_tendsto_of_core_tails
    (fun j=>scaledTightFourier P (gs j) p (Ls j) (xs j))
    (fun j=>scaledTightFourier_integrable P (gs j) p (Ls j) (xs j) (hx j)) c C hc
  · exact tight_characteristic_gaussian_core_tendsto P p hp L₀ hL₀ gs hg xs hx Ls hL hmu
  · intro T hT
    have hh:Tendsto (fun j=>(complexity (gs j) p:ℝ)) atTop atTop:=
      (Analysis.complexity_real_tendsto_atTop p).comp hg
    filter_upwards [hg.eventually_ge_atTop 2,hh.eventually_ge_atTop 32,hh.eventually_ge_atTop (T^2)]
      with j hj hhj hTj
    have hs:Stable (gs j) p:=by unfold Stable;omega
    have hn:32≤complexity (gs j) p:=by exact_mod_cast hhj
    exact htail (gs j) p hp hs hn (Ls j) (xs j) (hx j) T (by linarith) hTj


/-- The actual tight coefficient local limit at any index whose centered
standardized displacement tends to zero. The scaled length box is retained. -/
lemma tightMass_local_limit_zero (P:PsiTheory) (p:ℕ) (hp:1≤p) (B:ℝ) (hB:0≤B)
    (gs:ℕ→ℕ) (hg:Tendsto gs atTop atTop) (xs:ℕ→ℝ)
    (hx:∀j,xs j∈Ioo (0:ℝ) xCritical) (Ls:ℕ→Fin p→ℝ)
    (hL:∀j i,0≤Ls j i ∧ tightParameterScale (inverseY (xs j))*Ls j i≤B)
    (hmu:Tendsto (fun j=>(complexity (gs j) p:ℝ)*Psi (xs j)) atTop atTop)
    (ks:ℕ→ℕ)
    (hoffset:Tendsto (fun j=>((ks j:ℝ)-(complexity (gs j) p:ℝ)*Psi (xs j))/
      Real.sqrt ((complexity (gs j) p:ℝ)*euler Psi (xs j))) atTop (𝓝 0)) :
    Tendsto (fun j=>Real.sqrt ((complexity (gs j) p:ℝ)*euler Psi (xs j))*
      tightMass P (gs j) p (Ls j) (ks j) (xs j)) atTop (𝓝 (1/Real.sqrt (2*Real.pi))) := by
  have hl1 := tight_characteristic_l1_tendsto P p hp B hB gs hg xs hx Ls hL hmu
  let v : ℕ→ℝ := fun j=>Real.sqrt ((complexity (gs j) p:ℝ)*euler Psi (xs j))
  let z : ℕ→ℝ := fun j=>((ks j:ℝ)-(complexity (gs j) p:ℝ)*Psi (xs j))/v j
  let Q : ℕ→ℝ := fun j=>Real.exp (-(z j)^2/2)/Real.sqrt (2*Real.pi)
  have hQ : Tendsto Q atTop (𝓝 (1/Real.sqrt (2*Real.pi))) := by
    have hz : Tendsto (fun j=>-(z j)^2/2) atTop (𝓝 0) := by
      simpa only [zero_pow (by omega : 2≠0),neg_zero,zero_div] using ((hoffset.pow 2).neg.div_const 2)
    have ht := ((Real.continuous_exp.tendsto 0).comp hz).div_const (Real.sqrt (2*Real.pi))
    simpa only [Real.exp_zero,Function.comp_def,Q] using ht
  have he : Tendsto (fun j=>v j*tightMass P (gs j) p (Ls j) (ks j) (xs j)-Q j) atTop (𝓝 0) := by
    have herror : Tendsto (fun j=>(∫t:ℝ,‖scaledTightFourier P (gs j) p (Ls j) (xs j) t-
      Complex.exp (-(t:ℂ)^2/2)‖)/(2*Real.pi)) atTop (𝓝 0) := by
      simpa only [zero_div] using hl1.div_const (2*Real.pi)
    apply squeeze_zero_norm' _ herror
    filter_upwards [hg.eventually_ge_atTop 2] with j hj
    have hs : Stable (gs j) p := by unfold Stable;omega
    have hc : 0<complexity (gs j) p := by unfold Stable at hs;unfold complexity;omega
    have hh := tightMass_error_of_characteristic_l1 P (gs j) p hp hs (Ls j) hc (xs j) (hx j)
      _ (le_refl _) (ks j:ℤ)
    simp only [Int.natCast_nonneg,ite_true,Int.toNat_natCast,Int.cast_natCast] at hh
    have hφ : Real.exp (-((ks j:ℝ)-(complexity (gs j) p:ℝ)*Psi (xs j))^2/(2*(v j)^2))/
        Real.sqrt (2*Real.pi)=Q j := by
      dsimp [Q,z]
      congr 2
      simp only [div_pow]
      ring
    simpa only [v,hφ,Real.norm_eq_abs] using hh
  have ht := he.add hQ
  simp only [zero_add] at ht
  apply ht.congr'
  exact Eventually.of_forall (fun j=>by dsimp only;ring)
end WP.TightConnected
