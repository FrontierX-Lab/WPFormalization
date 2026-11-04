import WPFormalization.Tight.ConnectedUniform
import WPFormalization.Tight.ConnectedDivergingCoefficients
import WPFormalization.Tight.ConnectedPoissonZero
import WPFormalization.Volumes.DiagonalChainAlgebra
noncomputable section
namespace WP.TightConnected
open Set Filter
open scoped Topology

/- The coefficient ratio in the original F.2 derivative-saddle branch. -/
def connectedSaddleCoefficientRatio (P:PsiTheory) (k g n:ℕ) (t:Fin (2*k)→ℝ) : ℝ :=
  let Y := inverseY (connectedSaddle g n)
  realCoeff (TightMoments.momentTightG P (g-k) (2*k)
    (fun i=>t i/tightParameterScale Y)) n /
    (realCoeff (Phi P g) n*((4*r Y)^k*∏i,boundaryFactor 0 (t i)))

/- Original F.2 coefficient conclusion for n tending to infinity, including
k=0. The actual paper saddle and the compact scaled-length box are retained. -/
@[blueprint "lem:tight-connected"]
theorem tight_connected_original_saddle (P:PsiTheory) (k:ℕ) (B:ℝ) (hB:0≤B)
    (gs ns:ℕ→ℕ) (hg:Tendsto gs atTop atTop) (hn:Tendsto ns atTop atTop)
    (ts:ℕ→Fin (2*k)→ℝ) (ht:∀j i,ts j i∈Icc (0:ℝ) B) :
    Tendsto (fun j=>connectedSaddleCoefficientRatio P k (gs j) (ns j) (ts j)) atTop (𝓝 1) := by
  by_cases hk : k=0
  · subst k
    apply (show Tendsto (fun _j:ℕ=>(1:ℝ)) atTop (𝓝 1) from tendsto_const_nhds).congr'
    filter_upwards [hg.eventually_ge_atTop 2,hn.eventually_ge_atTop 1] with j hj hnj
    have hV := diagonal_volume_pos_nonempty P (gs j) (ns j) hnj (by unfold Stable;omega)
    have hcoef : 0<realCoeff (Phi P (gs j)) (ns j) := by
      have he := marked_realCoeff_volume P (gs j) 0 (ns j)
      simp only [iteratedDeriv_zero,Nat.add_zero] at he
      rw [he]
      positivity
    unfold connectedSaddleCoefficientRatio
    dsimp only
    simp only [Nat.mul_zero,Nat.sub_zero,pow_zero,Fin.prod_univ_zero,mul_one]
    rw [connected_momentTightG_zero_coeff P (gs j) hj _ (ns j),div_self hcoef.ne']
  · let gs' : ℕ→ℕ := fun j=>max (k+3) (gs j)
    let ns' : ℕ→ℕ := fun j=>max 2 (ns j)
    let xs : ℕ→ℝ := fun j=>connectedSaddle (gs' j) (ns' j)
    let Ls : ℕ→Fin (2*k)→ℝ := fun j i=>ts j i/tightParameterScale (inverseY (xs j))
    have hg' : Tendsto gs' atTop atTop := tendsto_atTop_mono (fun j=>le_max_right _ _) hg
    have hn' : Tendsto ns' atTop atTop := tendsto_atTop_mono (fun j=>le_max_right _ _) hn
    have hα (j:ℕ):0<tightParameterScale (inverseY (xs j)) :=
      tightParameterScale_pos _ (inverseY_branch _
        ⟨(connectedSaddle_spec _ _ (by dsimp [gs'];omega) (by dsimp [ns'];omega)).1.1.le,
          (connectedSaddle_spec _ _ (by dsimp [gs'];omega) (by dsimp [ns'];omega)).1.2⟩).1
    have hscale (j:ℕ) (i:Fin (2*k)) : tightParameterScale (inverseY (xs j))*Ls j i=ts j i := by
      dsimp only [Ls]
      field_simp [(hα j).ne']
    have hL : ∀j i,0≤Ls j i ∧ tightParameterScale (inverseY (connectedSaddle (gs' j) (ns' j)))*Ls j i≤B := by
      intro j i
      exact ⟨div_nonneg (ht j i).1 (hα j).le,(hscale j i).le.trans (ht j i).2⟩
    have hr := connected_coefficient_ratio_diverging P k (by omega) B hB gs' ns' hg' hn'
      (fun j=>by dsimp [gs'];omega) (fun j=>by dsimp [ns'];omega) Ls hL
    have hr' : Tendsto (fun j=>connectedSaddleCoefficientRatio P k (gs' j) (ns' j) (ts j)) atTop (𝓝 1) := by
      apply hr.congr'
      apply Eventually.of_forall
      intro j
      have he (i:Fin (2*k)) : tightParameterScale (inverseY (connectedSaddle (gs' j) (ns' j)))*Ls j i=ts j i := hscale j i
      simp_rw [he]
      unfold connectedSaddleCoefficientRatio
      dsimp only
      congr 1
      ring
    apply hr'.congr'
    filter_upwards [hg.eventually_ge_atTop (k+3),hn.eventually_ge_atTop 2] with j hj hnj
    simp only [gs',ns',max_eq_right hj,max_eq_right hnj]

/- The original F.2 relative-scale conclusion, without a density upper bound. -/
@[blueprint "lem:tight-connected"]
theorem tight_connected_original_scale (gs ns:ℕ→ℕ)
    (hg:Tendsto gs atTop atTop) (hn:Tendsto ns atTop atTop) :
    Tendsto (fun j=>tightParameterScale (inverseY (connectedSaddle (gs j) (ns j)))/
      tightScale ((ns j:ℝ)/(gs j:ℝ))) atTop (𝓝 1) := by
  let gs' : ℕ→ℕ := fun j=>max 3 (gs j)
  let ns' : ℕ→ℕ := fun j=>max 2 (ns j)
  have hg' : Tendsto gs' atTop atTop := tendsto_atTop_mono (fun j=>le_max_right _ _) hg
  have hr := connectedSaddle_scale_ratio_tendsto gs' ns' hg'
    (fun j=>le_max_left _ _) (fun j=>le_max_left _ _)
  apply hr.congr'
  filter_upwards [hg.eventually_ge_atTop 3,hn.eventually_ge_atTop 2] with j hj hnj
  simp only [gs',ns',max_eq_right hj,max_eq_right hnj]

lemma connected_boundaryFactor_sinh (t:ℝ) :
    boundaryFactor 0 t=(if t=0 then 1 else Real.sinh (t/2)/(t/2)) :=
  (boundary_factor_endpoints t).1

/- Original F.2 fixed-n reference c/(2g-2), including n=0 and k=0. -/
@[blueprint "lem:tight-connected"]
theorem tight_connected_original_bounded (P:PsiTheory) (k n:ℕ)
    (c:ℝ) (hc:0<c) (B:ℝ) (hB:0≤B) (gs:ℕ→ℕ) (hg:Tendsto gs atTop atTop)
    (ts:ℕ→Fin (2*k)→ℝ) (ht:∀j i,ts j i∈Icc (0:ℝ) B) :
    Tendsto (fun j=>realCoeff (TightMoments.momentTightG P (gs j-k) (2*k)
      (fun i=>ts j i/tightParameterScale (inverseY (c/(complexity (gs j) 0:ℝ))))) n /
        (realCoeff (Phi P (gs j)) n*((4*r (inverseY (c/(complexity (gs j) 0:ℝ))))^k*
          ∏i,boundaryFactor 0 (ts j i)))) atTop (𝓝 1) :=
  connected_coefficient_ratio_bounded P k n c hc B hB gs hg ts ht

/- The same original relative-scale assertion for the fixed-n reference. -/
@[blueprint "lem:tight-connected"]
theorem tight_connected_original_bounded_scale (gs:ℕ→ℕ) (hg:Tendsto gs atTop atTop)
    (n:ℕ) (c:ℝ) (hc:0<c) :
    Tendsto (fun j=>tightParameterScale (inverseY (c/(complexity (gs j) 0:ℝ)))/
      tightScale ((n:ℝ)/(gs j:ℝ))) atTop (𝓝 1) :=
  connected_bounded_poisson_scale_ratio_tendsto gs hg n c hc

/- Equivalent common-density form, uniform in all cusp counts and all cuts. -/
@[blueprint "lem:tight-connected"]
theorem tight_connected (P:PsiTheory) (k:ℕ) (B:ℝ) (hB:0≤B) :
    ∀ε:ℝ,0<ε→∃G:ℕ,∀g≥G,∀n:ℕ,∀t:Fin (2*k)→ℝ,
      (∀i,t i∈Icc (0:ℝ) B)→|connectedDensityCoefficientRatio P k g n t-1|≤ε :=
  tight_connected_density_uniform P k B hB
end WP.TightConnected
