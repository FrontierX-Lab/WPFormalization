import WPFormalization.Analysis.GevreyOneSequence
import WPFormalization.HigherOrder.EndpointInsertionMatching
import WPFormalization.HigherOrder.Endpoint
import WPFormalization.HigherOrder.AsymptoticUniqueness
import WPFormalization.Statements.RecursiveRemainderTarget
import WPFormalization.Marked.Positivity
import WPFormalization.HigherOrder.CriticalCuspExact
/-! Critical canonical transport vanishing follows from the explicit actual
C.3 remainder substatement. That upstream result remains a visible parameter;
this module does not assert the remainder or complete Proposition C.3. The
actual critical inverse-cusp identity and ordinary coefficient uniqueness
identify the canonical critical cusp series at all orders. -/
noncomputable section
namespace WP.Analysis
open Filter
open scoped Topology
lemma GevreyOneSequence.hasInversePowerExpansion (scale F:ℕ→ℝ)(hs:Tendsto scale atTop atTop)
    (f:HigherOrder.Series)(hF:GevreyOneSequence scale F f):
    HigherOrder.HasInversePowerExpansion F scale (fun j=>PowerSeries.coeff j f):=by
  obtain ⟨C,B,c,N₀,hC,hB,hc,hall⟩:=hF
  intro K
  obtain ⟨N₁,hN₁⟩:=eventually_atTop.1 (hs.eventually (eventually_ge_atTop ((K:ℝ)/c)))
  refine ⟨C*B^(K+1)*((K+1).factorial:ℝ),by positivity,max N₀ N₁,?_⟩
  intro n hn
  have hn₀:N₀≤n:=(le_max_left _ _).trans hn
  have hn₁:N₁≤n:=(le_max_right _ _).trans hn
  have hd:=hall n hn₀
  refine ⟨hd.1,?_⟩
  have hk:(K:ℝ)≤c*scale n:=by
    have he:((K:ℝ))≤ scale n*c:=(div_le_iff₀ hc).mp (hN₁ n hn₁)
    simpa only[mul_comm] using he
  exact hd.2 K hk
end WP.Analysis
namespace WP.HigherOrder
open Filter PowerSeries Set
open scoped Topology
private lemma critical_complexity_tendsto (p:ℕ):Tendsto (fun g:ℕ=>(complexity g p:ℝ)) atTop atTop:=by
  have ht:Tendsto (fun g:ℕ=>complexity g p) atTop atTop:=by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b+2)] with g hg
    dsimp[complexity]
    omega
  exact tendsto_natCast_atTop_atTop.comp ht

lemma critical_cusp_has_exact_expansion (P:PsiTheory)(p:ℕ)(hp:1≤p):
    HasInversePowerExpansion (fun g=>cuspCorrection P g p y₀) (fun g=>(complexity g p:ℝ))
      (fun j=>PowerSeries.coeff j ((1+PowerSeries.C (-(p:ℝ)/5)*PowerSeries.X)⁻¹)):=by
  have hG:=Analysis.GevreyOneSequence.of_real _ (critical_complexity_tendsto p) _ _
    (Analysis.linearInverseFactor_gevrey (-(p:ℝ)/5))
  have he:(fun g=>(1+(-(p:ℝ)/5)/(complexity g p:ℝ))⁻¹)=ᶠ[atTop]
      (fun g=>cuspCorrection P g p y₀):=by
    filter_upwards [eventually_ge_atTop 2] with g hg
    have hx: cuspCorrection P g p y₀=(1-(p:ℝ)/(5*(complexity g p:ℝ)))⁻¹:=by
      rw[←critical_cusp_inverse_exact P g p hg hp,inv_inv]
    rw[hx]
    congr 1
    simp only[div_eq_mul_inv,mul_inv_rev]
    ring
  have hh:=Analysis.GevreyOneSequence.congr _ _ _ _ hG he
  exact Analysis.GevreyOneSequence.hasInversePowerExpansion _ _ (critical_complexity_tendsto p) _ hh

lemma critical_cusp_has_canonical_expansion_of_remainder (P:PsiTheory)
    (hr:UniformRecursiveRemainderTarget P)(p:ℕ)(hp:1≤p):
    HasInversePowerExpansion (fun g=>cuspCorrection P g p y₀) (fun g=>(complexity g p:ℝ))
      (cuspCoefficient P y₀ p):=by
  obtain ⟨C,B,M,hC,hB,hM,hprofile,hscalar⟩:=hr
  intro K
  let D:ℝ:=C*B^(K+1)*scalarOrderWeight (M:ℝ) (K+1) p^(2*(K+1))
  have hpR:0<(p:ℝ):=by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hp)
  have hD:0<D:=by dsimp[D,scalarOrderWeight];positivity
  refine ⟨D,hD,2,?_⟩
  intro g hg
  have hs:Stable g p:=by unfold Stable;omega
  have hhN:1≤complexity g p:=by unfold complexity;omega
  have hh:0<(complexity g p:ℝ):=by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hhN)
  have he:=hscalar g p hp hs hhN (K+1) (by omega) y₀ ⟨y₀_pos.le,le_rfl⟩
  refine ⟨hh,?_⟩
  exact (le_add_of_nonneg_right (abs_nonneg _)).trans he

lemma critical_formalCusp_of_recursiveRemainder (P:PsiTheory)(hr:UniformRecursiveRemainderTarget P)
    (p:ℕ)(hp:1≤p):
    formalCusp P y₀ p=(1+PowerSeries.C (-(p:ℝ)/5)*PowerSeries.X)⁻¹:=by
  have he:=inverse_power_expansion_unique _ _ _ _ (critical_complexity_tendsto p)
    (critical_cusp_has_canonical_expansion_of_remainder P hr p hp) (critical_cusp_has_exact_expansion P p hp)
  ext j
  simpa only[formalCusp,PowerSeries.coeff_mk] using congrFun he j

lemma transportCoefficient_critical_of_recursiveRemainder (P:PsiTheory)(hr:UniformRecursiveRemainderTarget P)
    (p j:ℕ)(hp:1≤p)(hj:1≤j):transportCoefficient P p j y₀=0:=by
  let L:Series:=1+PowerSeries.C (-(p:ℝ)/5)*PowerSeries.X
  have hL0:PowerSeries.constantCoeff L=1:=by simp[L]
  have hLi0:PowerSeries.constantCoeff (L⁻¹)≠0:=by rw[PowerSeries.constantCoeff_inv,hL0,inv_one];exact one_ne_zero
  have hInv:(L⁻¹)⁻¹=L:=((PowerSeries.eq_inv_iff_mul_eq_one hLi0).mpr
    (PowerSeries.mul_inv_cancel L (by rw[hL0];exact one_ne_zero))).symm
  rw[transportCoefficient,critical_formalCusp_of_recursiveRemainder P hr p hp]
  change PowerSeries.coeff (j+1) ((L⁻¹)⁻¹)=0
  rw[hInv]
  simp[L,PowerSeries.coeff_C,show j≠0 by omega]
end WP.HigherOrder
