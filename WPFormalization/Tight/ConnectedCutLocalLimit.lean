import WPFormalization.Tight.ConnectedCharacteristicL1
import WPFormalization.Tight.ConnectedSaddleOffset
import WPFormalization.Statements.CuspLocalLimit
noncomputable section
namespace WP.TightConnected
open Set Filter
open scoped Topology
lemma connected_nat_sub_tendsto (gs:ℕ→ℕ) (hg:Tendsto gs atTop atTop) (k:ℕ) :
    Tendsto (fun j=>gs j-k) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [hg.eventually_ge_atTop (b+k)] with j hj
  omega

lemma connected_cut_complexity (g k:ℕ) (hg:k+2≤g) :
    complexity (g-k) (2*k)=complexity g 0 := by unfold complexity;omega

lemma connectedSaddle_numerator_scaled_limit (P:PsiTheory) (k:ℕ) (hk:1≤k) (B:ℝ) (hB:0≤B)
    (gs ns:ℕ→ℕ) (hg:Tendsto gs atTop atTop) (hn:Tendsto ns atTop atTop)
    (hgk:∀j,k+2≤gs j) (hn2:∀j,2≤ns j) (Ls:ℕ→Fin (2*k)→ℝ)
    (hL:∀j i,0≤Ls j i ∧ tightParameterScale (inverseY (connectedSaddle (gs j) (ns j)))*Ls j i≤B) :
    Tendsto (fun j=>Real.sqrt ((complexity (gs j) 0:ℝ)*euler Psi (connectedSaddle (gs j) (ns j)))*
      tightMass P (gs j-k) (2*k) (Ls j) (ns j) (connectedSaddle (gs j) (ns j)))
      atTop (𝓝 (1/Real.sqrt (2*Real.pi))) := by
  have hg2 (j:ℕ):2≤gs j := by have:=hgk j;omega
  have hc (j:ℕ):complexity (gs j-k) (2*k)=complexity (gs j) 0 := connected_cut_complexity _ _ (hgk j)
  have hmean := connectedSaddle_numerator_mean_tendsto gs ns hg2 hn2 hn
  have hoff := connectedSaddle_offset_tendsto gs ns hg hn hg2 hn2
  have hmean' : Tendsto (fun j=>(complexity (gs j-k) (2*k):ℝ)*Psi (connectedSaddle (gs j) (ns j))) atTop atTop := by
    simpa only [hc] using hmean
  have hoff' : Tendsto (fun j=>((ns j:ℝ)-(complexity (gs j-k) (2*k):ℝ)*Psi (connectedSaddle (gs j) (ns j)))/
      Real.sqrt ((complexity (gs j-k) (2*k):ℝ)*euler Psi (connectedSaddle (gs j) (ns j)))) atTop (𝓝 0) := by
    simpa only [hc] using hoff
  have ht := tightMass_local_limit_zero P (2*k) (by omega) B hB
    (fun j=>gs j-k) (connected_nat_sub_tendsto gs hg k)
    (fun j=>connectedSaddle (gs j) (ns j))
    (fun j=>(connectedSaddle_spec _ _ (hg2 j) (hn2 j)).1) Ls hL hmean' ns hoff'
  simpa only [hc] using ht

lemma connectedSaddle_denominator_scaled_limit (P:PsiTheory)
    (gs ns:ℕ→ℕ) (hg:Tendsto gs atTop atTop) (hn:Tendsto ns atTop atTop)
    (hg2:∀j,2≤gs j) (hn2:∀j,2≤ns j) :
    Tendsto (fun j=>Real.sqrt ((complexity (gs j) 1:ℝ)*euler Psi (connectedSaddle (gs j) (ns j)))*
      cuspMass P (gs j) 1 (ns j-1) (connectedSaddle (gs j) (ns j)))
      atTop (𝓝 (1/Real.sqrt (2*Real.pi))) := by
  have hs (j:ℕ) := connectedSaddle_spec (gs j) (ns j) (hg2 j) (hn2 j)
  have hnc (j:ℕ):((ns j-1:ℕ):ℝ)=(ns j:ℝ)-1 := by rw [Nat.cast_sub (by have:=hn2 j;omega)];norm_num
  have hmean : Tendsto (fun j=>(complexity (gs j) 1:ℝ)*Psi (connectedSaddle (gs j) (ns j))) atTop atTop := by
    have ht : Tendsto (fun j=>((ns j-1:ℕ):ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp (connected_nat_sub_tendsto ns hn 1)
    apply ht.congr'
    exact Eventually.of_forall (fun j=>(hnc j).trans (hs j).2.1.symm)
  have hoff : Tendsto (fun j=>(((ns j-1:ℕ):ℝ)-(complexity (gs j) 1:ℝ)*Psi (connectedSaddle (gs j) (ns j)))/
      Real.sqrt ((complexity (gs j) 1:ℝ)*euler Psi (connectedSaddle (gs j) (ns j)))) atTop (𝓝 0) := by
    simp only [hnc,fun j=>(hs j).2.1,sub_self,zero_div]
    exact tendsto_const_nhds
  have ht := cusp_local_limit P 1 (by omega) gs
    (fun j=>connectedSaddle (gs j) (ns j)) (fun j=>ns j-1) 0 hg (fun j=>(hs j).1) hmean hoff
  simpa only [zero_pow (by omega : 2≠0),neg_zero,zero_div,Real.exp_zero] using ht

lemma connectedSaddle_denominator_positive_lower (P:PsiTheory)
    (gs ns:ℕ→ℕ) (hg:Tendsto gs atTop atTop) (hn:Tendsto ns atTop atTop)
    (hg2:∀j,2≤gs j) (hn2:∀j,2≤ns j) :
    ∀ᶠj:ℕ in atTop,
      1/(2*Real.sqrt (2*Real.pi))≤
        Real.sqrt ((complexity (gs j) 1:ℝ)*euler Psi (connectedSaddle (gs j) (ns j)))*
          cuspMass P (gs j) 1 (ns j-1) (connectedSaddle (gs j) (ns j)) := by
  have ht := connectedSaddle_denominator_scaled_limit P gs ns hg hn hg2 hn2
  have hc : 0<1/Real.sqrt (2*Real.pi) := by positivity
  have hh : 1/(2*Real.sqrt (2*Real.pi))<1/Real.sqrt (2*Real.pi) := by
    convert half_lt_self hc using 1 <;>ring
  exact (ht.eventually (lt_mem_nhds hh)).mono (fun j hj=>hj.le)
end WP.TightConnected
