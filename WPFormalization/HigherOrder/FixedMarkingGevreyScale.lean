import WPFormalization.HigherOrder.OrderWeights
/-! The true order weight at fixed marking count normalizes to a Gevrey-two factorial, and one square-root order window stays inside the fixed small-weight region. -/
noncomputable section
namespace WP.HigherOrder

lemma nat_self_power_square_factorial (N:ℕ) :
    (N:ℝ)^(2*N) ≤ (Real.exp 2)^N*(N.factorial:ℝ)^2 := by
  have hfac:0<(N.factorial:ℝ):=by exact_mod_cast Nat.factorial_pos N
  have he:=Real.pow_div_factorial_le_exp (N:ℝ) (Nat.cast_nonneg _) N
  have hp:(N:ℝ)^N ≤ Real.exp (N:ℝ)*(N.factorial:ℝ):=(div_le_iff₀ hfac).mp he
  have hExp:(Real.exp (N:ℝ))^2=(Real.exp 2)^N:=by
    rw[←Real.exp_nat_mul,←Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hb:=pow_le_pow_left₀ (pow_nonneg (Nat.cast_nonneg N : (0:ℝ) ≤ N) N) hp 2
  rw[mul_pow,hExp] at hb
  simpa only[←pow_mul,Nat.mul_comm N 2] using hb

lemma fixed_marking_order_weight_factorial (M:ℝ)(hM:0 ≤ M)(p N:ℕ)(hN:1 ≤ N) :
    scalarOrderWeight M N p^(2*N) ≤
      (((p:ℝ)+M)^2*Real.exp 2)^N*(N.factorial:ℝ)^2 := by
  have hNR:(1:ℝ) ≤ N:=by exact_mod_cast hN
  have hS:0 ≤ scalarOrderWeight M N p:=by unfold scalarOrderWeight;positivity
  have hbound:scalarOrderWeight M N p ≤ ((p:ℝ)+M)*N:=by
    unfold scalarOrderWeight
    have hp:0 ≤ (p:ℝ):=Nat.cast_nonneg _
    nlinarith
  have hb:=pow_le_pow_left₀ hS hbound (2*N)
  apply hb.trans
  rw[mul_pow]
  have ht:=mul_le_mul_of_nonneg_left (nat_self_power_square_factorial N)
    (by positivity:0 ≤ ((p:ℝ)+M)^(2*N))
  apply ht.trans_eq
  rw[mul_pow,pow_mul]
  ring

end WP.HigherOrder

namespace WP.HigherOrder
lemma fixed_marking_small_sqrt_window (M:ℝ)(hM:0 ≤ M)(p:ℕ)(hp:1 ≤ p)(δ:ℝ)(hδ:0<δ) :
    ∃c:ℝ,0<c ∧∀h:ℝ,0<h→∀N:ℕ,1 ≤ N→(N:ℝ) ≤ c*Real.sqrt h→
      scalarOrderWeight M N p^2/h<δ := by
  let a:ℝ:=(p:ℝ)+M
  have ha:0<a:=by
    have hpr:(1:ℝ) ≤ p:=by exact_mod_cast hp
    dsimp[a]
    linarith
  let c:=Real.sqrt δ/(2*a)
  have hc:0<c:=div_pos (Real.sqrt_pos.mpr hδ) (by positivity)
  refine ⟨c,hc,?_⟩
  intro h hh N hN hwindow
  have hNR:(1:ℝ) ≤ N:=by exact_mod_cast hN
  have hS:0 ≤ scalarOrderWeight M N p:=by unfold scalarOrderWeight;positivity
  have hs:scalarOrderWeight M N p ≤ a*N:=by
    dsimp[a,scalarOrderWeight]
    have hpr:0 ≤ (p:ℝ):=Nat.cast_nonneg _
    nlinarith
  have hn2:=pow_le_pow_left₀ (Nat.cast_nonneg N : (0:ℝ) ≤ N) hwindow 2
  rw[mul_pow,Real.sq_sqrt hh.le] at hn2
  have hm:=mul_le_mul_of_nonneg_left hn2 (sq_nonneg a)
  have hs2:=pow_le_pow_left₀ hS hs 2
  have hb:scalarOrderWeight M N p^2/h ≤ a^2*c^2:=by
    apply (div_le_iff₀ hh).mpr
    nlinarith
  have he:a^2*c^2=δ/4:=by
    dsimp[c]
    rw[div_pow,Real.sq_sqrt hδ.le]
    field_simp[ha.ne']
    ring
  exact hb.trans_lt (by rw[he];linarith)
end WP.HigherOrder
