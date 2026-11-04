import Mathlib
/-! Elementary small-weight geometry and inversion control for C.3.
The generic first-order input is used explicitly here; the actual client
instantiates it with the proved growing-marking cusp estimate. -/
noncomputable section
namespace WP.HigherOrder
lemma small_weight_child_geometry (h S n:ℝ) (p L q:ℕ) (hh:0<h)
    (hp:1 ≤ p) (hL:1 ≤ L) (hS:(p:ℝ)+2*L ≤ S)
    (hsmall:S^2/h<1) (hn:h-(L:ℝ) ≤ n) (hq:q ≤ p+L+2) :
    h/2 ≤ n ∧ (q:ℝ) ≤ 4*Real.sqrt n := by
  have hpR:(1:ℝ) ≤ p:=by exact_mod_cast hp
  have hLR:(1:ℝ) ≤ L:=by exact_mod_cast hL
  have hqR:(q:ℝ) ≤ (p:ℝ)+L+2:=by exact_mod_cast hq
  have hq0:(0:ℝ) ≤ q:=Nat.cast_nonneg _
  have hS0:0 ≤ S:=by linarith
  have hs2:S^2<h:=(div_lt_one hh).mp hsmall
  have hSq:4*(L:ℝ)^2 ≤ S^2:=by
    have htwo:0 ≤ S-2*(L:ℝ):=by linarith
    nlinarith [mul_nonneg htwo (show 0 ≤ S+2*(L:ℝ) by positivity)]
  have hLh:2*(L:ℝ) ≤ h:=by nlinarith
  have hn2:h/2 ≤ n:=by linarith
  have hn0:0 ≤ n:=by linarith
  have hqS:(q:ℝ) ≤ 2*S:=by linarith
  have hqSq:(q:ℝ)^2 ≤ 4*S^2:=by
    nlinarith [mul_nonneg (sub_nonneg.mpr hqS) (show 0 ≤ 2*S+(q:ℝ) by positivity)]
  refine ⟨hn2,?_⟩
  have hr:=Real.sq_sqrt hn0
  have hr0:=Real.sqrt_nonneg n
  by_contra hbad
  have hbad':4*Real.sqrt n<(q:ℝ):=lt_of_not_ge hbad
  have hprod:=mul_nonneg (sub_nonneg.mpr hbad'.le) (show 0 ≤ (q:ℝ)+4*Real.sqrt n by positivity)
  nlinarith
lemma inverse_lower_from_uniform_first_order (n:ℕ→ℕ→ℕ) (f:ℕ→ℕ→ℝ→ℝ)
    (E:Set ℝ) (C:ℝ) (hC:0<C) (H:ℕ)
    (hfirst:∀g q:ℕ,1 ≤ q→H ≤ n g q→(q:ℝ) ≤ 4*Real.sqrt (n g q:ℝ)→
      ∀Y∈E,|f g q Y-1| ≤ C*((q:ℝ)+1)/(n g q:ℝ)) :
    ∃δ₀:ℝ,0<δ₀ ∧ δ₀ ≤ 1 ∧∀h S:ℝ,0<h→∀p L:ℕ,1 ≤ p→1 ≤ L→
    (p:ℝ)+2*L ≤ S→S^2/h<δ₀→∀g q:ℕ,1 ≤ q→h-(L:ℝ) ≤ (n g q:ℝ)→
    q ≤ p+L+2→∀Y∈E,
      1/2 ≤ f g q Y ∧ |(f g q Y)⁻¹| ≤ 2 :=by
  let K:ℝ:=H+100*C^2+1
  have hK:0<K:=by dsimp[K];positivity
  have hden:0<2*K+1:=by positivity
  refine ⟨1/(2*K+1),by positivity,(div_le_one hden).2 (by linarith),?_⟩
  intro h S hh p L hp hL hS hsmall g q hq hshift hqp Y hY
  have hpR:(1:ℝ) ≤ p:=by exact_mod_cast hp
  have hLR:(1:ℝ) ≤ L:=by exact_mod_cast hL
  have hS1:1 ≤ S:=by linarith
  have hSsq:1 ≤ S^2:=by nlinarith
  have hsmall1:S^2/h<1:=hsmall.trans_le ((div_le_one hden).2 (by linarith))
  obtain ⟨hnHalf,hqRoot⟩:=small_weight_child_geometry h S (n g q:ℝ) p L q
    hh hp hL hS hsmall1 hshift hqp
  have hbig0:S^2*(2*K+1)<h:=by simpa only[one_mul] using (div_lt_div_iff₀ hh hden).mp hsmall
  have hbig:2*K+1<h:=lt_of_le_of_lt (by nlinarith) hbig0
  have hnBig:K<(n g q:ℝ):=by linarith
  have hn0:(0:ℝ)<n g q:=hK.trans hnBig
  have hH:(H:ℝ) ≤ n g q:=by dsimp[K] at hnBig; nlinarith[sq_nonneg C]
  have hHnat:H ≤ n g q:=by exact_mod_cast hH
  have hfirst':=hfirst g q hq hHnat hqRoot Y hY
  have hcErr:|f g q Y-1| ≤ C*((q:ℝ)+1)/(n g q:ℝ):=hfirst'
  have hnOne:(1:ℝ) ≤ n g q:=by dsimp[K] at hnBig; nlinarith[sq_nonneg C,Nat.cast_nonneg (α:=ℝ) H]
  have hr1:1 ≤ Real.sqrt (n g q:ℝ):=Real.one_le_sqrt.mpr hnOne
  have hr0:=Real.sqrt_nonneg (n g q:ℝ)
  have hrsq:=Real.sq_sqrt hn0.le
  have hten:10*C ≤ Real.sqrt (n g q:ℝ):=by
    dsimp[K] at hnBig
    nlinarith[sq_nonneg (Real.sqrt (n g q:ℝ)-10*C),Nat.cast_nonneg (α:=ℝ) H]
  have hmul:=mul_le_mul_of_nonneg_right hten hr0
  have hqplus:(q:ℝ)+1 ≤ 5*Real.sqrt (n g q:ℝ):=by linarith
  have herr:|f g q Y-1| ≤ 1/2:=by
    apply hcErr.trans
    apply (div_le_iff₀ hn0).2
    have hCmul:=mul_le_mul_of_nonneg_left hqplus hC.le
    nlinarith
  have hlow:1/2 ≤ f g q Y:=by have hi:=(abs_le.mp herr).1;linarith
  refine ⟨hlow,?_⟩
  have hpos:0<f g q Y:=by linarith
  rw[abs_inv,abs_of_pos hpos]
  simpa only[one_div] using (one_div_le hpos (by norm_num:(0:ℝ)<2)).2 hlow
end WP.HigherOrder
