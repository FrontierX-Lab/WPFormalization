import WPFormalization.HigherOrder.SmallComponentCounts
import WPFormalization.HigherOrder.OrderWeights
import WPFormalization.HigherOrder.WeightedRemainderBounds
/-! The true bounded component, label subsets and node range preserve
the sharp S_L^(2L-1) edge remainder scale. A loss-r ratio/profile error
keeps S^(2(L-r)); the genuine Gamma growth, binomial label count and
one normalized kernel moment complete the fixed-loss estimate. -/
noncomputable section
namespace WP.HigherOrder
open Set
lemma selectedNat_cardinality_length (d:List ℕ)(I:Finset ℕ)(hI:I⊆Finset.range d.length) :
    (selectedNat d I).length=I.card := by
  rw[←selectedNat_toNat,List.length_map]
  exact selected_length_card (d.map Int.ofNat) I (by simpa only[List.length_map] using hI)


lemma separating_cardinality_remainder_bound (P:PsiTheory) :
    ∃T₀:ℝ,1 ≤ T₀ ∧∀L j s t:ℕ,∀d:List ℕ,Stable j (s+1)→2 ≤ 2*j+s→2*j+s<L→
    ∀S h D E Cm:ℝ,1 ≤ S→0<h→0 ≤ D→0 ≤ E→0 ≤ Cm→
    (((d.length+(2*j+s):ℕ):ℝ) ≤ S)→(t:ℝ) ≤ S→
    ∀Y∈Icc (0:ℝ) y₀,∀R:Finset ℕ→ℕ→ℕ→ℝ,
    (∀I∈Finset.powersetCard s (Finset.range d.length),∀l:ℕ,∀u∈Finset.range (t+l-1),
      |R I l u| ≤ D^(2*j+s)*(S+l+1)^(2*(L-(2*j+s)))/h^L*E)→
    Summable (fun l:ℕ=>(S+l+1)^(2*(L-(2*j+s))+1)*|weight Y l|)→
    (∑'l:ℕ,(S+l+1)^(2*(L-(2*j+s))+1)*|weight Y l|) ≤ Cm*S^(2*(L-(2*j+s))+1)→
    Summable (fun l:ℕ=>weight Y l*(∑I∈Finset.powersetCard s (Finset.range d.length),
      ∑u∈Finset.range (t+l-1),smallW P Y j (u::selectedNat d I)*R I l u)) ∧
    |∑'l:ℕ,weight Y l*(∑I∈Finset.powersetCard s (Finset.range d.length),
      ∑u∈Finset.range (t+l-1),smallW P Y j (u::selectedNat d I)*R I l u)| ≤
      Cm*(T₀*D)^(2*j+s)*S^(2*L-1)/h^L*E := by
  obtain ⟨T₀,hT₀,hsmall⟩:=smallW_real_uniform_complexity_bound P
  refine ⟨T₀,hT₀,?_⟩
  intro L j s t d hs hr2 hr S h D E Cm hS hh hD hE hCm hlabel ht Y hY R hR hmoment hmomentBound
  let r:=2*j+s
  let q:=L-r
  let G:=Real.Gamma ((r-1:ℕ):ℝ)*T₀^(r-1)
  let W:=fun l:ℕ=>∑I∈Finset.powersetCard s (Finset.range d.length),
      ∑u∈Finset.range (t+l-1),smallW P Y j (u::selectedNat d I)*R I l u
  have hS0:0 ≤ S:=by linarith
  have hT₀0:0 ≤ T₀:=by linarith
  have hG:0 ≤ G:=by
    dsimp[G]
    apply mul_nonneg _ (pow_nonneg hT₀0 _)
    exact (Real.Gamma_pos_of_pos (by exact_mod_cast (show 0<r-1 by dsimp[r];omega))).le
  have hlabelG:(Nat.choose d.length s:ℝ)*G ≤ (T₀*S)^r:=by
    have hb:=small_component_label_norm_bound d.length r s hr2 (by dsimp[r];omega) T₀ S hT₀ hlabel G
      (by rw[Real.norm_eq_abs,abs_of_nonneg hG])
    simpa only[Real.norm_eq_abs,abs_of_nonneg hG] using hb
  have hpoint(l:ℕ):|W l| ≤ ((T₀*S)^r*D^r/h^L*E)*(S+l+1)^(2*q+1):=by
    let C:=D^r*(S+l+1)^(2*q)/h^L*E
    have hC:0 ≤ C:=by dsimp[C];positivity
    have hnode:((t+l-1:ℕ):ℝ) ≤ S+l+1:=by
      have hn:t+l-1 ≤ t+l:=by omega
      have hR:((t+l-1:ℕ):ℝ) ≤ (t:ℝ)+l:=by exact_mod_cast hn
      linarith
    have hsmallTerm(I:Finset ℕ)(hI:I∈Finset.powersetCard s (Finset.range d.length))(u:ℕ):
        |smallW P Y j (u::selectedNat d I)| ≤ G:=by
      have hIs:=(Finset.mem_powersetCard.mp hI).1
      have hcard:=(Finset.mem_powersetCard.mp hI).2
      have hlen:(u::selectedNat d I).length=s+1:=by
        simp only[List.length_cons,selectedNat_cardinality_length d I hIs,hcard]
      have hc:complexity j (u::selectedNat d I).length=r-1:=by rw[hlen];dsimp[r];unfold complexity;omega
      have hb:=hsmall j (u::selectedNat d I) (by simpa only[hlen] using hs) (by rw[hlen];omega) Y hY
      simpa only[hc] using hb
    have hb:|W l| ≤ (Nat.choose d.length s:ℝ)*((t+l-1:ℕ):ℝ)*(G*C):=by
      dsimp[W]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      calc
        _ ≤ ∑I∈Finset.powersetCard s (Finset.range d.length),∑u∈Finset.range (t+l-1),G*C:=by
          apply Finset.sum_le_sum
          intro I hI
          apply (Finset.abs_sum_le_sum_abs _ _).trans
          apply Finset.sum_le_sum
          intro u hu
          rw[abs_mul]
          exact mul_le_mul (hsmallTerm I hI u) (hR I hI l u hu) (abs_nonneg _) hG
        _=_:=by simp only[Finset.sum_const,Finset.card_range,Finset.card_powersetCard,Finset.card_range,nsmul_eq_mul];ring
    apply hb.trans
    have hm:=mul_le_mul hlabelG hnode (Nat.cast_nonneg _) (by positivity:0 ≤ (T₀*S)^r)
    have hm':(Nat.choose d.length s:ℝ)*((t+l-1:ℕ):ℝ)*(G*C) ≤ (T₀*S)^r*(S+l+1)*C:=by
      have hb:=mul_le_mul_of_nonneg_right hm hC
      convert hb using 1 <;>ring
    apply hm'.trans_eq
    dsimp[C]
    rw[pow_succ]
    ring
  let K:ℝ:=(T₀*S)^r*D^r/h^L*E
  have hK:0 ≤ K:=by dsimp[K];positivity
  have hSummable:Summable (fun l:ℕ=>weight Y l*W l):=by
    apply Summable.of_norm
    have hdom:=hmoment.mul_left K
    apply Summable.of_nonneg_of_le (fun l=>norm_nonneg _) _ hdom
    intro l
    rw[Real.norm_eq_abs,abs_mul]
    have hb:=mul_le_mul_of_nonneg_left (hpoint l) (abs_nonneg (weight Y l))
    convert hb using 1 <;>dsimp[K]<;>ring
  refine ⟨hSummable,?_⟩
  have hb:=weighted_actual_remainder_bound (weight Y) W _ S K Cm (2*q+1) hK hSummable.hasSum hmoment hmomentBound hpoint
  apply hb.trans
  have hexp:r+(2*q+1) ≤ 2*L-1:=by dsimp[r,q] at *;omega
  have hPow:S^(r+(2*q+1)) ≤ S^(2*L-1):=pow_le_pow_right₀ hS hexp
  have hmul:=mul_le_mul_of_nonneg_left hPow (by positivity:0 ≤ Cm*(T₀*D)^r/h^L*E)
  convert hmul using 1 <;> (try dsimp[K]) <;> (try simp only[mul_pow,pow_add]) <;>ring

end WP.HigherOrder
