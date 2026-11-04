import WPFormalization.HigherOrder.LinearErrorMajorant
/-! Explicit one-step geometric budgets for the four actual remainder stages.
The analytic operator hypotheses are supplied separately; this module only proves the finite positive majorant calculation. -/

noncomputable section
namespace WP.HigherOrder
lemma linear_error_geometric_budget (A F B K C Q:ℝ) (n:ℕ)
    (hA:0 ≤ A) (hF:0 ≤ F) (hB:0<B) (hK:0 ≤ K) (hC:0 ≤ C) (hQ:0<Q)
    (hBq:2*B ≤ Q) (hres:4*A*K*B ≤ Q) (hforce:2*A*F ≤ C) :
    A*(F*B^n)+A*(∑i∈Finset.Icc 1 n,K*B^i*(C*Q^(n-i))) ≤ C*Q^n := by
  have hratio:0 ≤ B/Q:=div_nonneg hB.le hQ.le
  have hratio2:B/Q ≤ 1/2:=(div_le_iff₀ hQ).mpr (by linarith)
  have hterm (i:ℕ) (hi:i∈Finset.Icc 1 n) :
      K*B^i*(C*Q^(n-i)) = K*C*Q^n*(B/Q)^i := by
    have hin: i ≤ n := (Finset.mem_Icc.mp hi).2
    have hp : B^i*Q^(n-i)=Q^n*(B/Q)^i := by
      rw[div_pow,←mul_div_assoc]
      apply (eq_div_iff (pow_ne_zero i hQ.ne')).mpr
      calc
        _=B^i*(Q^(n-i)*Q^i):=by ring
        _=B^i*Q^n:=by rw[←pow_add,Nat.sub_add_cancel hin]
        _=_:=by ring
    calc
      _=K*C*(B^i*Q^(n-i)):=by ring
      _=_:=by rw[hp];ring
  have hsum : (∑i∈Finset.Icc 1 n,K*B^i*(C*Q^(n-i))) ≤ K*C*Q^n*(2*(B/Q)) := by
    calc
      _ = ∑i∈Finset.Icc 1 n,K*C*Q^n*(B/Q)^i:=Finset.sum_congr rfl hterm
      _=K*C*Q^n*(∑i∈Finset.Icc 1 n,(B/Q)^i):=(Finset.mul_sum _ _ _).symm
      _ ≤ _:=mul_le_mul_of_nonneg_left (sum_Icc_geom_le_two_mul (B/Q) n hratio hratio2) (by positivity)
  have hcon:2*A*K*(B/Q) ≤ 1/2:=by
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    have heq : (2*A*K*(B/Q))*2=(4*A*K*B)/Q := by ring
    rw[heq]
    exact (div_le_iff₀ hQ).mpr (by simpa only [one_mul] using hres)
  have hcpow:0 ≤ C*Q^n:=by positivity
  have hconv:A*(K*C*Q^n*(2*(B/Q))) ≤ (1/2)*(C*Q^n):=by
    convert mul_le_mul_of_nonneg_right hcon hcpow using 1 <;> ring
  have hforcing:A*(F*B^n) ≤ (1/2)*(C*Q^n):=by
    have hp:B^n ≤ Q^n:=pow_le_pow_left₀ hB.le (by linarith) n
    have h₁:=mul_le_mul_of_nonneg_left hp (mul_nonneg hA hF)
    have h₂:=mul_le_mul_of_nonneg_right hforce (pow_nonneg hQ.le n)
    nlinarith
  calc
    _ ≤ A*(F*B^n)+A*(K*C*Q^n*(2*(B/Q))):=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum hA)
    _ ≤ (1/2)*(C*Q^n)+(1/2)*(C*Q^n):=add_le_add hforcing hconv
    _=C*Q^n:=by ring

lemma four_stage_geometric_budget (b F B K C Q:ℝ) (n:ℕ)
    (hb:0 ≤ b) (hF:0 ≤ F) (hB:0<B) (hK:0 ≤ K) (hC:0 ≤ C) (hQ:0<Q)
    (hBq:2*B ≤ Q) (hres:12*(4+4*b+2*b^2)*K*B ≤ Q)
    (hforce:2*(4+4*b+2*b^2)*F ≤ C)
    (E Cₙ H G:ℝ)
    (he:E ≤ F*B^n+∑i∈Finset.Icc 1 n,K*B^i*(C*Q^(n-i)))
    (hc:Cₙ ≤ F*B^n+b*E)
    (hh:H ≤ F*B^n+b*E+∑i∈Finset.Icc 1 n,K*B^i*(C*Q^(n-i)))
    (hg:G ≤ F*B^n+b*(H+Cₙ)+∑i∈Finset.Icc 1 n,K*B^i*(C*Q^(n-i))) :
    E+Cₙ+H+G ≤ C*Q^n := by
  let T:=∑i∈Finset.Icc 1 n,K*B^i*(C*Q^(n-i))
  have hT:0 ≤ T:=Finset.sum_nonneg (fun i hi=>by positivity)
  have ha:0 ≤ 4+4*b+2*b^2:=by positivity
  have helim:=four_stage_error_elimination b (F*B^n) E Cₙ H G T T T hb (by positivity) hT hT hT he hc hh hg
  have hbudget:=linear_error_geometric_budget (4+4*b+2*b^2) F B (3*K) C Q n ha hF hB
    (by positivity) hC hQ hBq (by nlinarith) hforce
  have hs : (∑i∈Finset.Icc 1 n,3*K*B^i*(C*Q^(n-i)))=3*T := by
    dsimp[T]
    rw[Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw[hs] at hbudget
  apply helim.trans
  convert hbudget using 1 <;> ring
end WP.HigherOrder
