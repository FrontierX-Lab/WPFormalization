import WPFormalization.External.PainleveAnalyticData
import WPFormalization.HigherOrder.PureEndpoint
/-!
The fixed-order one-instanton coefficients in the classical GIKM coordinate
coincide with the paper's canonical rational jump coefficients after multiplication
by the action to the power of the order.  The proof uses the two actual recursions,
including the even-index restriction in GIKM (1.7); no matching assumption is added.
-/

noncomputable section
namespace WP.HigherOrder
open Set

lemma instanton_half_index_sum (a b : ℕ → ℝ) (n : ℕ) :
    (∑ l∈Finset.range n,b l*(if (n+2-l)%2=0 then a ((n+2-l)/2) else 0))=
      ∑ g∈Finset.Icc 2 ((n+2)/2),b (n+2-2*g)*a g := by
  simp_rw [mul_ite,mul_zero]
  rw [←Finset.sum_filter]
  apply Finset.sum_bij (fun l _ => (n+2-l)/2)
  · intro l hl
    obtain ⟨hl,he⟩ := Finset.mem_filter.mp hl
    have hl' := Finset.mem_range.mp hl
    apply Finset.mem_Icc.mpr
    constructor <;> omega
  · intro l hl k hk heq
    obtain ⟨hl,hle⟩ := Finset.mem_filter.mp hl
    obtain ⟨hk,hke⟩ := Finset.mem_filter.mp hk
    have hl' := Finset.mem_range.mp hl
    have hk' := Finset.mem_range.mp hk
    omega
  · intro g hg
    obtain ⟨hg2,hgn⟩ := Finset.mem_Icc.mp hg
    refine ⟨n+2-2*g,?_,?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_range.mpr (by omega)
      · omega
    · omega
  · intro l hl
    obtain ⟨hl,he⟩ := Finset.mem_filter.mp hl
    have hl' := Finset.mem_range.mp hl
    rw [show n+2-2*((n+2-l)/2)=l by omega]

def scaledInstanton (G : External.PainleveAnalytic.GIKMData) (n : ℕ) : ℝ :=
  External.painleveAction^n*G.b n
lemma scaledInstanton_recursion (G : External.PainleveAnalytic.GIKMData) (n : ℕ) :
    2*((n+1:ℕ):ℝ)*scaledInstanton G (n+1)=
      (∑g∈Finset.Icc 2 ((n+2)/2),(G.a g:ℝ)*External.painleveAction^(2*g)*
        scaledInstanton G (n+2-2*g))-
      ((n:ℝ)*(n+1)+1/4)*scaledInstanton G n := by
  have hA : 0<External.painleveAction := painleveAction_pos
  have hn0 : (n:ℝ)+1≠0 := by positivity
  have hb : 2*((n+1:ℕ):ℝ)*scaledInstanton G (n+1)=
      (192/25:ℝ)*External.painleveAction^n*
        (∑g∈Finset.Icc 2 ((n+2)/2),G.b (n+2-2*g)*(G.a g:ℝ))-
      (1/4:ℝ)*(2*(n:ℝ)+1)^2*scaledInstanton G n := by
    unfold scaledInstanton
    rw [G.b_recursion,instanton_half_index_sum (fun g:ℕ => (G.a g:ℝ)) G.b n]
    simp only [External.PainleveAnalytic.action]
    rw [pow_succ]
    push_cast
    field_simp [hA.ne',hn0] <;> ring
  have hs : (192/25:ℝ)*External.painleveAction^n*
        (∑g∈Finset.Icc 2 ((n+2)/2),G.b (n+2-2*g)*(G.a g:ℝ))=
      ∑g∈Finset.Icc 2 ((n+2)/2),(G.a g:ℝ)*External.painleveAction^(2*g)*
        scaledInstanton G (n+2-2*g) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g hg
    obtain ⟨hg2,hgn⟩ := Finset.mem_Icc.mp hg
    have hidx : 2*g+(n+2-2*g)=n+2 := by omega
    have hp : External.painleveAction^(2*g)*External.painleveAction^(n+2-2*g)=
        External.painleveAction^(n+2) := by rw [←pow_add,hidx]
    unfold scaledInstanton
    calc
      _ = (G.a g:ℝ)*(External.painleveAction^n*External.painleveAction^2)*G.b (n+2-2*g) := by rw [painleveAction_sq];ring
      _ = (G.a g:ℝ)*External.painleveAction^(n+2)*G.b (n+2-2*g) := by rw [pow_add]
      _ = _ := by rw [←hp];ring
  rw [hs] at hb
  convert hb using 1 <;> ring

lemma jumpCoefficient_real_scaled_recursion (n : ℕ) :
    2*((n+1:ℕ):ℝ)*(jumpCoefficient (n+1):ℝ)=
      (∑g∈Finset.Icc 2 ((n+2)/2),(zeroInstantonCoefficient g:ℝ)*External.painleveAction^(2*g)*
        (jumpCoefficient (n+2-2*g):ℝ))-
      ((n:ℝ)*(n+1)+1/4)*(jumpCoefficient n:ℝ) := by
  have hM : 1≤(n+2)/2 := by omega
  have hfin : Finset.Icc 1 ((n+2)/2)=insert 1 (Finset.Icc 2 ((n+2)/2)) := by
    ext g
    simp only [Finset.mem_Icc,Finset.mem_insert]
    omega
  have hr := jumpCoefficient_recursion n
  rw [hfin,Finset.sum_insert (by simp),jumpPotential_one,
    show n+2-2*1=n by omega] at hr
  have hreal := congrArg (fun q:ℚ => (q:ℝ)) hr
  push_cast at hreal
  have hsum : (∑g∈Finset.Icc 2 ((n+2)/2),(jumpPotential g:ℝ)*(jumpCoefficient (n+2-2*g):ℝ))=
      -(∑g∈Finset.Icc 2 ((n+2)/2),(zeroInstantonCoefficient g:ℝ)*External.painleveAction^(2*g)*
        (jumpCoefficient (n+2-2*g):ℝ)) := by
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro g hg
    have hg2 := (Finset.mem_Icc.mp hg).1
    have hq : jumpPotential g= -zeroInstantonCoefficient g*(192/25:ℚ)^g := by
      simp [jumpPotential,show g≠0 by omega,show g≠1 by omega]
    rw [hq]
    push_cast
    rw [pow_mul,painleveAction_sq]
    ring
  rw [hsum] at hreal
  have hn0 : (2:ℝ)*((n:ℝ)+1)≠0 := by positivity
  have hh := (eq_div_iff hn0).mp hreal
  push_cast at hh ⊢
  linear_combination hh


/-- The classical fixed-order jump coefficients have the paper's normalization. -/
lemma scaledInstanton_eq_jumpCoefficient (G : External.PainleveAnalytic.GIKMData) (n : ℕ) :
    scaledInstanton G n = (jumpCoefficient n : ℝ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [scaledInstanton, G.b_zero, jumpCoefficient_zero]
    | succ n =>
      have hs := scaledInstanton_recursion G n
      have hj := jumpCoefficient_real_scaled_recursion n
      have hsum :
          (∑ g∈Finset.Icc 2 ((n+2)/2),(G.a g:ℝ)*External.painleveAction^(2*g)*
            scaledInstanton G (n+2-2*g)) =
          (∑ g∈Finset.Icc 2 ((n+2)/2),(zeroInstantonCoefficient g:ℝ)*
            External.painleveAction^(2*g)*(jumpCoefficient (n+2-2*g):ℝ)) := by
        apply Finset.sum_congr rfl
        intro g hg
        obtain ⟨hg2,hgn⟩ := Finset.mem_Icc.mp hg
        rw [G.sourceCoefficient_eq_actual, ih (n+2-2*g) (by omega)]
      rw [hsum, ih n (by omega)] at hs
      have hn0 : (2:ℝ)*((n+1:ℕ):ℝ)≠0 := by positivity
      exact mul_left_cancel₀ hn0 (hs.trans hj.symm)

/-- Explicit rescaling identity used when transporting the fixed-order PI jump. -/
theorem instantonCoefficient_rescaling (G : External.PainleveAnalytic.GIKMData) (n : ℕ) :
    External.painleveAction ^ n * G.b n = (jumpCoefficient n : ℝ) :=
  scaledInstanton_eq_jumpCoefficient G n

end WP.HigherOrder
