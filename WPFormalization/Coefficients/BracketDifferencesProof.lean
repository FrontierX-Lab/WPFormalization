import WPFormalization.Statements.Coefficients
import WPFormalization.Marked.SingleMarkingProfile
import WPFormalization.Marked.UnmarkedReduction
/-! Original one-boundary bracket differences from the genuine uniform adjacent profile estimate. -/
noncomputable section
namespace WP
open Set

lemma bracketB_eq_normalized_zero (P:PsiTheory)(g k:ℕ)(hg:1≤g)(hk:k≤3*g-2):
    bracketB P g k=(4:ℝ)^(3*g-2)*normalized P g [k] 0:=by
  have hd:dimension g 1=3*g-2:=by unfold dimension;omega
  have hdef:deficit g [k]=3*g-2-k:=by simp only[deficit,List.length_singleton,List.sum_singleton,hd]
  have hn:k+(3*g-2-k)=3*g-2:=Nat.add_sub_of_le hk
  simp only[bracketB,mixedBracket,List.sum_singleton,normalized,
    show (0:ℝ)≠y₀ from ne_of_lt y₀_pos,ite_false,a_zero,one_pow,one_mul,r_zero_parameter,hdef]
  have hpow:(4:ℝ)^(3*g-2)=(4:ℝ)^k*4^(3*g-2-k):=by
    calc
      _=(4:ℝ)^(k+(3*g-2-k)):=congrArg (fun n:ℕ=>(4:ℝ)^n) hn.symm
      _=_:=pow_add _ _ _
  rw[hpow]
  have he:(2*Real.pi^2:ℝ)^ (3*g-2-k)=(4:ℝ)^(3*g-2-k)*(Real.pi^2/2:ℝ)^(3*g-2-k):=by
    rw[←mul_pow]
    congr 1
    ring
  rw[he]
  ring

lemma profile_one_zero_eq_bracket_ratio (P:PsiTheory)(g k:ℕ)(hg:1≤g)(hk:k≤3*g-2):
    profile P g [k] 0=bracketB P g k/volumeModel P g 1:=by
  have hzero:volumeModel P g 1=bracketB P g 0:=by simp[volumeModel,bracketB]
  rw[hzero,bracketB_eq_normalized_zero P g k hg hk,bracketB_eq_normalized_zero P g 0 hg (by omega)]
  unfold profile
  simp only[List.length_singleton,List.replicate_succ,List.replicate_zero]
  have h4:(4:ℝ)^(3*g-2)≠0:=by positivity
  exact (mul_div_mul_left _ _ h4).symm

lemma bracket_differences_proof (P : PsiTheory) : ∃ C : ℝ, 0 < C ∧
    ∀ g : ℕ, 1 ≤ g →
      bracketB P g 0/volumeModel P g 1 = 1 ∧
      ∀ k : ℕ, k < 3*g-2 →
        0 ≤ bracketB P g k/volumeModel P g 1-bracketB P g (k+1)/volumeModel P g 1 ∧
        bracketB P g k/volumeModel P g 1-bracketB P g (k+1)/volumeModel P g 1 ≤
          C*(k+1)/g := by
  obtain ⟨C,hC,hb⟩:=profile_adjacent_one_uniform_bound P
  refine ⟨C,hC,?_⟩
  intro g hg
  have hs:Stable g 1:=by unfold Stable;omega
  have hzero:(0:ℝ)∈Icc (0:ℝ) y₀:=⟨le_rfl,y₀_pos.le⟩
  have hden:0<normalized P g [0] 0:=normalized_pos_valid_nonempty P g [0] (by simp)
    (by simpa only[List.length_singleton] using hs) (by simp[dimension]) 0 hzero
  constructor
  · rw[←profile_one_zero_eq_bracket_ratio P g 0 hg (by omega)]
    simpa only[profile,List.length_singleton,List.replicate_succ,List.replicate_zero] using
      div_self hden.ne'
  · intro k hk
    rw[←profile_one_zero_eq_bracket_ratio P g k hg (by omega),
      ←profile_one_zero_eq_bracket_ratio P g (k+1) hg (by omega)]
    constructor
    · have hmono:=normalized_cons_raise_le P g k [] (by simpa using hs) 0 hzero
      change normalized P g [k+1] 0≤normalized P g [k] 0 at hmono
      have hp:profile P g [k+1] 0≤profile P g [k] 0:=by
        unfold profile
        simp only[List.length_singleton]
        exact div_le_div_of_nonneg_right hmono hden.le
      linarith only[hp]
    · simpa only[Nat.cast_add,Nat.cast_one] using hb g hg k 0 hzero
end WP
