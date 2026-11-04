import WPFormalization.HigherOrder.ProfileSplitting
import WPFormalization.Analysis.KernelPolynomialTails
import WPFormalization.Statements.TopologyTails
/-! The actual central profile-splitting tail is controlled by the original
C.5 all-zero topology mass. Genuine uniform kernel moments propagate this
bound through every finite node-degree kernel prefix, giving a forcing term
uniform in marking count, genus, degree, loss, parameter and prefix length. -/
noncomputable section
namespace WP.HigherOrder
open Set

lemma recursiveSeparating_zero_mass_nonneg (P:PsiTheory)(g n L:ℕ)(hg:2 ≤ g)
    (Y:ℝ)(hY:Y∈Icc (0:ℝ) y₀) :
    0 ≤ markedSplitLossTail P g (n+1) 1 L Y := by
  unfold markedSplitLossTail markedSplitLossTailGenus
  apply Finset.sum_nonneg
  intro j hj
  apply Finset.sum_nonneg
  intro s hs
  have hs':s ≤ n := by have :=Finset.mem_range.mp hs;omega
  split_ifs
  · unfold markedSplitTerm
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (W_nonneg P j (s+1) (by omega) Y hY))
        (W_nonneg P (g-j) (n+1-s) (by omega) Y hY)
    · exact (W_pos P g (n+1) (by omega) (by unfold Stable;omega) Y hY).le
  · exact le_rfl

lemma recursiveSeparating_tail_kernel_prefix :
    ∃C:ℝ,0<C ∧ ∀P:PsiTheory,∀g t L:ℕ,∀d:List ℕ,2 ≤ g → ∀N:ℕ,
      ∀Y∈Icc (0:ℝ) y₀,
        |∑l∈Finset.range N,weight Y l*(recursiveSeparatingTail P g (t+l) L d Y/2)| ≤
          C*((t:ℝ)+1)*markedSplitLossTail P g (d.length+1) 1 L Y := by
  obtain ⟨C,hC,hMoment⟩:=WP.Analysis.weight_polynomial_prefix_uniform 1
  refine ⟨C,hC,?_⟩
  intro P g t L d hg N Y hY
  let T:ℝ:=markedSplitLossTail P g (d.length+1) 1 L Y
  have hT:0 ≤ T:=recursiveSeparating_zero_mass_nonneg P g d.length L hg Y hY
  have hpos(l:ℕ):0 ≤ recursiveSeparatingTail P g (t+l) L d Y :=
    recursiveSeparatingTail_nonneg P g (t+l) L d hg Y hY
  have hbound(l:ℕ):recursiveSeparatingTail P g (t+l) L d Y/2 ≤ ((t:ℝ)+l+1)*T := by
    have hb:=recursiveSeparatingTail_le_zero P g (t+l) L d hg Y hY
    have hc:(((t+l-1:ℕ):ℝ)) ≤ (t:ℝ)+l+1 := by exact_mod_cast (show t+l-1 ≤ t+l+1 by omega)
    have he:=mul_le_mul_of_nonneg_right hc hT
    change recursiveSeparatingTail P g (t+l) L d Y ≤ (((t+l-1:ℕ):ℝ))*T at hb
    linarith [hpos l]
  rw [abs_of_nonneg (Finset.sum_nonneg (fun l hl=>mul_nonneg (weight_nonneg Y hY l) (div_nonneg (hpos l) (by norm_num))))]
  calc
    _ ≤ ∑l∈Finset.range N,weight Y l*(((t:ℝ)+l+1)*T) := by
      apply Finset.sum_le_sum
      intro l hl
      exact mul_le_mul_of_nonneg_left (hbound l) (weight_nonneg Y hY l)
    _=T*(∑l∈Finset.range N,((t:ℝ)+l+1)^1*weight Y l) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      ring
    _ ≤ T*(C*((t:ℝ)+1)) := by
      apply mul_le_mul_of_nonneg_left _ hT
      simpa only [pow_one] using hMoment Y hY t N
    _=_ := by ring

lemma recursiveSeparating_tail_uniform_forcing (P:PsiTheory) :
    ∃C B:ℝ,0<C ∧ 0<B ∧ ∃H:ℕ,∀g p:ℕ,1 ≤ p → 2 ≤ g →
      H ≤ complexity g p → (p:ℝ) ≤ 4*Real.sqrt (complexity g p:ℝ) →
      ∀L:ℕ,2 ≤ L → (L:ℝ) ≤ Real.sqrt (complexity g p:ℝ) →
      ∀t:ℕ,∀d:List ℕ,d.length+1=p → ∀N:ℕ,∀Y∈Icc (0:ℝ) y₀,
        |∑l∈Finset.range N,weight Y l*(recursiveSeparatingTail P g (t+l) L d Y/2)| ≤
          C*((t:ℝ)+1)*(B*((p:ℝ)+L)/(complexity g p:ℝ))^L := by
  obtain ⟨C₁,hC₁,hPrefix⟩:=recursiveSeparating_tail_kernel_prefix
  obtain ⟨C,B,hC,hB,H,hS,hT⟩:=topology_tails P 4 (by norm_num)
  refine ⟨C₁*C,B,by positivity,hB,H,?_⟩
  intro g p hp hg hH hpM L hL hLroot t d hd N Y hY
  have hb:=hPrefix P g t L d hg N Y hY
  rw [hd] at hb
  have ht:=hS g p hp hH hpM L hL hLroot Y hY
  change markedSplitLossTail P g p 1 L Y ≤ _ at ht
  apply hb.trans
  have he:=mul_le_mul_of_nonneg_left ht (show 0 ≤ C₁*((t:ℝ)+1) by positivity)
  convert he using 1 <;> ring

end WP.HigherOrder
