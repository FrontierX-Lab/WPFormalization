import WPFormalization.HigherOrder.SecondHeadDegree
import WPFormalization.Analysis.UniformKernelMoments
import WPFormalization.HigherOrder.SecondKernelSum

/-! Absolute kernel summation identifies the actual head increment with its cubic and three exceptional values. -/
noncomputable section
namespace WP.HigherOrder

lemma kernelMoment_hasSum (j : ℕ) (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀) :
    HasSum (fun l : ℕ=>(l:ℝ)^j*weight Y l) (kernelMoment j Y) := by
  obtain ⟨M,hM⟩:=uniform_kernel_moments.2 j
  have hs : Summable (fun l : ℕ=>(l:ℝ)^j*weight Y l) :=
    Summable.of_nonneg_of_le (fun l=>mul_nonneg (by positivity) (weight_nonneg Y hY l))
      (fun l=>mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg l) (by linarith) j)
        (weight_nonneg Y hY l)) (hM Y hY).1
  exact hs.hasSum

lemma rInfinity_hasSum (p : ℕ) (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀) (x : ℝ) :
    HasSum (fun l : ℕ=>weight Y l*rInfinity p Y (x+l))
      ((1-transportBeta (p-1) Y-A Y*(4-(p:ℝ)))*Theta Y+
        (-A Y*(((p:ℝ)-5)*Theta Y+2*moment₁ Y))*(Theta Y*x+moment₁ Y)+
        (-A Y*Theta Y)*(Theta Y*x^2+2*moment₁ Y*x+kernelMoment 2 Y)) := by
  let r₀:=1-transportBeta (p-1) Y-A Y*(4-(p:ℝ))
  let r₁:= -A Y*(((p:ℝ)-5)*Theta Y+2*moment₁ Y)
  let r₂:= -A Y*Theta Y
  have h₀:=kernelMoment_hasSum 0 Y hY
  have h₁:=kernelMoment_hasSum 1 Y hY
  have h₂:=kernelMoment_hasSum 2 Y hY
  simp only [pow_zero,one_mul,kernelMoment_zero] at h₀
  simp only [pow_one,kernelMoment_one] at h₁
  have hs:=((h₀.mul_left (r₀+r₁*x+r₂*x^2)).add (h₁.mul_left (r₁+2*r₂*x))).add
    (h₂.mul_left r₂)
  convert! hs using 1
  · ext l
    dsimp [rInfinity,r₀,r₁,r₂]
    ring
  · dsimp [r₀,r₁,r₂]
    ring

lemma sInfinity_hasSum (p : ℕ) (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀) (x : ℝ) :
    let c:=1-transportBeta (p+1) Y-alpha p Y
    let s₀:=c+A Y
    let s₁:=c-A Y*(((p:ℝ)-3)*Theta Y+2*moment₁ Y+5-2*p)
    let s₂:= -A Y*(((p:ℝ)-2)*Theta Y+2*moment₁ Y)
    let s₃:= -A Y*Theta Y
    HasSum (fun l : ℕ=>weight Y l*sInfinity p Y (x+l))
      (s₀*Theta Y+s₁*(Theta Y*x+moment₁ Y)+
        s₂*(Theta Y*x^2+2*moment₁ Y*x+kernelMoment 2 Y)+
        s₃*(Theta Y*x^3+3*moment₁ Y*x^2+3*kernelMoment 2 Y*x+kernelMoment 3 Y)) := by
  dsimp only
  let c:=1-transportBeta (p+1) Y-alpha p Y
  let s₀:=c+A Y
  let s₁:=c-A Y*(((p:ℝ)-3)*Theta Y+2*moment₁ Y+5-2*p)
  let s₂:= -A Y*(((p:ℝ)-2)*Theta Y+2*moment₁ Y)
  let s₃:= -A Y*Theta Y
  have h₀:=kernelMoment_hasSum 0 Y hY
  have h₁:=kernelMoment_hasSum 1 Y hY
  have h₂:=kernelMoment_hasSum 2 Y hY
  have h₃:=kernelMoment_hasSum 3 Y hY
  simp only [pow_zero,one_mul,kernelMoment_zero] at h₀
  simp only [pow_one,kernelMoment_one] at h₁
  have hs:=(((h₀.mul_left (s₀+s₁*x+s₂*x^2+s₃*x^3)).add
    (h₁.mul_left (s₁+2*s₂*x+3*s₃*x^2))).add
      (h₂.mul_left (s₂+3*s₃*x))).add (h₃.mul_left s₃)
  convert! hs using 1
  · ext l
    dsimp [sInfinity,c,s₀,s₁,s₂,s₃]
    ring
  · dsimp [c,s₀,s₁,s₂,s₃]
    ring

lemma unrestricted_second_head_hasSum (p : ℕ) (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀) (t : ℝ) :
    HasSum (fun l : ℕ=>weight Y l*(A Y*(p-1:ℝ)*rInfinity p Y (t+l-1)+
      2*A Y*sInfinity p Y (t+l-2)+
      (A Y)^2*((Nat.choose (p-1) 2:ℝ)+theta Y 1/2+1/2)))
      ((cubicIncrement p Y).eval t) := by
  have h₀:=kernelMoment_hasSum 0 Y hY
  simp only [pow_zero,one_mul,kernelMoment_zero] at h₀
  have hs:=(((rInfinity_hasSum p Y hY (t-1)).mul_left (A Y*(p-1:ℝ))).add
    ((sInfinity_hasSum p Y hY (t-2)).mul_left (2*A Y))).add
      (h₀.mul_left ((A Y)^2*((Nat.choose (p-1) 2:ℝ)+theta Y 1/2+1/2)))
  convert! hs using 1
  · ext l
    congr 1 <;>ring
  · simp only [cubicIncrement,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_sub,
      Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_pow]
    norm_num
    <;> ring
lemma head_cutoff_hasSum (f : ℕ→ℝ) (S : ℝ) (hs : HasSum f S) (N : ℕ) :
    HasSum (fun d : ℕ=>if N≤d then f d else 0) (S-∑d∈Finset.range N,f d) := by
  let F : ℕ→ℝ:=fun d=>if N≤d then f d else 0
  have hshift : HasSum (fun d=>f (d+N)) (S-∑d∈Finset.range N,f d) := by
    apply (hasSum_nat_add_iff N).mpr
    convert! hs using 1
    ring
  have he : HasSum (fun d=>F (d+N)) (S-∑d∈Finset.range N,f d) := by
    simpa only [F,show ∀d:ℕ,N≤d+N by omega,ite_true] using hshift
  have hprefix : (∑d∈Finset.range N,F d)=0 := by
    apply Finset.sum_eq_zero
    intro d hd
    dsimp [F]
    rw [if_neg (by have hi:=Finset.mem_range.mp hd;omega)]
  have hh:=he.sum_range_add
  simpa only [hprefix,zero_add] using hh

lemma head_shift_spike_hasSum (Y c : ℝ) (n t : ℕ) :
    HasSum (fun l : ℕ=>if t+l=n then weight Y l*c else 0)
      (if t≤n then weight Y (n-t)*c else 0) := by
  by_cases ht : t≤n
  · rw [if_pos ht]
    convert! hasSum_ite_eq (n-t) (weight Y (n-t)*c) using 1
    ext l
    by_cases he : t+l=n
    · have hl : l=n-t := by omega
      subst l
      simp only [he,ite_true]
    · have hl : l≠n-t := by omega
      simp only [he,hl,ite_false]
  · rw [if_neg ht]
    have he : (fun l : ℕ=>if t+l=n then weight Y l*c else 0)=(fun _ : ℕ=>0) := by
      funext l
      rw [if_neg (by omega)]
    rw [he]
    exact hasSum_zero

lemma secondIncrement_head_eq_cubic (p t : ℕ) (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀) :
    secondIncrement Y 0 (t::List.replicate p (0:ℕ))=
      (cubicIncrement (p+1) Y).eval (t:ℝ)+exceptionalIncrement (p+1) t Y := by
  have hr:=rInfinity_hasSum (p+1) Y hY ((t:ℝ)-1)
  have hs:=sInfinity_hasSum (p+1) Y hY ((t:ℝ)-2)
  dsimp only at hs
  have h₀:=kernelMoment_hasSum 0 Y hY
  simp only [pow_zero,one_mul,kernelMoment_zero] at h₀
  have he₁ (l:ℕ) : (t:ℝ)-1+l=(t:ℝ)+l-1 := by ring
  have he₂ (l:ℕ) : (t:ℝ)-2+l=(t:ℝ)+l-2 := by ring
  simp_rw [he₁] at hr
  simp_rw [he₂] at hs
  have hrCut:=head_cutoff_hasSum _ _ hr (1-t)
  have hsCut:=head_cutoff_hasSum _ _ hs (2-t)
  have hsp₁:=head_shift_spike_hasSum Y (A Y*(3-(p:ℝ))) 1 t
  have hsp₂:=head_shift_spike_hasSum Y (A Y) 2 t
  have h₂:=head_cutoff_hasSum _ _ h₀ (2-t)
  have h₃:=head_cutoff_hasSum _ _ h₀ (3-t)
  let z : ℝ:=(Nat.choose p 2:ℝ)+theta Y 1/2
  have hcut:=((((hrCut.add hsp₁).mul_left (A Y*(p:ℝ))).add
    ((hsCut.sub hsp₂).mul_left (2*A Y))).add (h₂.mul_left ((A Y)^2*z))).add
      (h₃.mul_left ((A Y)^2/2))
  have huncut:=((hr.mul_left (A Y*(p:ℝ))).add (hs.mul_left (2*A Y))).add
    (h₀.mul_left ((A Y)^2*(z+1/2)))
  have hfull:=unrestricted_second_head_hasSum (p+1) Y hY (t:ℝ)
  have hhfull : HasSum (fun l:ℕ=> A Y*(p:ℝ)*(weight Y l*rInfinity (p+1) Y ((t:ℝ)+l-1))+
      2*A Y*(weight Y l*sInfinity (p+1) Y ((t:ℝ)+l-2))+
      (A Y)^2*(z+1/2)*weight Y l) ((cubicIncrement (p+1) Y).eval (t:ℝ)) := by
    convert! hfull using 1
    funext l
    simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
    dsimp [z]
    ring
  have hv:=huncut.unique hhfull
  have ht : HasSum (fun l:ℕ=>weight Y l*secondDegreeCountLayer Y t (List.replicate p (0:ℕ)) l)
      ((cubicIncrement (p+1) Y).eval (t:ℝ)+exceptionalIncrement (p+1) t Y) := by
    convert! hcut using 1
    · funext l
      rw [secondDegreeCountLayer_head]
      have hc₁ : (1-t≤l)↔(1≤t+l) := by omega
      have hc₂ : (2-t≤l)↔(2≤t+l) := by omega
      have hc₃ : (3-t≤l)↔(3≤t+l) := by omega
      simp only [hc₁,hc₂,hc₃]
      dsimp [z]
      split_ifs
      all_goals first | omega | ring
    · rw [←hv]
      unfold exceptionalIncrement
      simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
      dsimp [z]
      split_ifs <;>ring
  exact (secondDegreeCountLayer_hasSum Y hY t (List.replicate p (0:ℕ))).unique ht

end WP.HigherOrder
