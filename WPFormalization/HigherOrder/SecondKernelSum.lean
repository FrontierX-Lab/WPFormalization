import WPFormalization.Marked.SecondDegreeLayer
import WPFormalization.HigherOrder.SecondProfileGrowth
import WPFormalization.Analysis.WeightedPolynomialPrefix

/-! Actual absolute kernel summation identifies the second recursion-layer coefficient with the fixed Appendix C.1 formula. -/
noncomputable section
open Set
noncomputable section
open Set
namespace WP.HigherOrder
lemma weight_cutoff_hasSum (Y : ℝ) (hY : Y∈Icc (0:ℝ) y₀) (j t : ℕ) :
    HasSum (fun l : ℕ => if j ≤ t+l then weight Y l else 0) (tailWeight Y (j-t)) := by
  let N := j-t
  let f : ℕ→ℝ := fun l => if j ≤ t+l then weight Y l else 0
  have hs : Summable (fun l => weight Y (l+N)) :=
    (summable_nat_add_iff N).2 (Analysis.weight_hasSum_at_one Y hY).summable
  have hshift : (fun l : ℕ => f (l+N))=(fun l => weight Y (l+N)) := by
    funext l
    dsimp [f,N]
    rw [if_pos (by omega)]
  have hzero : (∑ i∈Finset.range N,f i)=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi' := Finset.mem_range.mp hi
    dsimp [f,N] at *
    exact if_neg (by omega)
  have he : HasSum (fun l : ℕ => f (l+N)) (tailWeight Y N) := by
    rw [hshift]
    exact hs.hasSum
  have hall := he.sum_range_add
  rw [hzero,zero_add] at hall
  exact hall
end WP.HigherOrder
namespace WP.HigherOrder
lemma secondDegreeCountLayer_hasSum (Y : ℝ) (hY : Y∈Icc (0:ℝ) y₀) (t : ℕ) (d : List ℕ) :
    HasSum (fun l : ℕ => weight Y l*secondDegreeCountLayer Y t d l)
      (secondIncrement Y 0 (t::d)) := by
  let m (j l : ℕ) : ℝ := if 1 ≤ t+d[j]!+l then weight Y l*
    (1-transportBeta d.length Y-degreeCorrection ((t+d[j]!+l-1)::d.eraseIdx j) Y) else 0
  let f (l : ℕ) : ℝ := if 2 ≤ t+l then weight Y l*
    (∑ u∈Finset.range (t+l-1),(1-transportBeta (d.length+2) Y-alpha (d.length+1) Y-
      degreeCorrection (u::(t+l-2-u)::d) Y)) else 0
  let b : ℝ := (Nat.choose (zeros d) 2:ℝ)+theta Y 1/2
  have hm : HasSum (fun l : ℕ => ∑ j∈Finset.range d.length,(A Y*(2*(d[j]!:ℝ)+1))*m j l)
      (∑ j∈Finset.range d.length,(A Y*(2*(d[j]!:ℝ)+1))*(∑'l : ℕ,m j l)) := by
    apply hasSum_sum
    intro j hj
    exact (second_merger_front_summable Y hY t d j (Finset.mem_range.mp hj)).hasSum.mul_left _
  have hf : HasSum (fun l : ℕ => 2*A Y*f l) (2*A Y*(∑'l : ℕ,f l)) :=
    (second_handle_front_summable Y hY t d).hasSum.mul_left _
  have h₂ := (weight_cutoff_hasSum Y hY 2 t).mul_left ((A Y)^2*b)
  have h₃ := (weight_cutoff_hasSum Y hY 3 t).mul_left ((A Y)^2/2)
  have hfull := ((hm.add hf).add h₂).add h₃
  have hmBody (l : ℕ) : (∑ j∈Finset.range d.length,(A Y*(2*(d[j]!:ℝ)+1))*m j l)=
      weight Y l*(A Y*(∑ j∈Finset.range d.length,(2*(d[j]!:ℝ)+1)*
        (if 1 ≤ t+d[j]!+l then 1-transportBeta d.length Y-degreeCorrection (mergerProfile t d l j) Y else 0))) := by
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [m]
    by_cases hn : 1 ≤ t+d[j]!+l
    · rw [if_pos hn,if_pos hn]
      unfold mergerProfile
      ring
    · simp only [if_neg hn,mul_zero]
  have hfBody (l : ℕ) : 2*A Y*f l=weight Y l*(2*A Y*
      (∑ u∈Finset.range (t+l-1),(1-transportBeta (d.length+2) Y-alpha (d.length+1) Y-
        degreeCorrection (contractionProfile t d l u) Y))) := by
    dsimp [f]
    by_cases hn : 2 ≤ t+l
    · rw [if_pos hn]
      unfold contractionProfile
      ring
    · have he : t+l-1=0 := by omega
      simp only [if_neg hn,he,Finset.range_zero,Finset.sum_empty,mul_zero]
  convert hfull using 1
  · funext l
    rw [hmBody l,hfBody l]
    dsimp [secondDegreeCountLayer,b]
    by_cases h₂ : 2 ≤ t+l <;> by_cases h₃ : 3 ≤ t+l <;>
      simp only [h₂,h₃,ite_true,ite_false,mul_zero] <;> ring
  · change A Y*(∑ j∈Finset.range d.length,(2*(d[j]!:ℝ)+1)*(∑'l : ℕ,m j l))+
        2*A Y*(∑'l : ℕ,f l)+(A Y)^2*(b*tailWeight Y (2-t)+tailWeight Y (3-t)/2)=
        (∑ j∈Finset.range d.length,(A Y*(2*(d[j]!:ℝ)+1))*(∑'l : ℕ,m j l))+
          2*A Y*(∑'l : ℕ,f l)+(A Y)^2*b*tailWeight Y (2-t)+(A Y)^2/2*tailWeight Y (3-t)
    rw [Finset.mul_sum]
    simp only [mul_assoc]
    ring
end WP.HigherOrder
