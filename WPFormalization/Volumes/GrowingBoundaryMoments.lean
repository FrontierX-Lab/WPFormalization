import WPFormalization.Marked.ExternalStringMoments

/-! The degree moments of the original sinh boundary weights, uniformly for
all boundary lengths. These are polynomial bounds after normalization, with
no fixed compact length box. -/
noncomputable section
namespace WP
open Set Filter BoundaryConvolution
open scoped Topology

lemma boundary_length_moment_succ (L : ℝ) (k : ℕ) :
    ((k+1:ℕ):ℝ)*(((k+1:ℕ):ℝ)+1)*boundaryLengthCoefficient L (k+1) =
      (L^2/8*boundaryLengthCoefficient L k)*((k:ℝ)+2)/(2*k+3) := by
  have hf : (2*(k+1)+1).factorial =
      (2*k+3)*(2*k+2)*(2*k+1).factorial := by
    rw [show 2*(k+1)+1=(2*k+1)+1+1 by omega,
      Nat.factorial_succ,Nat.factorial_succ]
    ring
  unfold boundaryLengthCoefficient
  rw [hf,show 2*(k+1)=2*k+2 by omega,pow_add,pow_succ]
  push_cast
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hfpos : (0:ℝ) < (2*k+1).factorial := by positivity
  field_simp
  ring

lemma boundary_length_moment_succ_le (L : ℝ) (k : ℕ) :
    ((k+1:ℕ):ℝ)*(((k+1:ℕ):ℝ)+1)*boundaryLengthCoefficient L (k+1) ≤
      L^2/8*boundaryLengthCoefficient L k := by
  rw [boundary_length_moment_succ]
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hpos : 0 ≤ L^2/8*boundaryLengthCoefficient L k :=
    mul_nonneg (by positivity) (boundaryLengthCoefficient_nonneg L k)
  apply (div_le_iff₀ (by positivity : (0:ℝ)<2*k+3)).2
  exact mul_le_mul_of_nonneg_left (by linarith : (k:ℝ)+2 ≤ 2*k+3) hpos

theorem boundary_length_quadratic_moment (L : ℝ) :
    Summable (fun k : ℕ => (k:ℝ)*((k:ℝ)+1)*boundaryLengthCoefficient L k) ∧
    (∑' k : ℕ, (k:ℝ)*((k:ℝ)+1)*boundaryLengthCoefficient L k) ≤
      L^2/8*boundaryFactor 0 L := by
  have hs := (boundaryLengthCoefficient_hasSum L).summable.mul_left (L^2/8)
  have hm : Summable (fun k : ℕ => ((k+1:ℕ):ℝ)*(((k+1:ℕ):ℝ)+1)*
      boundaryLengthCoefficient L (k+1)) :=
    hs.of_nonneg_of_le (fun k => mul_nonneg (by positivity)
      (boundaryLengthCoefficient_nonneg L (k+1))) (boundary_length_moment_succ_le L)
  have hm' : Summable (fun k : ℕ => (k:ℝ)*((k:ℝ)+1)*boundaryLengthCoefficient L k) :=
    (summable_nat_add_iff 1).mp hm
  refine ⟨hm',?_⟩
  have he := hm'.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one,Nat.cast_zero,zero_mul,zero_add] at he
  rw [←he]
  calc _ ≤ ∑' k : ℕ, L^2/8*boundaryLengthCoefficient L k :=
         hm.tsum_le_tsum (boundary_length_moment_succ_le L) hs
       _ = _ := by rw [tsum_mul_left,(boundaryLengthCoefficient_hasSum L).tsum_eq]

theorem boundary_degree_quadratic_moment (n : ℕ) (hn : 1 ≤ n) (L : Fin n → ℝ) :
    Summable (fun d : Fin n → ℕ =>
      boundaryProfileMoment d * boundaryDegreeWeight n L d) ∧
    (∑' d : Fin n → ℕ, boundaryProfileMoment d * boundaryDegreeWeight n L d) ≤
      ((n:ℝ)/8 * ∑ i, (L i)^2) * ∏ i, boundaryFactor 0 (L i) := by
  let w : Fin n → ℕ → ℝ := fun i => boundaryLengthCoefficient (L i)
  have hw (i : Fin n) : Summable (w i) := (boundaryLengthCoefficient_hasSum (L i)).summable
  have hwn (i : Fin n) (k : ℕ) : 0 ≤ w i k := boundaryLengthCoefficient_nonneg _ _
  have hm (i : Fin n) := boundary_length_quadratic_moment (L i)
  refine ⟨boundary_tuple_moment_summable hn w hw hwn (fun i => (hm i).1),?_⟩
  apply (boundary_tuple_moment_tsum_le hn w hw hwn (fun i => (hm i).1)).trans
  have ht (i : Fin n) :
      (∑' k : ℕ, (k:ℝ)*((k:ℝ)+1)*w i k) *
        (∏ j ∈ Finset.univ.erase i, ∑' k : ℕ, w j k) ≤
      (L i)^2/8 * ∏ j, boundaryFactor 0 (L j) := by
    have hs (j : Fin n) : (∑' k : ℕ, w j k)=boundaryFactor 0 (L j) :=
      (boundaryLengthCoefficient_hasSum (L j)).tsum_eq
    simp_rw [hs]
    calc _ ≤ ((L i)^2/8*boundaryFactor 0 (L i))*
           ∏ j ∈ Finset.univ.erase i, boundaryFactor 0 (L j) :=
           mul_le_mul_of_nonneg_right (hm i).2
             (Finset.prod_nonneg (fun j _ => (zero_le_one.trans (one_le_boundaryFactor _ _))))
         _ = _ := by
           rw [←Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ i)]
           ring
  calc (n:ℝ) * ∑ i, _ ≤ (n:ℝ) * ∑ i, (L i)^2/8 * ∏ j, boundaryFactor 0 (L j) :=
         mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => ht i)) (Nat.cast_nonneg n)
       _ = _ := by rw [←Finset.sum_mul,←Finset.sum_div];ring

end WP
