import WPFormalization.Marked.ExternalStringProfile
import WPFormalization.Volumes.BoundaryPolynomial
noncomputable section
namespace WP.BoundaryConvolution
lemma boundaryProfileMoment_le_coordinate_sum {p : ℕ} (hp : 1 ≤ p) (b : Fin p → ℕ) :
    boundaryProfileMoment b ≤ (p:ℝ) * ∑ i, ((b i:ℝ)*((b i:ℝ)+1)) := by
  have hq := sq_sum_le_card_mul_sum_sq (s:=Finset.univ) (f:=fun i : Fin p => (b i:ℝ))
  simp only [Finset.card_univ,Fintype.card_fin] at hq
  have hpR : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hs : 0 ≤ ∑ i : Fin p, (b i:ℝ) := Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)
  have hl : (∑ i : Fin p, (b i:ℝ)) ≤ (p:ℝ)*(∑ i : Fin p, (b i:ℝ)) := by nlinarith
  have he : (∑ i : Fin p, ((b i:ℝ)*((b i:ℝ)+1))) =
      (∑ i : Fin p, (b i:ℝ)^2)+(∑ i : Fin p, (b i:ℝ)) := by
    simp only [mul_add,mul_one,pow_two,Finset.sum_add_distrib]
  rw [he]
  unfold boundaryProfileMoment
  push_cast
  nlinarith

lemma boundary_coordinate_product {p : ℕ} (w : Fin p → ℕ → ℝ)
    (m : ℕ → ℝ) (b : Fin p → ℕ) (i : Fin p) :
    m (b i) * (∏ j, w j (b j)) =
      ∏ j, (if j=i then m (b j)*w j (b j) else w j (b j)) := by
  rw [←Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ i),
    ←Finset.prod_erase_mul Finset.univ (fun j => if j=i then m (b j)*w j (b j) else w j (b j)) (Finset.mem_univ i)]
  simp only [ite_true]
  have he : (∏ j ∈ Finset.univ.erase i, if j=i then m (b j)*w j (b j) else w j (b j)) =
      ∏ j ∈ Finset.univ.erase i, w j (b j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [if_neg (Finset.mem_erase.mp hj).1]
  rw [he]
  ring

lemma boundary_coordinate_product_summable {p : ℕ} (w : Fin p → ℕ → ℝ)
    (hw : ∀ i, Summable (w i)) (hwn : ∀ i k, 0 ≤ w i k)
    (i : Fin p) (hm : Summable (fun k : ℕ => (k:ℝ)*((k:ℝ)+1)*w i k)) :
    Summable (fun b : Fin p → ℕ => ((b i:ℝ)*((b i:ℝ)+1)) * ∏ j, w j (b j)) := by
  have hs : ∀ j : Fin p, Summable (fun k : ℕ => if j=i then (k:ℝ)*((k:ℝ)+1)*w j k else w j k) := by
    intro j
    by_cases he : j=i
    · subst j;simpa using hm
    · simpa [he] using hw j
  have hn : ∀ j : Fin p, ∀ k : ℕ,
      0 ≤ (if j=i then (k:ℝ)*((k:ℝ)+1)*w j k else w j k) := by
    intro j k
    split_ifs
    · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)) (hwn j k)
    · exact hwn j k
  convert summable_fin_tuple_product p _ hs hn using 1
  ext b
  exact boundary_coordinate_product w (fun k => (k:ℝ)*((k:ℝ)+1)) b i

lemma boundary_coordinate_product_tsum {p : ℕ} (w : Fin p → ℕ → ℝ)
    (hw : ∀ i, Summable (w i)) (hwn : ∀ i k, 0 ≤ w i k)
    (i : Fin p) (hm : Summable (fun k : ℕ => (k:ℝ)*((k:ℝ)+1)*w i k)) :
    (∑' b : Fin p → ℕ, ((b i:ℝ)*((b i:ℝ)+1)) * ∏ j, w j (b j)) =
      (∑' k : ℕ, (k:ℝ)*((k:ℝ)+1)*w i k) *
        ∏ j ∈ Finset.univ.erase i, ∑' k : ℕ, w j k := by
  have hs : ∀ j : Fin p, Summable (fun k : ℕ => if j=i then (k:ℝ)*((k:ℝ)+1)*w j k else w j k) := by
    intro j
    by_cases he : j=i
    · subst j;simpa using hm
    · simpa [he] using hw j
  have hn : ∀ j : Fin p, ∀ k : ℕ,
      0 ≤ (if j=i then (k:ℝ)*((k:ℝ)+1)*w j k else w j k) := by
    intro j k
    split_ifs
    · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)) (hwn j k)
    · exact hwn j k
  have he := tsum_fin_tuple_product p _ hs hn
  simp_rw [←boundary_coordinate_product w (fun k => (k:ℝ)*((k:ℝ)+1))] at he
  rw [he,←Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ i)]
  simp only [ite_true]
  have hep : (∏ j ∈ Finset.univ.erase i,
      ∑' k : ℕ, if j=i then (k:ℝ)*((k:ℝ)+1)*w j k else w j k) =
      ∏ j ∈ Finset.univ.erase i, ∑' k : ℕ, w j k := by
    apply Finset.prod_congr rfl
    intro j hj
    simp only [if_neg (Finset.mem_erase.mp hj).1]
  rw [hep]
  ring
end WP.BoundaryConvolution
namespace WP.BoundaryConvolution
lemma boundary_tuple_moment_summable {p : ℕ} (hp : 1 ≤ p) (w : Fin p → ℕ → ℝ)
    (hw : ∀ i, Summable (w i)) (hwn : ∀ i k, 0 ≤ w i k)
    (hm : ∀ i, Summable (fun k : ℕ => (k:ℝ)*((k:ℝ)+1)*w i k)) :
    Summable (fun b : Fin p → ℕ => boundaryProfileMoment b * ∏ j, w j (b j)) := by
  have hmajor : Summable (fun b : Fin p → ℕ => (p:ℝ) *
      ∑ i : Fin p, ((b i:ℝ)*((b i:ℝ)+1)) * ∏ j, w j (b j)) := by
    exact (hasSum_sum (s:=Finset.univ) (fun i _ => (boundary_coordinate_product_summable w hw hwn i (hm i)).hasSum)).summable.mul_left _
  have hn : ∀ b : Fin p → ℕ, 0 ≤ boundaryProfileMoment b * ∏ j, w j (b j) := by
    intro b
    exact mul_nonneg (by unfold boundaryProfileMoment;positivity) (Finset.prod_nonneg (s:=Finset.univ) (fun j _ => hwn j (b j)))
  have he : ∀ b : Fin p → ℕ, boundaryProfileMoment b * (∏ j, w j (b j)) ≤
      (p:ℝ) * ∑ i : Fin p, ((b i:ℝ)*((b i:ℝ)+1)) * ∏ j, w j (b j) := by
    intro b
    have he := mul_le_mul_of_nonneg_right (boundaryProfileMoment_le_coordinate_sum hp b)
      (Finset.prod_nonneg (s:=Finset.univ) (fun j _ => hwn j (b j)))
    simpa only [Finset.sum_mul,mul_assoc] using he
  exact Summable.of_nonneg_of_le hn he hmajor

lemma boundary_tuple_moment_tsum_le {p : ℕ} (hp : 1 ≤ p) (w : Fin p → ℕ → ℝ)
    (hw : ∀ i, Summable (w i)) (hwn : ∀ i k, 0 ≤ w i k)
    (hm : ∀ i, Summable (fun k : ℕ => (k:ℝ)*((k:ℝ)+1)*w i k)) :
    (∑' b : Fin p → ℕ, boundaryProfileMoment b * ∏ j, w j (b j)) ≤
      (p:ℝ) * ∑ i : Fin p, (∑' k : ℕ, (k:ℝ)*((k:ℝ)+1)*w i k) *
        ∏ j ∈ Finset.univ.erase i, ∑' k : ℕ, w j k := by
  have hmajor : Summable (fun b : Fin p → ℕ => (p:ℝ) *
      ∑ i : Fin p, ((b i:ℝ)*((b i:ℝ)+1)) * ∏ j, w j (b j)) := by
    exact (hasSum_sum (s:=Finset.univ) (fun i _ => (boundary_coordinate_product_summable w hw hwn i (hm i)).hasSum)).summable.mul_left _
  have he : ∀ b : Fin p → ℕ, boundaryProfileMoment b * (∏ j, w j (b j)) ≤
      (p:ℝ) * ∑ i : Fin p, ((b i:ℝ)*((b i:ℝ)+1)) * ∏ j, w j (b j) := by
    intro b
    have he := mul_le_mul_of_nonneg_right (boundaryProfileMoment_le_coordinate_sum hp b)
      (Finset.prod_nonneg (s:=Finset.univ) (fun j _ => hwn j (b j)))
    simpa only [Finset.sum_mul,mul_assoc] using he
  have hsumHS := hasSum_sum (s:=Finset.univ) (fun i _ =>
    (boundary_coordinate_product_summable w hw hwn i (hm i)).hasSum)
  have hsum := hasSum_le he (boundary_tuple_moment_summable hp w hw hwn hm).hasSum
    (hsumHS.mul_left (p:ℝ))
  simpa only [boundary_coordinate_product_tsum w hw hwn _ (hm _)] using hsum
end WP.BoundaryConvolution
namespace WP.BoundaryConvolution
lemma boundary_tuple_moment_uniform_bound {p : ℕ} (hp : 1 ≤ p) (w : Fin p → ℕ → ℝ)
    (hw : ∀ i, Summable (w i)) (hwn : ∀ i k, 0 ≤ w i k)
    (hm : ∀ i, Summable (fun k : ℕ => (k:ℝ)*((k:ℝ)+1)*w i k))
    (B M : ℝ) (hB : 1 ≤ B) (hM : 0 ≤ M)
    (hwB : ∀ i, (∑' k : ℕ, w i k) ≤ B)
    (hmM : ∀ i, (∑' k : ℕ, (k:ℝ)*((k:ℝ)+1)*w i k) ≤ M) :
    (∑' b : Fin p → ℕ, boundaryProfileMoment b * ∏ j, w j (b j)) ≤
      (p:ℝ)^2 * M * B^p := by
  apply (boundary_tuple_moment_tsum_le hp w hw hwn hm).trans
  have hterm (i : Fin p) : (∑' k : ℕ, (k:ℝ)*((k:ℝ)+1)*w i k) *
      (∏ j ∈ Finset.univ.erase i, ∑' k : ℕ, w j k) ≤ M * B^p := by
    have hprod : (∏ j ∈ Finset.univ.erase i, ∑' k : ℕ, w j k) ≤ B^p := by
      calc
        _ ≤ ∏ j ∈ Finset.univ.erase i, B :=
          Finset.prod_le_prod₀ (fun j _ => tsum_nonneg (hwn j)) (fun j _ => hwB j)
        _ = B ^ (Finset.univ.erase i).card := by simp
        _ ≤ B^p := pow_le_pow_right₀ hB (by
          simpa only [Finset.card_univ,Fintype.card_fin] using Finset.card_le_card (Finset.erase_subset (s:=Finset.univ) i))
    exact mul_le_mul (hmM i) hprod (Finset.prod_nonneg (fun j _ => tsum_nonneg (hwn j))) hM
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hterm i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  have hpR : (0:ℝ) ≤ p := Nat.cast_nonneg p
  have he := mul_le_mul_of_nonneg_left hsum hpR
  nlinarith only [he]
end WP.BoundaryConvolution
namespace WP.BoundaryConvolution
lemma boundary_single_square_to_moment (w : ℕ → ℝ) (hwn : ∀ k, 0 ≤ w k)
    (hs : Summable (fun k : ℕ => ((k:ℝ)+1)^2*w k)) :
    Summable w ∧ (∑' k, w k) ≤ ∑' k : ℕ, ((k:ℝ)+1)^2*w k ∧
    Summable (fun k : ℕ => (k:ℝ)*((k:ℝ)+1)*w k) ∧
    (∑' k : ℕ, (k:ℝ)*((k:ℝ)+1)*w k) ≤ ∑' k : ℕ, ((k:ℝ)+1)^2*w k := by
  have hplain (k : ℕ) : w k ≤ ((k:ℝ)+1)^2*w k := by
    have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have hpoly : (1:ℝ) ≤ ((k:ℝ)+1)^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hpoly (hwn k)]
  have hmoment (k : ℕ) : (k:ℝ)*((k:ℝ)+1)*w k ≤ ((k:ℝ)+1)^2*w k := by
    have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have hpoly : (k:ℝ)*((k:ℝ)+1) ≤ ((k:ℝ)+1)^2 := by nlinarith
    exact mul_le_mul_of_nonneg_right hpoly (hwn k)
  have hmnon (k : ℕ) : 0 ≤ (k:ℝ)*((k:ℝ)+1)*w k := by
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)) (hwn k)
  have hp := Summable.of_nonneg_of_le hwn hplain hs
  have hm := Summable.of_nonneg_of_le hmnon hmoment hs
  exact ⟨hp,hp.tsum_le_tsum hplain hs,hm,hm.tsum_le_tsum hmoment hs⟩

lemma boundary_tuple_square_moment_bound {p : ℕ} (hp : 1 ≤ p) (w : Fin p → ℕ → ℝ)
    (hwn : ∀ i k, 0 ≤ w i k)
    (hs : ∀ i, Summable (fun k : ℕ => ((k:ℝ)+1)^2*w i k))
    (H : ℝ) (hH : 0 ≤ H) (hbound : ∀ i, (∑' k : ℕ, ((k:ℝ)+1)^2*w i k) ≤ H) :
    Summable (fun b : Fin p → ℕ => ∏ i, w i (b i)) ∧
    Summable (fun b : Fin p → ℕ => boundaryProfileMoment b * ∏ i, w i (b i)) ∧
    (∑' b : Fin p → ℕ, boundaryProfileMoment b * ∏ i, w i (b i)) ≤
      (p:ℝ)^2*H*(H+1)^p := by
  have he := fun i => boundary_single_square_to_moment (w i) (hwn i) (hs i)
  refine ⟨summable_fin_tuple_product p w (fun i => (he i).1) hwn,
    boundary_tuple_moment_summable hp w (fun i => (he i).1) hwn (fun i => (he i).2.2.1),?_⟩
  exact boundary_tuple_moment_uniform_bound hp w (fun i => (he i).1) hwn
    (fun i => (he i).2.2.1) (H+1) H (by linarith) hH
    (fun i => ((he i).2.1.trans (hbound i)).trans (by linarith))
    (fun i => (he i).2.2.2.trans (hbound i))
end WP.BoundaryConvolution
