import WPFormalization.HigherOrder.SecondProfileGrowth
import WPFormalization.HigherOrder.SecondSeparatingCoefficients

/-! The actual order weights Sj of Appendix C.5(a,d). All three child tuples, loss-shifted scalar factors, dilaton/KdV/descent children and the linear finite counts satisfy the displayed elementary weight inequalities. -/
noncomputable section
namespace WP.HigherOrder

def profileOrderWeight (M:ℝ) (j:ℕ) (d:List ℕ) : ℝ := (d.sum:ℝ)+d.length+M*j
def scalarOrderWeight (M:ℝ) (j p:ℕ) : ℝ := (p:ℝ)+M*j

lemma profileOrderWeight_base_le (M:ℝ) (hM:0≤M) (j:ℕ) (d:List ℕ) :
    (d.sum:ℝ)+d.length≤ profileOrderWeight M j d := by
  unfold profileOrderWeight
  have hMj : 0≤M*(j:ℝ):=by positivity
  linarith

lemma scalar_order_weight_shift (M:ℝ) (hM:1≤M) (i j p q r:ℕ)
    (hq:q≤p+r) (hij:i+r≤j) : scalarOrderWeight M i q≤ scalarOrderWeight M j p := by
  have hqR : (q:ℝ)≤(p:ℝ)+r:=by exact_mod_cast hq
  have hiR : (i:ℝ)+r≤j:=by exact_mod_cast hij
  have hMi:=mul_le_mul_of_nonneg_left hiR (show 0≤M by linarith)
  have hMr:=mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg r : (0:ℝ)≤r)
  unfold scalarOrderWeight
  nlinarith

lemma merger_order_weight (M:ℝ) (hM:0≤M) (i j t l k:ℕ) (d:List ℕ)
    (hij:i≤j) (hk:k<d.length) (hn:1≤t+d[k]!+l) :
    profileOrderWeight M i (mergerProfile t d l k)≤ profileOrderWeight M j (t::d)+l := by
  obtain ⟨hs,hl⟩:=sum_eraseIdx_component d k hk
  have hsum : (mergerProfile t d l k).sum+1=(t::d).sum+l := by
    simp only [mergerProfile,List.sum_cons]
    omega
  have hlen : (mergerProfile t d l k).length+1=(t::d).length := by
    simp only [mergerProfile,List.length_cons]
    omega
  have hsumR : ((mergerProfile t d l k).sum:ℝ)+1=((t::d).sum:ℝ)+l:=by exact_mod_cast hsum
  have hlenR : ((mergerProfile t d l k).length:ℝ)+1=((t::d).length:ℝ):=by exact_mod_cast hlen
  have horder:=mul_le_mul_of_nonneg_left (show (i:ℝ)≤j by exact_mod_cast hij) hM
  unfold profileOrderWeight
  linarith

lemma handle_order_weight (M:ℝ) (hM:0≤M) (i j t l u:ℕ) (d:List ℕ)
    (hij:i≤j) (hu:u<t+l-1) :
    profileOrderWeight M i (contractionProfile t d l u)≤ profileOrderWeight M j (t::d)+l := by
  have hsum : (contractionProfile t d l u).sum+2=(t::d).sum+l := by
    simp only [contractionProfile,List.sum_cons]
    omega
  have hlen : (contractionProfile t d l u).length=(t::d).length+1 := by simp [contractionProfile]
  have hsumR : ((contractionProfile t d l u).sum:ℝ)+2=((t::d).sum:ℝ)+l:=by exact_mod_cast hsum
  have hlenR : ((contractionProfile t d l u).length:ℝ)=((t::d).length:ℝ)+1:=by exact_mod_cast hlen
  have horder:=mul_le_mul_of_nonneg_left (show (i:ℝ)≤j by exact_mod_cast hij) hM
  unfold profileOrderWeight
  linarith

lemma selectedNat_toNat (d:List ℕ) (I:Finset ℕ) :
    (selected (d.map Int.ofNat) I).map Int.toNat=selectedNat d I := by
  rw [←selectedNat_int_map,List.map_map]
  simp only [Function.comp_def,Int.ofNat_eq_natCast,Int.toNat_natCast,List.map_id']

lemma selectedNat_sum_le (d:List ℕ) (I:Finset ℕ) : (selectedNat d I).sum≤d.sum := by
  rw [←selectedNat_toNat]
  exact selected_nat_toNat_sum_le d I

lemma selectedNat_length_le (d:List ℕ) (I:Finset ℕ) : (selectedNat d I).length≤d.length := by
  have hs:=selected_nat_toNat_sublist d I
  rw [selectedNat_toNat] at hs
  exact hs.length_le

lemma separating_order_weight (M:ℝ) (hM:0≤M) (i j t l u:ℕ) (d:List ℕ) (I:Finset ℕ)
    (hij:i≤j) (hu:u<t+l-1) :
    profileOrderWeight M i ((t+l-2-u)::selectedNat d I)≤ profileOrderWeight M j (t::d)+l := by
  have hs:=(selectedNat_sum_le d I)
  have hl:=(selectedNat_length_le d I)
  have hsum : (((t+l-2-u)::selectedNat d I).sum)+2≤(t::d).sum+l := by
    simp only [List.sum_cons]
    omega
  have hlen : (((t+l-2-u)::selectedNat d I).length)≤(t::d).length := by simp only [List.length_cons];omega
  have hsumR : ((((t+l-2-u)::selectedNat d I).sum):ℝ)+2≤((t::d).sum:ℝ)+l:=by exact_mod_cast hsum
  have hlenR : ((((t+l-2-u)::selectedNat d I).length):ℝ)≤((t::d).length:ℝ):=by exact_mod_cast hlen
  have horder:=mul_le_mul_of_nonneg_left (show (i:ℝ)≤j by exact_mod_cast hij) hM
  unfold profileOrderWeight
  linarith

lemma dilaton_order_weight (M:ℝ) (hM:0≤M) (i j p d:ℕ) (hij:i≤j) :
    profileOrderWeight M i (d::List.replicate p 0)≤ scalarOrderWeight M j p+d+1 := by
  have horder:=mul_le_mul_of_nonneg_left (show (i:ℝ)≤j by exact_mod_cast hij) hM
  simp only [profileOrderWeight,scalarOrderWeight,List.sum_cons,List.sum_replicate,
    nsmul_zero,add_zero,List.length_cons,List.length_replicate,Nat.cast_add,Nat.cast_one]
  linarith

lemma merger_count_le_order_weight (M:ℝ) (hM:0≤M) (j t:ℕ) (d:List ℕ) :
    (∑k∈Finset.range d.length,(2*(d[k]!:ℝ)+1))≤2*profileOrderWeight M j (t::d) := by
  have he : (∑k∈Finset.range d.length,(2*(d[k]!:ℝ)+1))=2*(d.sum:ℝ)+d.length := by
    rw [Finset.sum_add_distrib,←Finset.mul_sum]
    have hs:=sum_range_getElem d (fun k:ℕ=>(k:ℝ))
    have hc : (d.map (fun k:ℕ=>(k:ℝ))).sum=(d.sum:ℝ):=(map_list_sum (Nat.castAddMonoidHom ℝ) d).symm
    rw [hc] at hs
    rw [hs]
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]
  rw [he]
  have hMj : 0≤M*(j:ℝ):=by positivity
  simp only [profileOrderWeight,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
  linarith [show (0:ℝ)≤t from Nat.cast_nonneg t,show (0:ℝ)≤d.length from Nat.cast_nonneg _]
lemma pair_count_le_order_weight (M:ℝ) (hM:0≤M) (j t l:ℕ) (d:List ℕ) :
    ((t+l-1:ℕ):ℝ)≤ profileOrderWeight M j (t::d)+l := by
  have hn : t+l-1≤(t::d).sum+l := by simp only [List.sum_cons];omega
  have hnr : ((t+l-1:ℕ):ℝ)≤((t::d).sum:ℝ)+l := by exact_mod_cast hn
  have hb:=profileOrderWeight_base_le M hM j (t::d)
  linarith [show (0:ℝ)≤(t::d).length from Nat.cast_nonneg _]

lemma canonical_path_count_le_order_weight (M:ℝ) (hM:0≤M) (j:ℕ) (d:List ℕ) :
    (d.sum:ℝ)≤ profileOrderWeight M j d := by
  have hb:=profileOrderWeight_base_le M hM j d
  linarith [show (0:ℝ)≤d.length from Nat.cast_nonneg _]

lemma kdv_order_weight (M:ℝ) (hM:0≤M) (i j p:ℕ) (hp:1≤p) (hij:i≤j) :
    profileOrderWeight M i (1::List.replicate (p-1) 0)≤ scalarOrderWeight M j p+1 := by
  have horder:=mul_le_mul_of_nonneg_left (show (i:ℝ)≤j by exact_mod_cast hij) hM
  simp only [profileOrderWeight,scalarOrderWeight,List.sum_cons,List.sum_replicate,
    nsmul_zero,add_zero,List.length_cons,List.length_replicate,Nat.cast_add,Nat.cast_one,
    Nat.cast_sub hp]
  linarith

lemma descent_order_weight (M:ℝ) (hM:0≤M) (i j p:ℕ) (hij:i≤j) :
    scalarOrderWeight M i (p+2)≤ scalarOrderWeight M j p+2 := by
  have horder:=mul_le_mul_of_nonneg_left (show (i:ℝ)≤j by exact_mod_cast hij) hM
  simp only [scalarOrderWeight,Nat.cast_add,Nat.cast_ofNat]
  linarith
end WP.HigherOrder
