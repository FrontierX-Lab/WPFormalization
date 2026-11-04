import WPFormalization.Weighted.ModelValidity
import WPFormalization.Weighted.CoefficientConvolution
import WPFormalization.Weighted.Clipping
/-! Exact normalization of the actual weighted linear sum into finite layers
with the genuine q-coefficients. Invalid negative mergers contribute zero; all
valid merger/contraction profiles are identified with their original signed
validModel factors. The weighted-bound statements themselves are not assumed. -/
noncomputable section
namespace WP
def mergerProfile (pivot : ℕ) (d : List ℕ) (l j : ℕ) : List ℕ :=
  (pivot+d[j]!+l-1) :: d.eraseIdx j
def contractionProfile (pivot : ℕ) (d : List ℕ) (l u : ℕ) : List ℕ :=
  u :: (pivot+l-2-u) :: d
def stateWeightRatio (c : ℝ) (parent child : List ℕ) : ℝ := clippedWeight c child/clippedWeight c parent
-- Deliberately named differently from the scalar clippedPhi ratio.
def mergerModelFactor (c Y : ℝ) (g pivot : ℕ) (d : List ℕ) (l j : ℕ) : ℝ :=
  let ds := ((pivot : ℤ)+(d[j]! : ℤ)+l-1) :: (d.eraseIdx j).map Int.ofNat
  theta Y l*(validModel g ds Y/model g (pivot :: d) Y*signedWeight c ds/clippedWeight c (pivot :: d))
def contractionModelFactor (c Y : ℝ) (g pivot : ℕ) (d : List ℕ) (l u : ℕ) : ℝ :=
  let ds := (u : ℤ) :: ((pivot : ℤ)+l-2-u) :: d.map Int.ofNat
  theta Y l*(validModel (g-1) ds Y/model g (pivot :: d) Y*signedWeight c ds/clippedWeight c (pivot :: d))
lemma mergerModelFactor_eq (c Y : ℝ) (g pivot : ℕ) (d : List ℕ) (l j : ℕ)
    (hg : 2 ≤ g) (hd : (pivot :: d).sum ≤ dimension g (d.length+1))
    (hl : l ≤ deficit g (pivot :: d)) (hj : j < d.length) (hY : Y ∈ Set.Icc 0 y₀) :
    mergerModelFactor c Y g pivot d l j =
      if 1 ≤ pivot+d[j]!+l then
        linearQ Y (complexity g (d.length+1)) (deficit g (pivot :: d)) l /
          (3*((complexity g (d.length+1) : ℝ)-1))*
            stateWeightRatio c (pivot :: d) (mergerProfile pivot d l j)
      else 0 := by
  let ds := ((pivot : ℤ)+(d[j]! : ℤ)+l-1) :: (d.eraseIdx j).map Int.ofNat
  change theta Y l*(validModel g ds Y/model g (pivot :: d) Y*signedWeight c ds/clippedWeight c (pivot :: d)) = _
  by_cases hnode : 1 ≤ pivot+d[j]!+l
  · rw [if_pos hnode]
    have he : ds.map Int.toNat = mergerProfile pivot d l j := by
      dsimp only [ds,mergerProfile]
      simp only [List.map_cons,List.map_map,Function.comp_def,Int.ofNat_eq_natCast,Int.toNat_natCast,List.map_id_fun',id_eq]
      congr 1
      omega
    calc
      _ = (theta Y l*validModel g ds Y/model g (pivot :: d) Y)*
          (signedWeight c ds/clippedWeight c (pivot :: d)) := by ring
      _ = _ := by
        rw [validModel_merger_ratio g pivot d l j Y hg hd hl hj (by omega) hY]
        unfold signedWeight stateWeightRatio
        rw [he]
  · rw [if_neg hnode]
    have hp0 : pivot=0 := by omega
    have hj0 : d[j]! = 0 := by omega
    have hl0 : l=0 := by omega
    have hz : validModel g ds Y=0 := by
      apply validModel_zero_negative
      exact ⟨-1,by simp [ds,hp0,hj0,hl0],by norm_num⟩
    rw [hz]
    ring
lemma contractionModelFactor_eq (c Y : ℝ) (g pivot : ℕ) (d : List ℕ) (l u : ℕ)
    (hg : 2 ≤ g) (hd : (pivot :: d).sum ≤ dimension g (d.length+1))
    (hl : l ≤ deficit g (pivot :: d)) (hu : u ∈ Finset.range (pivot+l-1))
    (hY : Y ∈ Set.Icc 0 y₀) :
    contractionModelFactor c Y g pivot d l u =
      4*linearQ Y (complexity g (d.length+1)) (deficit g (pivot :: d)) l /
        (3*((complexity g (d.length+1) : ℝ)-1))*
          stateWeightRatio c (pivot :: d) (contractionProfile pivot d l u) := by
  let ds := (u : ℤ) :: ((pivot : ℤ)+l-2-u) :: d.map Int.ofNat
  have hu' := Finset.mem_range.mp hu
  have he : ds.map Int.toNat = contractionProfile pivot d l u := by
    dsimp only [ds,contractionProfile]
    simp only [List.map_cons,List.map_map,Function.comp_def,Int.ofNat_eq_natCast,Int.toNat_natCast,List.map_id_fun',id_eq]
    congr 1
    congr 1
    omega
  change theta Y l*(validModel (g-1) ds Y/model g (pivot :: d) Y*signedWeight c ds/clippedWeight c (pivot :: d)) = _
  calc
    _ = (theta Y l*validModel (g-1) ds Y/model g (pivot :: d) Y)*
        (signedWeight c ds/clippedWeight c (pivot :: d)) := by ring
    _ = _ := by
      rw [validModel_contraction_ratio g pivot d l u Y hg hd hl hu hY]
      unfold signedWeight stateWeightRatio
      rw [he]
def weightedLinearLayer (c : ℝ) (pivot : ℕ) (d : List ℕ) (l : ℕ) : ℝ :=
  (∑ j ∈ Finset.range d.length, (2*(d[j]! : ℝ)+1)*
    (if 1 ≤ pivot+d[j]!+l then stateWeightRatio c (pivot :: d) (mergerProfile pivot d l j) else 0)) +
  2*∑ u ∈ Finset.range (pivot+l-1), stateWeightRatio c (pivot :: d) (contractionProfile pivot d l u)
lemma weightedLinear_eq_layers (c Y : ℝ) (g pivot : ℕ) (d : List ℕ)
    (hg : 2 ≤ g) (hd : (pivot :: d).sum ≤ dimension g (d.length+1)) (hY : Y ∈ Set.Icc 0 y₀) :
    weightedLinear c Y g pivot d =
      ∑ l ∈ Finset.range (deficit g (pivot :: d)+1),
        (linearQ Y (complexity g (d.length+1)) (deficit g (pivot :: d)) l /
          (3*((complexity g (d.length+1) : ℝ)-1)))*weightedLinearLayer c pivot d l := by
  have hm :
      (∑ j ∈ Finset.range d.length, (2*(d[j]! : ℝ)+1)*
        ∑ l ∈ Finset.range (deficit g (pivot :: d)+1), mergerModelFactor c Y g pivot d l j) =
      ∑ l ∈ Finset.range (deficit g (pivot :: d)+1),
        (linearQ Y (complexity g (d.length+1)) (deficit g (pivot :: d)) l /
          (3*((complexity g (d.length+1) : ℝ)-1)))*
          ∑ j ∈ Finset.range d.length, (2*(d[j]! : ℝ)+1)*
            (if 1 ≤ pivot+d[j]!+l then stateWeightRatio c (pivot :: d) (mergerProfile pivot d l j) else 0) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro j hj
    rw [mergerModelFactor_eq c Y g pivot d l j hg hd
      (by have := Finset.mem_range.mp hl; omega) (Finset.mem_range.mp hj) hY]
    split_ifs <;> ring
  have hn :
      (1/2 : ℝ)*(∑ l ∈ Finset.range (deficit g (pivot :: d)+1),
        ∑ u ∈ Finset.range (pivot+l-1), contractionModelFactor c Y g pivot d l u) =
      ∑ l ∈ Finset.range (deficit g (pivot :: d)+1),
        (linearQ Y (complexity g (d.length+1)) (deficit g (pivot :: d)) l /
          (3*((complexity g (d.length+1) : ℝ)-1)))*
          (2*∑ u ∈ Finset.range (pivot+l-1), stateWeightRatio c (pivot :: d) (contractionProfile pivot d l u)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro u hu
    rw [contractionModelFactor_eq c Y g pivot d l u hg hd
      (by have := Finset.mem_range.mp hl; omega) hu hY]
    ring
  unfold weightedLinear
  dsimp only
  rw [if_neg (by omega : g ≠ 0)]
  have he :
      (∑ j ∈ Finset.range d.length, (2*(d[j]! : ℝ)+1)*
        ∑ l ∈ Finset.range (deficit g (pivot :: d)+1), mergerModelFactor c Y g pivot d l j) +
      (1/2 : ℝ)*(∑ l ∈ Finset.range (deficit g (pivot :: d)+1),
        ∑ u ∈ Finset.range (pivot+l-1), contractionModelFactor c Y g pivot d l u) =
      ∑ l ∈ Finset.range (deficit g (pivot :: d)+1),
        (linearQ Y (complexity g (d.length+1)) (deficit g (pivot :: d)) l /
          (3*((complexity g (d.length+1) : ℝ)-1)))*weightedLinearLayer c pivot d l := by
    rw [hm,hn,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    unfold weightedLinearLayer
    ring
  convert he using 1
  unfold mergerModelFactor contractionModelFactor
  simp only [Finset.mul_sum]
end WP
