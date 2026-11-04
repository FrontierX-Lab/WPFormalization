import WPFormalization.Comparison.ZeroPotential
import WPFormalization.Comparison.ZeroMass
/-! The genuine finite linear kernel used by the lower comparison.
Its mass is exactly one at a positive pivot and the proved all-zero mass
at an all-zero pivot. The actual profile drift gives the global exponential
zero-potential budget. Both mass and potential are identified with the original
nested merger/handle sums, for the typed finite-state application. -/
noncomputable section
namespace WP
open Set

def linearLowerCoef (Y:ℝ)(g pivot:ℕ)(d:List ℕ)(l:ℕ):ℝ:=
  linearQ Y (complexity g (d.length+1)) (deficit g (pivot::d)) l/(3*((complexity g (d.length+1):ℝ)-1))
def linearRawMass (Y:ℝ)(g pivot:ℕ)(d:List ℕ):ℝ:=
  ∑l∈Finset.range (deficit g (pivot::d)+1),linearLowerCoef Y g pivot d l*zeroCountLayer pivot d l
def linearRawPotential (Y:ℝ)(g pivot:ℕ)(d:List ℕ):ℝ:=
  (2:ℝ)^(zeros (pivot::d))*
    ∑l∈Finset.range (deficit g (pivot::d)+1),linearLowerCoef Y g pivot d l*zeroPotentialLayer pivot d l
lemma linearLowerCoef_nonneg (Y:ℝ)(hY:Y∈Icc 0 y₀)(g pivot:ℕ)(d:List ℕ)(hg:2 ≤ g)(l:ℕ):
    0 ≤ linearLowerCoef Y g pivot d l := by
  have hh:2 ≤ complexity g (d.length+1):=by unfold complexity;omega
  have hhR:(2:ℝ) ≤ complexity g (d.length+1):=by exact_mod_cast hh
  unfold linearLowerCoef
  exact div_nonneg (linearQ_nonneg Y hY _ _ _ hh) (by linarith)
lemma linearRawMass_nonneg (Y:ℝ)(hY:Y∈Icc 0 y₀)(g pivot:ℕ)(d:List ℕ)(hg:2 ≤ g):
    0 ≤ linearRawMass Y g pivot d := by
  apply Finset.sum_nonneg
  intro l hl
  exact mul_nonneg (linearLowerCoef_nonneg Y hY g pivot d hg l) (zeroCountLayer_nonneg _ _ _)
lemma linearRawMass_positive_pivot (Y:ℝ)(hY:Y∈Icc 0 y₀)(g pivot:ℕ)(d:List ℕ)(hg:2 ≤ g)(hp:1 ≤ pivot)
    (hd:(pivot::d).sum ≤ dimension g (d.length+1)):linearRawMass Y g pivot d=1 := by
  unfold linearRawMass linearLowerCoef
  simp_rw[zeroCountLayer_positive pivot d _ hp]
  exact linear_count_mass Y hY g pivot d hg hp hd
lemma zeroEntries_sum (d:List ℕ)(hd:∀k∈d,k=0):d.sum=0 := by
  induction d with
  | nil => rfl
  | cons a d ih =>
    have ha:=hd a (by simp)
    have ht:=ih (fun k hk=>hd k (by simp[hk]))
    simp[ha,ht]
lemma zeros_all_zero_length (d:List ℕ)(hd:∀k∈d,k=0):zeros d=d.length := by
  have hr:d=List.replicate d.length 0:=List.eq_replicate_iff.mpr ⟨rfl,hd⟩
  rw[hr]
  simp[zeros]
lemma linearRawMass_zero_pivot (Y:ℝ)(g:ℕ)(d:List ℕ)(hd:∀k∈d,k=0):
    linearRawMass Y g 0 d=zeroLinearMass Y g (d.length+1) := by
  have hs:=zeroEntries_sum d hd
  have hm:deficit g (0::d)=dimension g (d.length+1):=by simp[deficit,hs]
  unfold linearRawMass linearLowerCoef zeroLinearMass
  rw[hm]
  dsimp only
  apply Finset.sum_congr rfl
  intro l hl
  rw[zeroCountLayer_zero d hd l]
  push_cast
  ring
lemma linearRawMass_exp_lower (Y:ℝ)(hY:Y∈Icc 0 y₀)(g pivot:ℕ)(d:List ℕ)(hg:2 ≤ g)
    (hd:(pivot::d).sum ≤ dimension g (d.length+1))(hp:1 ≤ pivot ∨(pivot=0 ∧∀k∈d,k=0)):
    Real.exp (-(zeros (pivot::d):ℝ)/(complexity g (d.length+1):ℝ)) ≤ linearRawMass Y g pivot d := by
  rcases hp with hp|⟨rfl,hzero⟩
  · rw[linearRawMass_positive_pivot Y hY g pivot d hg hp hd]
    apply Real.exp_le_one_iff.mpr
    have hz:0 ≤ (zeros (pivot::d):ℝ)/(complexity g (d.length+1):ℝ):=by positivity
    simpa only[neg_div] using neg_nonpos.mpr hz
  · rw[linearRawMass_zero_pivot Y g d hzero]
    have hz:zeros (0::d)=d.length+1:=by simp[zeros_cons_eq,zeros_all_zero_length d hzero]
    rw[hz]
    exact zeroMass_exp_lower Y hY g (d.length+1) hg (by omega)
lemma linearRawPotential_bound (Y:ℝ)(hY:Y∈Icc 0 y₀)(g pivot:ℕ)(d:List ℕ)(hg:2 ≤ g)
    (hp:1 ≤ pivot ∨(pivot=0 ∧∀k∈d,k=0)):
    linearRawPotential Y g pivot d ≤ linearRawMass Y g pivot d*((2:ℝ)^(zeros (pivot::d))+(2:ℝ)^26) :=
  finite_zero_power_budget _ _ (fun l _=>linearLowerCoef_nonneg Y hY g pivot d hg l) pivot d hp
lemma zeroPotentialLayer_raw_identity (pivot:ℕ)(d:List ℕ)(l:ℕ):
    (2:ℝ)^(zeros (pivot::d))*zeroPotentialLayer pivot d l=
      (∑j∈Finset.range d.length,(2*(d[j]!:ℝ)+1)*(if 1 ≤ pivot+d[j]!+l then
        (2:ℝ)^(zeros (mergerProfile pivot d l j)) else 0))+
      2*∑u∈Finset.range (pivot+l-1),(2:ℝ)^(zeros (contractionProfile pivot d l u)) := by
  have hn:(2:ℝ)^(zeros (pivot::d))≠0:=by positivity
  unfold zeroPotentialLayer zeroPowerRatio
  rw[mul_add,Finset.mul_sum]
  apply congrArg₂ (fun a b:ℝ=>a+b)
  · apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> field_simp <;> ring
  · calc _=2*((2:ℝ)^(zeros (pivot::d))*(∑u∈Finset.range (pivot+l-1),
          (2:ℝ)^(zeros (contractionProfile pivot d l u))/(2:ℝ)^(zeros (pivot::d)))):=by ring
         _=2*(∑u∈Finset.range (pivot+l-1),(2:ℝ)^(zeros (contractionProfile pivot d l u))):=by
           congr 1
           rw[Finset.mul_sum]
           apply Finset.sum_congr rfl
           intro u hu
           field_simp
lemma linearRawMass_eq_nested (Y:ℝ)(g pivot:ℕ)(d:List ℕ):
    linearRawMass Y g pivot d=∑l∈Finset.range (deficit g (pivot::d)+1),linearLowerCoef Y g pivot d l*
      ((∑j∈Finset.range d.length,(2*(d[j]!:ℝ)+1)*(if 1 ≤ pivot+d[j]!+l then (1:ℝ) else 0))+
      2*∑u∈Finset.range (pivot+l-1),(1:ℝ)) := by
  unfold linearRawMass zeroCountLayer
  simp
lemma linearRawPotential_eq_nested (Y:ℝ)(g pivot:ℕ)(d:List ℕ):
    linearRawPotential Y g pivot d=∑l∈Finset.range (deficit g (pivot::d)+1),linearLowerCoef Y g pivot d l*
      ((∑j∈Finset.range d.length,(2*(d[j]!:ℝ)+1)*(if 1 ≤ pivot+d[j]!+l then
        (2:ℝ)^(zeros (mergerProfile pivot d l j)) else 0))+
      2*∑u∈Finset.range (pivot+l-1),(2:ℝ)^(zeros (contractionProfile pivot d l u))) := by
  unfold linearRawPotential
  rw[Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  calc _=linearLowerCoef Y g pivot d l*((2:ℝ)^(zeros (pivot::d))*zeroPotentialLayer pivot d l):=by ring
       _=_:=by rw[zeroPotentialLayer_raw_identity]
end WP
