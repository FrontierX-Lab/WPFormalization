import WPFormalization.Critical.ShortConfigurationRecordingIntersections
noncomputable section
set_option maxHeartbeats 0
namespace WP.Critical.ShortConfiguration
open Set Finset
open WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open scoped Classical

lemma finite_parameter_preimage {α β : Type*} (f : α→β) (s : Set α) (hf : Set.InjOn f s)
    (t : Finset β) : {a | a∈s ∧ f a∈t}.Finite ∧ Nat.card {a //a∈s ∧ f a∈t}≤t.card := by
  let code : {a //a∈s ∧ f a∈t}→{b //b∈t} := fun a=>⟨f a.val,a.property.2⟩
  have hi : Function.Injective code := by
    intro a b he
    apply Subtype.ext
    exact hf a.property.1 b.property.1 (congrArg Subtype.val he)
  haveI : Finite {a //a∈s ∧ f a∈t} := Finite.of_injective code hi
  refine ⟨@Set.toFinite α ({a |a∈s ∧ f a∈t} : Set α) (Finite.of_injective code hi),?_⟩
  simpa using Nat.card_le_card_of_injective code hi

variable (B : BorderedGeometry) (H : SegmentClassics B) {r : ℕ}
    (γ : Fin r→B.curves.Primitive) (hinj : Function.Injective γ)
    (hsimple : ∀i,SimpleTrace B (γ i)) (L : ℝ) (hL : 0<L)
    (hlength : ∀i,B.curves.length (γ i)≤L)

def pairVertices (i j : Fin r) : Finset B.surface.Point :=
  if hij : i=j then ∅ else
    (intersection_trace_finite_card_bound B H (γ i) (γ j) (hsimple i) (hsimple j)
      (fun he=>hij (hinj he)) L hL (hlength i) (hlength j)).1.toFinset

lemma pairVertices_mem (i j : Fin r) (p : B.surface.Point) :
    p∈pairVertices B H γ hinj hsimple L hL hlength i j ↔
      i≠j ∧ p∈B.curves.trace (γ i) ∧ p∈B.curves.trace (γ j) := by
  by_cases hij : i=j
  · simp [pairVertices,hij]
  · simp [pairVertices,hij]

lemma pairVertices_card_le (i j : Fin r) :
    (pairVertices B H γ hinj hsimple L hL hlength i j).card≤(Nat.floor (L/segmentScale L)+1)^2 := by
  by_cases hij : i=j
  · simp [pairVertices,hij]
  · have hh := intersection_trace_finite_card_bound B H (γ i) (γ j) (hsimple i) (hsimple j)
      (fun he=>hij (hinj he)) L hL (hlength i) (hlength j)
    have hc : Nat.card (B.curves.trace (γ i)∩B.curves.trace (γ j) : Set B.surface.Point)≤
        (Nat.floor (L/segmentScale L)+1)^2 := hh.2
    rw [Nat.card_coe_set_eq] at hc
    simpa only [pairVertices,dif_neg hij,←Set.ncard_eq_toFinset_card] using hc

def crossingVertices : Finset B.surface.Point :=
  univ.biUnion (fun i=>univ.biUnion (fun j=>pairVertices B H γ hinj hsimple L hL hlength i j))

lemma crossingVertices_mem (p : B.surface.Point) :
    p∈crossingVertices B H γ hinj hsimple L hL hlength ↔
      ∃i j,i≠j ∧ p∈B.curves.trace (γ i) ∧ p∈B.curves.trace (γ j) := by
  simp [crossingVertices,pairVertices_mem]

lemma crossingVertices_card_le :
    (crossingVertices B H γ hinj hsimple L hL hlength).card≤
      r*r*(Nat.floor (L/segmentScale L)+1)^2 := by
  unfold crossingVertices
  calc
    _ ≤ ∑i:Fin r,(univ.biUnion (fun j=>pairVertices B H γ hinj hsimple L hL hlength i j)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑i:Fin r,∑j:Fin r,(Nat.floor (L/segmentScale L)+1)^2 := by
      apply sum_le_sum
      intro i hi
      exact Finset.card_biUnion_le.trans (sum_le_sum (fun j hj=>pairVertices_card_le B H γ hinj hsimple L hL hlength i j))
    _ = _ := by simp;ring


def crossingParameterSet (i : Fin r) : Set ℝ :=
  {t |t∈Ico 0 (B.curves.length (γ i)) ∧
    curveParam B (γ i) t∈crossingVertices B H γ hinj hsimple L hL hlength}

lemma crossingParameterSet_finite_card (i : Fin r) :
    (crossingParameterSet B H γ hinj hsimple L hL hlength i).Finite ∧
    Nat.card (crossingParameterSet B H γ hinj hsimple L hL hlength i)≤
      r*r*(Nat.floor (L/segmentScale L)+1)^2 := by
  have hh := finite_parameter_preimage (curveParam B (γ i)) (Ico 0 (B.curves.length (γ i)))
    (hsimple i) (crossingVertices B H γ hinj hsimple L hL hlength)
  exact ⟨hh.1,hh.2.trans (crossingVertices_card_le B H γ hinj hsimple L hL hlength)⟩

def breakpoints (i : Fin r) : Finset ℝ :=
  insert 0 ((crossingParameterSet_finite_card B H γ hinj hsimple L hL hlength i).1.toFinset)

lemma zero_mem_breakpoints (i : Fin r) :
    0∈breakpoints B H γ hinj hsimple L hL hlength i := mem_insert_self _ _

lemma breakpoints_mem_period (i : Fin r) {t : ℝ}
    (ht : t∈breakpoints B H γ hinj hsimple L hL hlength i) :
    t∈Ico 0 (B.curves.length (γ i)) := by
  rcases mem_insert.mp ht with he|ht
  · rw [he]
    exact ⟨le_rfl,(B.curves.representative (γ i)).period_pos⟩
  · exact ((crossingParameterSet_finite_card B H γ hinj hsimple L hL hlength i).1.mem_toFinset.mp ht).1

lemma breakpoints_card_le (i : Fin r) :
    (breakpoints B H γ hinj hsimple L hL hlength i).card≤
      r*r*(Nat.floor (L/segmentScale L)+1)^2+1 := by
  unfold breakpoints
  have hh := crossingParameterSet_finite_card B H γ hinj hsimple L hL hlength i
  have hc : Nat.card (crossingParameterSet B H γ hinj hsimple L hL hlength i)≤
      r*r*(Nat.floor (L/segmentScale L)+1)^2 := hh.2
  rw [Nat.card_coe_set_eq,Set.ncard_eq_toFinset_card _ hh.1] at hc
  exact (card_insert_le _ _).trans (Nat.add_le_add_right hc 1)

def NetworkEdges := Σi:Fin r,Fin (breakpoints B H γ hinj hsimple L hL hlength i).card

lemma networkEdges_card_le :
    Nat.card (NetworkEdges B H γ hinj hsimple L hL hlength)≤
      r*(r*r*(Nat.floor (L/segmentScale L)+1)^2+1) := by
  simp only [NetworkEdges,Nat.card_sigma,Nat.card_fin]
  calc
    _ ≤ ∑_i:Fin r,(r*r*(Nat.floor (L/segmentScale L)+1)^2+1) :=
      sum_le_sum (fun i _=>breakpoints_card_le B H γ hinj hsimple L hL hlength i)
    _ = _ := by simp

end WP.Critical.ShortConfiguration
