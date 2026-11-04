import Mathlib.Data.Fintype.Quotient
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Compactness.Compact

/-!
Finite families partitioned by chains of actual nonempty intersections.
Indices are never identified merely because their sets agree: distinct repeated
nonempty sets lie in the same nonsingleton index block.
-/

namespace WP.FiniteIntersectionClusters

open Set Relation

universe u v
variable {ι : Type u} {X : Type v}

/-- The actual nonempty-intersection relation. -/
def intersects (W : ι → Set X) (i j : ι) : Prop := (W i ∩ W j).Nonempty

instance intersects_symm (W : ι → Set X) : Std.Symm (intersects W) where
  symm i j h := by simpa [intersects, Set.inter_comm] using h

/-- A block of indices connected by finite intersection chains. -/
def Cluster (W : ι → Set X) := Quotient (Relation.EqvGen.setoid (intersects W))

/-- The block containing the actual index `i`. -/
def cluster (W : ι → Set X) (i : ι) : Cluster W := Quotient.mk _ i

instance [Finite ι] (W : ι → Set X) : Finite (Cluster W) :=
  inferInstanceAs (Finite (Quotient _))

noncomputable instance [Fintype ι] (W : ι → Set X) : Fintype (Cluster W) :=
  Fintype.ofFinite (Cluster W)

theorem cluster_surjective (W : ι → Set X) : Function.Surjective (cluster W) := by
  intro c
  exact Quotient.inductionOn c fun i => ⟨i, rfl⟩

theorem cluster_eq_iff (W : ι → Set X) (i j : ι) :
    cluster W i = cluster W j ↔ Relation.ReflTransGen (intersects W) i j := by
  rw [← Relation.EqvGen.eqvGen_eq_reflTransGen]
  constructor
  · exact Quotient.exact
  · intro h
    exact @Quotient.sound ι (Relation.EqvGen.setoid (intersects W)) i j h

section FiniteFamily
variable [Fintype ι] (W : ι → Set X)

/-- The finite block of actual indices, retaining multiplicities of repeated sets. -/
noncomputable def members (c : Cluster W) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => cluster W i = c)

@[simp] theorem mem_members (c : Cluster W) (i : ι) :
    i ∈ members W c ↔ cluster W i = c := by
  classical
  simp [members]

theorem members_nonempty (c : Cluster W) : (members W c).Nonempty := by
  obtain ⟨i, rfl⟩ := cluster_surjective W c
  exact ⟨i, (mem_members W _ _).2 rfl⟩

/-- The actual union carried by one block. -/
noncomputable def carrier (c : Cluster W) : Set X := ⋃ i ∈ members W c, W i

theorem subset_carrier (i : ι) : W i ⊆ carrier W (cluster W i) := by
  exact Set.subset_biUnion_of_mem ((mem_members W _ _).2 rfl)

theorem carrier_nonempty (hW : ∀ i, (W i).Nonempty) (c : Cluster W) :
    (carrier W c).Nonempty := by
  obtain ⟨i, hi⟩ := members_nonempty W c
  exact (hW i).mono (Set.subset_biUnion_of_mem hi)

/-- Different blocks have disjoint actual unions. -/
theorem carrier_disjoint {c d : Cluster W} (hcd : c ≠ d) :
    Disjoint (carrier W c) (carrier W d) := by
  rw [Set.disjoint_left]
  intro x hx hy
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 hx
  obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.1 hy
  have hij : cluster W i = cluster W j :=
    Quotient.sound (Relation.EqvGen.rel _ _ ⟨x, hxi, hxj⟩)
  exact hcd (((mem_members W c i).1 hi).symm.trans
    (hij.trans ((mem_members W d j).1 hj)))

theorem iUnion_carrier : (⋃ c : Cluster W, carrier W c) = ⋃ i, W i := by
  apply Set.Subset.antisymm
  · rintro x hx
    obtain ⟨c, hc⟩ := Set.mem_iUnion.1 hx
    obtain ⟨i, _, hxi⟩ := Set.mem_iUnion₂.1 hc
    exact Set.mem_iUnion_of_mem i hxi
  · rintro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    exact Set.mem_iUnion_of_mem (cluster W i) (subset_carrier W i hi)

/-- Singleton is an index statement: another equal nonempty set is not ignored. -/
theorem members_cluster_eq_singleton_iff (i : ι) :
    members W (cluster W i) = {i} ↔ ∀ j, j ≠ i → Disjoint (W i) (W j) := by
  classical
  constructor
  · intro hmem j hji
    rw [Set.disjoint_left]
    intro x hxi hxj
    have heq : cluster W i = cluster W j :=
      Quotient.sound (Relation.EqvGen.rel _ _ ⟨x, hxi, hxj⟩)
    have hj : j ∈ members W (cluster W i) := (mem_members W _ _).2 heq.symm
    rw [hmem, Finset.mem_singleton] at hj
    exact hji hj
  · intro hdis
    have only : ∀ j, intersects W i j → j = i := by
      intro j hij
      by_contra hji
      obtain ⟨x, hxi, hxj⟩ := hij
      exact Set.disjoint_left.1 (hdis j hji) hxi hxj
    have path_eq : ∀ j, Relation.ReflTransGen (intersects W) i j → j = i := by
      intro j hij
      induction hij with
      | refl => rfl
      | @tail a b _ hab ih =>
        subst a
        exact only b hab
    ext j
    rw [mem_members, Finset.mem_singleton]
    constructor
    · intro hij
      exact path_eq j ((cluster_eq_iff W i j).1 hij.symm)
    · rintro rfl
      rfl

variable [TopologicalSpace X]

/-- Each intersection-chain block carries a preconnected actual union. -/
theorem carrier_isPreconnected (hW : ∀ i, IsPreconnected (W i)) (c : Cluster W) :
    IsPreconnected (carrier W c) := by
  apply IsPreconnected.biUnion_of_reflTransGen (fun i _ => hW i)
  intro i hi j hj
  have hij : cluster W i = cluster W j :=
    ((mem_members W c i).1 hi).trans ((mem_members W c j).1 hj).symm
  have hpath := (cluster_eq_iff W i j).1 hij
  have liftpath : ∀ {a b}, Relation.ReflTransGen (intersects W) a b →
      a ∈ members W c →
      Relation.ReflTransGen (fun x y => (W x ∩ W y).Nonempty ∧ x ∈ members W c) a b := by
    intro a b hab
    induction hab with
    | refl => intro _; exact .refl
    | @tail b d hab hbd ih =>
      intro ha
      apply (ih ha).tail
      refine ⟨hbd, ?_⟩
      apply (mem_members W c b).2
      exact ((cluster_eq_iff W a b).2 hab).symm.trans ((mem_members W c a).1 ha)
  exact liftpath hpath hi

theorem carrier_isConnected (hne : ∀ i, (W i).Nonempty)
    (hW : ∀ i, IsPreconnected (W i)) (c : Cluster W) : IsConnected (carrier W c) :=
  ⟨carrier_nonempty W hne c, carrier_isPreconnected W hW c⟩

theorem carrier_isCompact (hW : ∀ i, IsCompact (W i)) (c : Cluster W) :
    IsCompact (carrier W c) :=
  (members W c).isCompact_biUnion (fun i _ => hW i)

end FiniteFamily
end WP.FiniteIntersectionClusters
