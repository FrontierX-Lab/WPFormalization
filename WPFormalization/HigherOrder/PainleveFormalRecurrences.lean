import WPFormalization.HigherOrder.EndpointFormal
/-! Stability of the actual rational coefficient tables, their full scalar recurrences and uniqueness. -/
noncomputable section
namespace WP.HigherOrder
lemma zeroInstantonTable_stable (n k : ℕ) (hk : k ≤ n) :
    zeroInstantonTable n k=zeroInstantonCoefficient k := by
  induction n with
  | zero =>
      have hk0 : k=0 := by omega
      subst k
      rfl
  | succ n ih =>
      by_cases he : k=n+1
      · subst k;rfl
      · have hk' : k ≤ n := by omega
        simpa only [zeroInstantonTable,if_neg he] using ih hk'
lemma zeroInstantonCoefficient_recursion (n : ℕ) :
    zeroInstantonCoefficient (n+1)=
      ((25*(n:ℚ)^2-1)/48)*zeroInstantonCoefficient n-
        (1/2:ℚ)*∑ j ∈ Finset.Icc 1 n,
          zeroInstantonCoefficient j*zeroInstantonCoefficient (n+1-j) := by
  change zeroInstantonTable (n+1) (n+1)=_
  simp only [zeroInstantonTable,ite_true]
  rw [zeroInstantonTable_stable n n le_rfl]
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_Icc.mp hj
  rw [zeroInstantonTable_stable n j hj'.2,
    zeroInstantonTable_stable n (n+1-j) (by omega)]
lemma jumpTable_stable (n k : ℕ) (hk : k ≤ n) :
    jumpTable n k=jumpCoefficient k := by
  induction n with
  | zero =>
      have hk0 : k=0 := by omega
      subst k
      rfl
  | succ n ih =>
      by_cases he : k=n+1
      · subst k;rfl
      · have hk' : k ≤ n := by omega
        simpa only [jumpTable,if_neg he] using ih hk'
lemma jumpCoefficient_recursion (n : ℕ) :
    jumpCoefficient (n+1)=
      -(((n+1:ℕ):ℚ)*n*jumpCoefficient n+
        ∑ g ∈ Finset.Icc 1 ((n+2)/2), jumpPotential g*jumpCoefficient (n+2-2*g))/
        (2*(n+1:ℕ)) := by
  change jumpTable (n+1) (n+1)=_
  simp only [jumpTable,ite_true]
  rw [jumpTable_stable n n le_rfl]
  congr 3
  apply Finset.sum_congr rfl
  intro g hg
  have hg' := Finset.mem_Icc.mp hg
  have hb : 2*g ≤ n+2 := by omega
  rw [jumpTable_stable n (n+2-2*g) (by omega)]
lemma zeroInstantonCoefficient_unique (u : ℕ → ℚ) (h0 : u 0=1)
    (hr : ∀ n, u (n+1)=((25*(n:ℚ)^2-1)/48)*u n-
      (1/2:ℚ)*∑ j ∈ Finset.Icc 1 n, u j*u (n+1-j)) :
    u=zeroInstantonCoefficient := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simpa using h0
      | succ n =>
          rw [hr,zeroInstantonCoefficient_recursion,ih n (by omega)]
          congr 2
          apply Finset.sum_congr rfl
          intro j hj
          have hj' := Finset.mem_Icc.mp hj
          rw [ih j (by omega),ih (n+1-j) (by omega)]
lemma jumpCoefficient_unique (v : ℕ → ℚ) (h0 : v 0=1)
    (hr : ∀ n, v (n+1)=
      -(((n+1:ℕ):ℚ)*n*v n+
        ∑ g ∈ Finset.Icc 1 ((n+2)/2), jumpPotential g*v (n+2-2*g))/(2*(n+1:ℕ))) :
    v=jumpCoefficient := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simpa using h0
      | succ n =>
          rw [hr,jumpCoefficient_recursion,ih n (by omega)]
          congr 3
          apply Finset.sum_congr rfl
          intro g hg
          have hg' := Finset.mem_Icc.mp hg
          rw [ih (n+2-2*g) (by omega)]
end WP.HigherOrder
