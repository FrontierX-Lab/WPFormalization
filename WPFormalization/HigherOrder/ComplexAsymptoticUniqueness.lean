import WPFormalization.HigherOrder.VectorAsymptoticUniqueness
/-! Complex inverse-power asymptotics have unique coefficients.
The proof samples a ray expansion along the unbounded natural-number scale
and applies the proved vector-valued uniqueness lemma. -/
noncomputable section
namespace WP.HigherOrder
open Filter
open scoped Topology
lemma real_inverse_pow_smul_complex (x:ℝ) (j:ℕ) (a:ℂ) :
    ((x^j)⁻¹:ℝ) • a=a/(x:ℂ)^j := by
  rw [Complex.real_smul]
  push_cast
  ring

def HasComplexInversePowerExpansion (f:ℝ→ℂ) (a:ℕ→ℂ) : Prop :=
  ∀K:ℕ,∃C R:ℝ,0<C ∧ 0<R ∧ ∀x:ℝ,R≤x →
    ‖f x-∑j∈Finset.range (K+1),a j/(x:ℂ)^j‖≤C/x^(K+1)
lemma HasComplexInversePowerExpansion.on_naturals (f:ℝ→ℂ) (a:ℕ→ℂ)
    (ha:HasComplexInversePowerExpansion f a) :
    HasVectorInversePowerExpansion (fun n:ℕ=>f n) (fun n:ℕ=>(n:ℝ)) a := by
  intro K
  obtain ⟨C,R,hC,hR,he⟩:=ha K
  obtain ⟨N,hN⟩:=exists_nat_ge R
  refine ⟨C,hC,N,?_⟩
  intro n hn
  have hRn : R≤(n:ℝ):=hN.trans (by exact_mod_cast hn)
  refine ⟨hR.trans_le hRn,?_⟩
  simp_rw [real_inverse_pow_smul_complex]
  exact he n hRn
lemma complex_inverse_power_expansion_unique (f:ℝ→ℂ) (a b:ℕ→ℂ)
    (ha:HasComplexInversePowerExpansion f a)
    (hb:HasComplexInversePowerExpansion f b) : a=b := by
  exact vector_inverse_power_expansion_unique (fun n:ℕ=>f n) (fun n:ℕ=>(n:ℝ)) a b
    tendsto_natCast_atTop_atTop (ha.on_naturals f a) (hb.on_naturals f b)
end WP.HigherOrder
