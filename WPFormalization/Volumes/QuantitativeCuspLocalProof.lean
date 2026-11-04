import WPFormalization.Volumes.MarkedQuantitativeL1
/-! The original quantitative local limit statement, proved from the actual
uniform characteristic L1 estimate and exact all-integer Fourier inversion.
There is no assumed local-limit, Gaussian chart, or model-comparison input. -/
noncomputable section
namespace WP
open Set Filter Complex MeasureTheory
open scoped Topology
set_option autoImplicit false
lemma quantitative_cusp_local_proof (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C κ M₀ : ℝ, 0 < C ∧ 0 < κ ∧ 0 < M₀ ∧
    ∀ g : ℕ, ∀ x ∈ Set.Ioo 0 xCritical,
      let h : ℝ := complexity g p
      let μ := h*Psi x
      let σ := Real.sqrt (h*euler Psi x)
      M₀ ≤ min h μ → ∀ k : ℤ,
        |σ*(if 0 ≤ k then cuspMass P g p k.toNat x else 0) -
          Real.exp (-((k : ℝ)-μ)^2/(2*σ^2))/Real.sqrt (2*Real.pi)| ≤
          C*Real.rpow (min h μ) (-κ)  :=by
  obtain ⟨C,κ,M₀,hC,hκ,hM₀,hL1⟩:=marked_characteristic_quantitative_l1 P p hp
  refine ⟨C/(2*Real.pi),κ,M₀,div_pos hC (by positivity),hκ,hM₀,?_⟩
  intro g x hx
  dsimp only
  intro hm k
  have hmpos:0 < min (complexity g p:ℝ) ((complexity g p:ℝ)*Psi x):=hM₀.trans_le hm
  have hh:0<(complexity g p:ℝ):=hmpos.trans_le (min_le_left _ _)
  have hn:0<complexity g p:=by exact_mod_cast hh
  have hs:Stable g p:=by unfold Stable complexity at *;omega
  have hb:=hL1 g x hx hm
  have ht:=cuspMass_error_of_characteristic_l1 P g p hp hs hn x hx _ hb k
  convert ht using 1 <;>simp only[Real.rpow_eq_pow] <;>ring
end WP
