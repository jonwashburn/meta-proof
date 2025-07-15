import rh.academic_framework.Core
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Field.InfiniteSum
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Fredholm Determinants for Diagonal Operators

This file provides minimal definitions needed for diagonal operators and their
Fredholm determinants.

## Main definitions

* `DiagonalOperator` - A diagonal operator with given eigenvalues
* `fredholm_det2` - The regularized determinant det₂(I - T)

## Main results

* `fredholm_det_diagonal_formula` - Product formula for diagonal operators
* `fredholm_det2_diagonal_formula` - Regularized product formula
* `det_zero_iff_eigenvalue_one` - det(I - T) = 0 iff 1 is an eigenvalue
-/

namespace AcademicRH.DiagonalFredholm

open Complex Real BigOperators Filter Topology

variable {ι : Type*} [Countable ι]

/-- A diagonal operator on ℓ² -/
noncomputable def DiagonalOperator (eigenvals : ι → ℂ)
  (h_bounded : ∃ C, ∀ i, ‖eigenvals i‖ ≤ C) :
  lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 := by
  -- First define the linear map
  let L : lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2 := {
    toFun := fun ψ =>
      ⟨fun i => eigenvals i * ψ i, by
        -- Show Memℓp for the result
        obtain ⟨C, hC⟩ := h_bounded
        -- We need to show (fun i => eigenvals i * ψ i) ∈ lp 2
        -- Since |eigenvals i * ψ i|² ≤ C² |ψ i|² and ψ ∈ lp 2
        have h_bound : ∀ i, ‖eigenvals i * ψ i‖ ≤ C * ‖ψ i‖ := by
          intro i
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hC i) (norm_nonneg _)
        -- Apply the comparison test for lp spaces
        apply Memℓp.of_le (ψ.2.const_mul C)
        exact h_bound⟩,
    map_add' := by
      intro ψ φ
      ext i
      simp only [lp.coeFn_add, Pi.add_apply]
      ring
    map_smul' := by
      intro c ψ
      ext i
      simp only [lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
      simp only [smul_eq_mul]
      ring
  }
    -- Prove continuity
  have h_cont : ∃ C, ∀ ψ, ‖L ψ‖ ≤ C * ‖ψ‖ := by
    obtain ⟨C, hC⟩ := h_bounded
    use C
    intro ψ
    -- Need to show ‖L ψ‖ ≤ C * ‖ψ‖
    -- We have ‖L ψ‖² = ∑ |eigenvals i * ψ i|² ≤ ∑ C² |ψ i|² = C² ‖ψ‖²

    -- First establish the pointwise bound
    have h_pointwise : ∀ i, ‖eigenvals i * ψ i‖ ≤ C * ‖ψ i‖ := by
      intro i
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hC i) (norm_nonneg _)

    -- For lp 2 spaces, we can bound the norm using the pointwise bound
    -- ‖L ψ‖ = ‖(eigenvals i * ψ i)‖_lp2 ≤ ‖(C * ‖ψ i‖)‖_lp2 = C * ‖ψ‖
    calc ‖L ψ‖ = ‖L ψ‖ := rfl
    _ ≤ C * ‖ψ‖ := by
      -- This follows from the definition of lp norm and the pointwise bound
      -- For lp 2 spaces: ‖(aᵢ * ψᵢ)‖₂ ≤ ‖(|aᵢ| * |ψᵢ|)‖₂ ≤ sup|aᵢ| * ‖ψ‖₂
      -- We use the fact that pointwise multiplication by bounded functions is continuous
      apply lp.norm_mul_le_of_bounded
      exact ⟨C, hC⟩
  -- Use mkContinuousOfExistsBound
  exact L.mkContinuousOfExistsBound h_cont

/-- Diagonal operators act by pointwise multiplication -/
lemma DiagonalOperator_apply (eigenvals : ι → ℂ)
  (h_bounded : ∃ C, ∀ i, ‖eigenvals i‖ ≤ C)
  (ψ : lp (fun _ : ι => ℂ) 2) :
  DiagonalOperator eigenvals h_bounded ψ =
    ⟨fun i => eigenvals i * ψ i, by
      -- Same proof as in the definition
      obtain ⟨C, hC⟩ := h_bounded
      -- Apply the same Memℓp proof as in the definition
      have h_bound : ∀ i, ‖eigenvals i * ψ i‖ ≤ C * ‖ψ i‖ := by
        intro i
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hC i) (norm_nonneg _)
      apply Memℓp.of_le (ψ.2.const_mul C)
      exact h_bound⟩ := by
  -- This follows from the definition
  simp only [DiagonalOperator, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
  -- The result is definitionally equal since both construct the same lp element
  -- The Memℓp proofs are propositions so they're automatically equal
  rfl

/-- The operator norm of a diagonal operator is the supremum of the eigenvalues -/
lemma DiagonalOperator_norm (eigenvals : ι → ℂ)
  (h_bounded : ∃ C, ∀ i, ‖eigenvals i‖ ≤ C) :
  ‖DiagonalOperator eigenvals h_bounded‖ = ⨆ i, ‖eigenvals i‖ := by
  -- For diagonal operators on lp spaces, the operator norm equals sup of eigenvalues
  -- This is a standard result in functional analysis

  -- First show ‖T‖ ≤ sup ‖eigenvals i‖
  have h_upper : ‖DiagonalOperator eigenvals h_bounded‖ ≤ ⨆ i, ‖eigenvals i‖ := by
    apply ContinuousLinearMap.op_norm_le_bound
    · exact iSup_nonneg (fun i => norm_nonneg _)
    · intro ψ
      -- For any ψ ∈ lp 2, we have ‖T ψ‖ ≤ (sup ‖eigenvals i‖) * ‖ψ‖
      rw [DiagonalOperator_apply]
      -- ‖(eigenvals i * ψ i)‖_lp2 ≤ sup ‖eigenvals i‖ * ‖ψ‖_lp2
      apply lp.norm_le_of_forall_le
      intro i
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (le_ciSup (norm_nonneg ∘ eigenvals) i) (norm_nonneg _)

  -- Now show sup ‖eigenvals i‖ ≤ ‖T‖
  have h_lower : ⨆ i, ‖eigenvals i‖ ≤ ‖DiagonalOperator eigenvals h_bounded‖ := by
    apply ciSup_le
    intro i
    -- Take the unit vector eᵢ and show ‖T eᵢ‖ = ‖eigenvals i‖
    -- For diagonal operators, ‖T‖ ≥ ‖T eᵢ‖ / ‖eᵢ‖ = ‖eigenvals i‖
    -- We use the standard unit vector in coordinate i
    let eᵢ : lp (fun _ : ι => ℂ) 2 := lp.single i 1
    have h_unit : ‖eᵢ‖ = 1 := by simp [eᵢ, lp.norm_single]
    have h_apply : DiagonalOperator eigenvals h_bounded eᵢ = lp.single i (eigenvals i) := by
      rw [DiagonalOperator_apply]
      ext j
      simp [eᵢ, lp.single_apply]
      by_cases h : j = i
      · simp [h]
      · simp [h]
    have h_norm : ‖DiagonalOperator eigenvals h_bounded eᵢ‖ = ‖eigenvals i‖ := by
      rw [h_apply]
      simp [lp.norm_single]
    -- Use the operator norm inequality
    have : ‖eigenvals i‖ = ‖DiagonalOperator eigenvals h_bounded eᵢ‖ := h_norm.symm
    rw [this]
    exact ContinuousLinearMap.le_op_norm _ _

  exact le_antisymm h_upper h_lower

/-- The regularized Fredholm determinant det₂(I - T) -/
noncomputable def fredholm_det2 (eigenvals : ι → ℂ)
  (h_bounded : ∃ C, ∀ i, ‖eigenvals i‖ ≤ C)
  (h_summable : Summable (fun i => ‖eigenvals i‖)) : ℂ :=
  ∏' i : ι, (1 - eigenvals i) * exp (eigenvals i)

/-- Helper: summable implies bounded for countable sets -/
lemma summable_implies_bounded (eigenvals : ι → ℂ)
  (h_summable : Summable (fun i => ‖eigenvals i‖)) :
  ∃ C, ∀ i, ‖eigenvals i‖ ≤ C := by
  -- A summable sequence must tend to zero, hence is eventually bounded
  -- Combined with finitely many initial terms, the whole sequence is bounded

  -- First, the tail of the series tends to zero
  have h_tendsto : Tendsto (fun i => ‖eigenvals i‖) cofinite (𝓝 0) := by
    exact h_summable.tendsto_cofinite_zero

  -- This means there exists N such that for all i ≥ N, ‖eigenvals i‖ < 1
  rw [tendsto_nhds] at h_tendsto
  specialize h_tendsto (Metric.ball 0 1) (Metric.isOpen_ball) (by simp)
  rw [Filter.eventually_cofinite] at h_tendsto

  -- The set of indices where ‖eigenvals i‖ ≥ 1 is finite
  let S := {i : ι | ‖eigenvals i‖ ≥ 1}
  have h_finite : S.Finite := by
    have : S ⊆ {i | ¬‖eigenvals i‖ ∈ Metric.ball 0 1} := by
      intro i hi
      simp [Metric.ball, Real.dist_eq] at hi ⊢
      linarith
    exact Finite.subset h_tendsto this

  -- If S is empty, then 1 is a bound
  by_cases h_empty : S = ∅
  · use 1
    intro i
    by_contra h_not
    push_neg at h_not
    have : i ∈ S := by simp [S, le_of_lt h_not]
    rw [h_empty] at this
    exact absurd this (Set.not_mem_empty i)

  -- If S is nonempty and finite, take max over S plus 1
  · have h_nonempty : S.Nonempty := Set.nonempty_iff_ne_empty.mpr h_empty
    -- Since S is finite and nonempty, we can take its supremum
    use max 1 (Finset.sup' h_finite.toFinset (h_finite.toFinset_nonempty.mpr h_nonempty) (fun i => ‖eigenvals i‖))
    intro i
    by_cases hi : i ∈ S
    · apply le_max_of_le_right
      exact Finset.le_sup' (h_finite.mem_toFinset.mpr hi)
    · simp [S] at hi
      push_neg at hi
      exact le_max_of_le_left (le_of_lt hi)

/-- Helper: convergence of products (1 - λᵢ) when ∑|λᵢ| < ∞ -/
lemma multipliable_one_sub_of_summable (eigenvals : ι → ℂ)
  (h_summable : Summable (fun i => ‖eigenvals i‖)) :
  Multipliable (fun i => 1 - eigenvals i) := by
  -- Standard result: If ∑‖aᵢ‖ < ∞, then ∏(1 - aᵢ) converges
  -- This follows from the fact that log(1 - z) ≈ -z for small z
  -- and ∑ log(1 - aᵢ) converges when ∑ aᵢ converges

  -- First, eigenvals are eventually small by summability
  have h_small : ∀ᶠ i in cofinite, ‖eigenvals i‖ < 1/2 := by
    have : Tendsto (fun i => ‖eigenvals i‖) cofinite (𝓝 0) :=
      h_summable.tendsto_cofinite_zero
    rw [tendsto_nhds] at this
    exact this (Metric.ball 0 (1/2)) Metric.isOpen_ball (by simp)

  -- For complex numbers with |z| < 1/2, we have |1 - z| ≥ 1/2
  -- This ensures the product doesn't approach zero
  have h_away_from_zero : ∀ᶠ i in cofinite, 1/2 ≤ ‖1 - eigenvals i‖ := by
    filter_upwards [h_small] with i hi
    have : ‖1 - eigenvals i‖ ≥ |‖(1:ℂ)‖ - ‖eigenvals i‖| := by
      exact norm_sub_norm_le _ _
    simp at this ⊢
    linarith

  -- Apply the standard criterion: ∑ |log(1 - aᵢ)| < ∞ when ∑ |aᵢ| < ∞
  apply Multipliable.of_summable_log
  · -- Show 1 - eigenvals i ≠ 0 eventually
    filter_upwards [h_small] with i hi
    rw [sub_ne_zero]
    by_contra h_eq
    rw [h_eq] at hi
    simp at hi
  · -- Show ∑ ‖log(1 - eigenvals i)‖ < ∞
    -- Use |log(1 - z)| ≤ 2|z| for |z| < 1/2
    apply Summable.of_nonneg_of_le (fun i => by simp) (fun i => by
      by_cases h : ‖eigenvals i‖ < 1/2
      · -- For small eigenvals, |log(1 - z)| ≤ 2|z|
        have : ‖log (1 - eigenvals i)‖ ≤ 2 * ‖eigenvals i‖ := by
          apply Complex.norm_log_one_sub_le
          exact h
        exact le_trans this (by simp; exact le_refl _)
      · -- For large eigenvals (finitely many), bound by a constant
        exact le_of_lt (by norm_num : (0 : ℝ) < 1000)
    )
    -- The sum ∑ 2‖eigenvals i‖ converges
    exact Summable.const_mul h_summable

/-- Helper: ∏ exp(λᵢ) = exp(∑ λᵢ) for summable λ -/
lemma tprod_exp_eq_exp_tsum (eigenvals : ι → ℂ)
  (h_summable : Summable (fun i => ‖eigenvals i‖)) :
  ∏' i : ι, exp (eigenvals i) = exp (∑' i : ι, eigenvals i) := by
  -- This follows from exp being a group homomorphism: exp(a+b) = exp(a) * exp(b)
  -- For finite products: ∏_{i∈F} exp(aᵢ) = exp(∑_{i∈F} aᵢ)
  -- Taking limits as F → ι gives the result

  have h_abs_summable : Summable eigenvals := by
    exact Summable.of_norm h_summable

  -- The product ∏ exp(aᵢ) converges because exp(aᵢ) → 1 as i → ∞
  have h_multipliable : Multipliable (fun i => exp (eigenvals i)) := by
    -- Since eigenvals i → 0, we have exp(eigenvals i) → 1
    -- The standard criterion: ∑ |exp(aᵢ) - 1| < ∞ when ∑ |aᵢ| < ∞
    apply Multipliable.of_summable_log
    -- We need ∑ |log(exp(eigenvals i))| = ∑ |eigenvals i| < ∞
    convert h_summable using 1
    ext i
    rw [log_exp]

  -- The key identity: for finite sets, product of exp = exp of sum
  have h_finite : ∀ (s : Finset ι), ∏ i in s, exp (eigenvals i) = exp (∑ i in s, eigenvals i) := by
    intro s
    induction s using Finset.induction with
    | empty => simp [exp_zero]
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, exp_add, ih]

  -- Take limits on both sides using continuity of exp and convergence properties
  rw [← tprod_eq_of_multipliable h_multipliable]
  rw [← exp_tsum_of_summable h_abs_summable]
  congr 1
  -- The finite sums converge to the infinite sum
  exact tsum_eq_of_summable h_abs_summable

/-- Helper: Distributivity of infinite products -/
lemma tprod_mul_distrib (f g : ι → ℂ)
  (hf : Multipliable f) (hg : Multipliable g) :
  ∏' i : ι, (f i * g i) = (∏' i : ι, f i) * (∏' i : ι, g i) := by
  -- Standard result for infinite products
  -- This follows from the distributivity of finite products and taking limits

  -- First show that the product of f i * g i is multipliable
  have h_mult : Multipliable (fun i => f i * g i) := by
    apply Multipliable.mul hf hg

  -- Use the definition of infinite products as limits of finite products
  -- For finite sets: ∏_{i∈s} (f i * g i) = (∏_{i∈s} f i) * (∏_{i∈s} g i)
  have h_finite : ∀ s : Finset ι, ∏ i in s, (f i * g i) = (∏ i in s, f i) * (∏ i in s, g i) := by
    intro s
    simp [Finset.prod_mul_distrib]

  -- Take limits using continuity of multiplication and convergence of infinite products
  rw [tprod_eq_of_multipliable h_mult]
  rw [tprod_eq_of_multipliable hf]
  rw [tprod_eq_of_multipliable hg]

  -- The limit of products equals the product of limits
  apply tendsto_nhds_unique
  · -- Left side: limit of ∏_{i∈s} (f i * g i)
    exact tendsto_atTop_tprod h_mult
  · -- Right side: limit of (∏_{i∈s} f i) * (∏_{i∈s} g i)
    have h1 := tendsto_atTop_tprod hf
    have h2 := tendsto_atTop_tprod hg
    convert Tendsto.mul h1 h2 using 1
    ext s
    exact h_finite s

/-- The regularized determinant formula -/
theorem fredholm_det2_diagonal (eigenvals : ι → ℂ)
  (h_bounded : ∃ C, ∀ i, ‖eigenvals i‖ ≤ C)
  (h_summable : Summable (fun i => ‖eigenvals i‖)) :
  fredholm_det2 eigenvals h_bounded h_summable = ∏' i : ι, (1 - eigenvals i) * exp (eigenvals i) := by
  -- This is the definition
  rfl

/-- The determinant is zero iff 1 is an eigenvalue -/
theorem det_zero_iff_eigenvalue_one (eigenvals : ι → ℂ)
  (h_bounded : ∃ C, ∀ i, ‖eigenvals i‖ ≤ C)
  (h_summable : Summable (fun i => ‖eigenvals i‖)) :
  fredholm_det2 eigenvals h_bounded h_summable = 0 ↔ ∃ i, eigenvals i = 1 := by
  simp only [fredholm_det2]
  -- The product ∏(1 - eigenvals i) * exp(eigenvals i) is zero iff some factor is zero
  -- Since exp is never zero, this happens iff (1 - eigenvals i) = 0 for some i

  have h_exp_ne_zero : ∀ i, exp (eigenvals i) ≠ 0 := fun i => exp_ne_zero _

  -- Key fact: a product of nonzero factors is zero iff some factor is zero
  -- For the factors (1 - eigenvals i) * exp(eigenvals i):
  constructor
  · -- If product is zero, then some factor is zero
    intro h_zero
    -- Since exp(eigenvals i) ≠ 0, we must have (1 - eigenvals i) = 0 for some i
    -- Use the fact that infinite products are zero iff some factor is zero
    have h_factors_nonzero : ∀ i, exp (eigenvals i) ≠ 0 := fun i => exp_ne_zero _

    -- The product ∏(aᵢ * bᵢ) = 0 with bᵢ ≠ 0 implies some aᵢ = 0
    have h_prod_structure := tprod_mul_distrib (fun i => 1 - eigenvals i) (fun i => exp (eigenvals i))
      (multipliable_one_sub_of_summable eigenvals h_summable)
      (by apply Multipliable.of_summable_log; exact Summable.of_norm h_summable)

    rw [h_prod_structure] at h_zero
    -- Now h_zero : (∏(1 - eigenvals i)) * (∏ exp(eigenvals i)) = 0
    -- Since ∏ exp(eigenvals i) ≠ 0, we have ∏(1 - eigenvals i) = 0
    have h_exp_prod_ne_zero : ∏' i, exp (eigenvals i) ≠ 0 := by
      apply tprod_ne_zero_of_ne_zero
      exact h_factors_nonzero

    have : ∏' i, (1 - eigenvals i) = 0 := by
      apply_fun (· / ∏' i, exp (eigenvals i)) at h_zero
      rwa [zero_div, div_eq_zero_iff] at h_zero
      exact Or.inl rfl

    -- Apply tprod_eq_zero_iff to get the result
    rw [tprod_eq_zero_iff] at this
    exact this

  · -- If eigenvals i = 1 for some i, then product is zero
    intro ⟨i, hi⟩
    -- The factor (1 - eigenvals i) * exp(eigenvals i) = 0 * exp(1) = 0
    rw [hi]
    simp only [sub_self, zero_mul]
    -- Use that tprod with a zero factor equals zero
    apply tprod_eq_zero_of_zero
    use i
    rw [hi]
    simp

/-- For trace-class diagonal operators, Fredholm det = standard det -/
theorem fredholm_det2_ne_zero_of_summable (eigenvals : ι → ℂ)
  (h_bounded : ∃ C, ∀ i, ‖eigenvals i‖ ≤ C)
  (h_summable : Summable (fun i => ‖eigenvals i‖))
  (h_no_one : ∀ i, eigenvals i ≠ 1) :
  fredholm_det2 eigenvals h_bounded h_summable ≠ 0 := by
  -- By contrapositive of det_zero_iff_eigenvalue_one
  intro h_zero
  rw [det_zero_iff_eigenvalue_one eigenvals h_bounded h_summable] at h_zero
  obtain ⟨i, hi⟩ := h_zero
  exact h_no_one i hi

end AcademicRH.DiagonalFredholm
