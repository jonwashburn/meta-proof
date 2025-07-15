import rh.academic_framework.Core
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Basic


/-!
# Weierstrass Product Theory

This file contains helper lemmas for Weierstrass product convergence.

## Main results

* `log_one_sub_bound` - Bound on |log(1-z)| for small z
* `multipliable_one_sub_of_summable` - Convergence criterion for ∏(1-aᵢ)
-/

namespace AcademicRH.DiagonalFredholm

open Complex Real BigOperators

/-- Custom implementation of the logarithm bound for |z| < 1/2 -/
lemma norm_log_one_sub_le {z : ℂ} (hz : ‖z‖ < 1 / 2) : ‖log (1 - z)‖ ≤ 2 * ‖z‖ := by
  -- This is a standard bound that follows from the Taylor series of log(1-z)
  -- For |z| < 1/2, we have |log(1-z)| ≤ |z|/(1-|z|) ≤ 2|z|
  -- The proof uses that the Taylor series converges absolutely for |z| < 1

  -- First establish that |z| < 1
  have h1 : ‖z‖ < 1 := by
    have : (1 / 2 : ℝ) < 1 := by norm_num
    exact lt_trans hz this

  -- Use mathlib's bound: |log(1-z)| ≤ |z|/(1-|z|) for |z| < 1
  have h_bound : ‖log (1 - z)‖ ≤ ‖z‖ / (1 - ‖z‖) := by
    exact Complex.norm_log_one_sub_le h1

  -- Show that |z|/(1-|z|) ≤ 2|z| when |z| < 1/2
  have h_denom : 1 / 2 ≤ 1 - ‖z‖ := by
    have : ‖z‖ ≤ 1 / 2 := le_of_lt hz
    linarith

  have h_div : ‖z‖ / (1 - ‖z‖) ≤ 2 * ‖z‖ := by
    rw [div_le_iff]
    · ring_nf
      have : ‖z‖ ≤ (1 / 2) * (1 - ‖z‖) := by
        have : ‖z‖ < 1 / 2 := hz
        have h_pos : 0 < 1 - ‖z‖ := by linarith [norm_nonneg z]
        rw [mul_div_cancel_left (1 - ‖z‖) (ne_of_gt h_pos)] at h_denom
        exact mul_le_of_le_one_right (norm_nonneg z) (by linarith [this])
      linarith
    · linarith [norm_nonneg z]

  exact le_trans h_bound h_div

/-- Alias for compatibility -/
lemma log_one_sub_bound {z : ℂ} (hz : ‖z‖ < 1 / 2) :
  ‖log (1 - z)‖ ≤ 2 * ‖z‖ := norm_log_one_sub_le hz

/-- If ∑ aᵢ converges and each |aᵢ| < 1/2, then ∏(1-aᵢ) converges -/
lemma multipliable_one_sub_of_summable {ι : Type*} {a : ι → ℂ}
  (h_sum : Summable a) (h_small : ∀ i, ‖a i‖ < 1/2) :
  Multipliable (fun i => 1 - a i) := by
  -- This is a standard result in complex analysis
  -- The proof uses the relationship between products and sums via logarithms
  -- Since |log(1 - aᵢ)| ≤ 2|aᵢ| and ∑|aᵢ| converges, the product converges

  -- Use the criterion: ∏(1-aᵢ) converges iff ∑log(1-aᵢ) converges absolutely
  apply Multipliable.of_summable_log

  -- Show that ∑log(1-aᵢ) converges absolutely
  apply Summable.of_norm

  -- Use the bound |log(1-aᵢ)| ≤ 2|aᵢ|
  have h_bound : ∀ i, ‖log (1 - a i)‖ ≤ 2 * ‖a i‖ := by
    intro i
    exact norm_log_one_sub_le (h_small i)

  -- Since ∑|aᵢ| converges, ∑2|aᵢ| converges
  have h_summable_norm : Summable (fun i => ‖a i‖) := by
    exact Summable.of_norm h_sum

  have h_summable_bound : Summable (fun i => 2 * ‖a i‖) := by
    exact Summable.const_mul h_summable_norm

  -- Apply comparison test
  exact Summable.of_nonneg_of_le (fun i => norm_nonneg _) h_bound h_summable_bound

end AcademicRH.DiagonalFredholm
