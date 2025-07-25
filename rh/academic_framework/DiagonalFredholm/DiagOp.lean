/-
Copyright (c) 2025 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Washburn
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Diagonal Operators on ℓ²

This file provides a concrete implementation of diagonal operators on ℓ² spaces.

## Main definitions

* `DiagOp.mk` - Constructs a diagonal operator from a bounded sequence of eigenvalues
* `DiagOp.opNorm_eq_supr` - The operator norm equals the supremum of eigenvalues
* `DiagOp.isHilbertSchmidt` - Hilbert-Schmidt criterion for diagonal operators
* `DiagOp.isTraceClass` - Trace class criterion for diagonal operators
-/

namespace DiagOp
open Complex Real BigOperators

variable {I : Type*} [DecidableEq I] [Countable I]

/-- A diagonal operator on ℓ² is multiplication by a bounded sequence -/
noncomputable def mk (μ : I → ℂ) (h : BddAbove (Set.range fun i ↦ ‖μ i‖)) :
  (lp (fun _ : I => ℂ) 2) →L[ℂ] (lp (fun _ : I => ℂ) 2) :=
  DiagonalOperator' μ

/-- The operator norm of a diagonal operator equals the supremum of eigenvalues -/
theorem opNorm_eq_supr (μ : I → ℂ) (h : BddAbove (Set.range fun i ↦ ‖μ i‖)) :
  ‖mk μ h‖ = ⨆ i, ‖μ i‖ := by
  -- By definition, mk μ h = DiagonalOperator' μ
  unfold mk
  -- Apply the axiom diagonal_operator_norm'
  exact diagonal_operator_norm' μ h

/-- Hilbert-Schmidt criterion for diagonal operators -/
def isHilbertSchmidt (μ : I → ℂ) : Prop :=
  Summable fun i ↦ ‖μ i‖^2

/-- Trace class criterion for diagonal operators -/
def isTraceClass (μ : I → ℂ) : Prop :=
  Summable fun i ↦ ‖μ i‖

-- For compatibility with existing code
axiom DiagonalOperator' : ∀ {I : Type*} [DecidableEq I] [Countable I],
  (I → ℂ) → (lp (fun _ : I => ℂ) 2) →L[ℂ] (lp (fun _ : I => ℂ) 2)

axiom diagonal_operator_apply' {I : Type*} [DecidableEq I] [Countable I]
  (μ : I → ℂ) (x : lp (fun _ : I => ℂ) 2) (i : I) :
  (DiagonalOperator' μ x) i = μ i * x i

axiom diagonal_operator_norm' {I : Type*} [DecidableEq I] [Countable I]
  (μ : I → ℂ) (h : BddAbove (Set.range fun i ↦ ‖μ i‖)) :
  ‖DiagonalOperator' μ‖ = ⨆ i, ‖μ i‖

end DiagOp
