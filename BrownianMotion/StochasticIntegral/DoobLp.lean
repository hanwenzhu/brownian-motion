/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Architect
import BrownianMotion.Auxiliary.Martingale
import Mathlib.Probability.Martingale.OptionalStopping

/-! # Doob's Lᵖ inequality

-/

open MeasureTheory Filter Finset
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → E} {𝓕 : Filtration ι mΩ}
  {Y : ι → Ω → ℝ}

@[blueprint
  "lem:doob_countable"
  (title := "Doob's maximal Inequality for countable")
  (statement := /-- Let $X : I \rightarrow \Omega \rightarrow \mathbb{R}$ be a non-negative
    sub-martingale with $I$ countable.
    Then for every $M \in I,\lambda > 0$ and $p>1$ we have
    \begin{align*}
      P\left( \sup_{i\in I, i\leq M}X_i\geq\lambda \right)
      \le \frac{\mathbb{E}\left[X_M \mathbb{I}_{\sup_{i \le M}X_i \ge \lambda}\right]}{\lambda}
      \le \frac{\mathbb{E}[X_M]}{\lambda}
      \: .
    \end{align*} -/)
  (proof := /-- For any finite subset $J \subset I$ with $M \in J$, we have by
    Lemma~\ref{lem:maximal_ineq}
    \begin{align*}
      P\left( \sup_{i\in J, i \le M}X_i\geq\lambda \right)
      \le \frac{\mathbb{E}\left[X_{M} \mathbb{I}_{\sup_{i \in J, i \le M}X_i \ge
      \lambda}\right]}{\lambda}
      \: .
    \end{align*}
    Then we build a countable increasing sequence of finite sets $J_n$ with $\sup_{i\in I, i\leq
    M}X_i = \sup_n\sup_{i\in J_n, i \le M}X_i$ and conclude by monotone convergence.
    %See 8.1.1 Pascucci. -/)
  (proofUses := ["lem:maximal_ineq"])
  (latexEnv := "lemma")]
theorem maximal_ineq_countable [Countable ι] [IsFiniteMeasure P]
    (hsub : Submartingale Y 𝓕 P) (hnonneg : 0 ≤ Y) (ε : ℝ≥0) (n : ι) :
    ε • P {ω | (ε : ℝ) ≤ ⨆ i ≤ n, Y i ω} ≤
     ENNReal.ofReal (∫ ω in {ω | (ε : ℝ) ≤ ⨆ i ≤ n, Y i ω}, Y n ω ∂P) := by
  sorry

theorem maximal_ineq_norm_countable [Countable ι] [IsFiniteMeasure P]
    (hsub : Martingale X 𝓕 P) (ε : ℝ≥0) (n : ι) :
    ε • P {ω | (ε : ℝ) ≤ ⨆ i ≤ n, ‖X i ω‖} ≤
     ENNReal.ofReal (∫ ω in {ω | (ε : ℝ) ≤ ⨆ i ≤ n, ‖X i ω‖}, ‖X n ω‖ ∂P) := by
  sorry

@[blueprint
  "thm:doob_ineq"
  (title := "Doob Inequality")
  (statement := /-- Let $X: \mathbb{R}_+ \to \Omega \to \mathbb{R}$ be a right-continuous
    non-negative sub-martingale.
    For every $T \in \mathbb{R}_+$ and $\lambda>0$ we have
    \begin{align*}
      P\left( \sup_{t\in[0,T]}X_t \geq \lambda \right)
      \leq \frac{\mathbb{E}[X_T \mathbb{I}_{\sup_{i \le T}X_i \ge \lambda}]}{\lambda}
      \leq \frac{\mathbb{E}[X_T]}{\lambda}
      \: .
    \end{align*} -/)
  (proof := /-- Since $X$ is right-continuous and $[0,T]$ is a compact interval, we have that
    \begin{align*}
      \sup_{t\in[0,T]}X_t = \sup_{t\in[0,T] \cap \mathbb{Q}}X_t
      \: .
    \end{align*}
    Then apply Lemma~\ref{lem:doob_countable} with $I = [0,T] \cap \mathbb{Q}$ and $M = T$. -/)
  (proofUses := ["lem:doob_countable"])]
theorem maximal_ineq [SecondCountableTopology ι] [IsFiniteMeasure P]
    (hsub : Submartingale Y 𝓕 P) (hnonneg : 0 ≤ Y) (ε : ℝ≥0) (n : ι) :
    ε • P {ω | (ε : ℝ) ≤ ⨆ i ≤ n, Y i ω} ≤
     ENNReal.ofReal (∫ ω in {ω | (ε : ℝ) ≤ ⨆ i ≤ n, Y i ω}, Y n ω ∂P) := by
  obtain ⟨T, hT_countable, hT_dense⟩ := TopologicalSpace.exists_countable_dense ι
  sorry

@[blueprint
  "cor:doob_ineq_norm"
  (title := "Doob Inequality for normed spaces")
  (statement := /-- Let $X:\mathbb{R}_+ \to \Omega \to E$ be a right-continuous martingale with
    values in a normed space $E$.
    For every $T$ and $\lambda>0$ we have
    $$
    P\left( \sup_{t\in[0,T]} \lVert X_t \rVert \geq \lambda \right)
    \leq \frac{\mathbb{E}[\lVert X_T \rVert]}{\lambda}.
    $$ -/)
  (proof := /-- By Corollary~\ref{cor:Martingale.submartingale_norm}, $\lVert X \rVert$ is a
    sub-martingale.
    Then apply Theorem~\ref{thm:doob_ineq}. -/)
  (proofUses := ["cor:Martingale.submartingale_norm", "thm:doob_ineq"])
  (latexEnv := "corollary")]
theorem maximal_ineq_norm [SecondCountableTopology ι] [IsFiniteMeasure P]
    (hsub : Martingale X 𝓕 P) (ε : ℝ≥0) (n : ι) :
    ε • P {ω | (ε : ℝ) ≤ ⨆ i ≤ n, ‖X i ω‖} ≤
     ENNReal.ofReal (∫ ω in {ω | (ε : ℝ) ≤ ⨆ i ≤ n, ‖X i ω‖}, ‖X n ω‖ ∂P) := by
  sorry

end ProbabilityTheory
