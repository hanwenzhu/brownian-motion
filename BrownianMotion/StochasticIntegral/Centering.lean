/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Architect
import Mathlib.Probability.Martingale.Centering

/-!
# Lemmas about the Doob decomposition

-/

open scoped NNReal ENNReal

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {X : ℕ → Ω → E} {𝓕 : Filtration ℕ mΩ}

@[blueprint
  "lem:predictablePart_add_one"
  (statement := /-- For any integer $n \ge 0$, $A_{n+1} = A_n + \mathbb{E}[X_{n+1} - X_n \mid
    \mathcal{F}_n]$. -/)
  (proof := /-- Let $n \in \mathbb{N}$. Then
    \begin{align*}
      A_{n+1}
      & = \sum_{k=0}^n \mathbb{E}[X_{k+1}-X_k \mid \mathcal{F}_k] \\
      & = \sum_{k=0}^{n-1} \mathbb{E}[X_{k+1}-X_k \mid \mathcal{F}_k] + \mathbb{E}[X_{n+1}-X_n \mid
      \mathcal{F}_n] \\
      & = A_n + \mathbb{E}[X_{n+1} - X_n \mid \mathcal{F}_n],
    \end{align*}
    which concludes the proof. -/)
  (latexEnv := "lemma")]
lemma predictablePart_add_one (n : ℕ) :
    predictablePart X 𝓕 μ (n + 1) =
      predictablePart X 𝓕 μ n + μ[X (n + 1) - X n | 𝓕 n] := by
  simp [predictablePart, Finset.sum_range_add]

variable [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

attribute [blueprint
  "def:predictable"
  (title := "Predictable process")
  (statement := /-- A process $X : T \to \Omega \to E$ is said to be predictable with respect to a
    filtration $\mathcal{F}$ if it is measurable with respect to the predictable sigma-algebra on $T
    \times \Omega$. -/)]
  MeasureTheory.IsPredictable

attribute [blueprint
  "lem:predictable_nat_iff"
  (statement := /-- Let $X : \mathbb{N} \to \Omega \to E$ be a stochastic process and let
    $\mathcal{F}$ be a filtration indexed by $\mathbb{N}$.
    Then $X$ is predictable if and only if $X_0$ is $\mathcal{F}_0$-measurable and for all $n \in
    \mathbb{N}$, $X_{n+1}$ is $\mathcal{F}_n$-measurable. -/)
  (proof := /-- Suppose first that $X$ is predictable. Straightaway, $X_0$ is
    $\mathcal{F}_0$-measurable as predictable implies progressively measurable which in turn implies
    adapted.
    
    Fixing $n$, we observe that for any $S \in \mathcal{B}(E)$,
    $$X_{n + 1}^{-1}(S) = \{\omega \mid (n + 1, \omega) \in X^{-1}(S)\} =
    \pi^{-1}(\iota^{-1}(X^{-1}(S)))$$
    where
    $$\pi : \Omega \to \{n + 1\} \times \Omega : \omega \mapsto (n + 1, \omega)$$
    and
    $$\iota : \{n + 1\} \times \Omega \to T \times \Omega : (n + 1, \omega) \mapsto (n + 1,
    \omega).$$
    As $X^{-1}(S) \in \Sigma_{\mathcal{F}}$ -- the predictable $\sigma$-algebra, it suffices to show
    that $\pi^{-1}(\iota^{-1}(\Sigma_{\mathcal{F}})) \in \mathcal{F}_n$. To this end, we again only
    need to show these for the generating sets of $\Sigma_{\mathcal{F}}$:
    \begin{itemize}
        \item For $A \in \mathcal{F}_0$, measurability is clear as $\iota^{-1}(\{0\} \times A) =
        \varnothing$.
        \item Similarly, for $m > n$ and $A \in \mathcal{F}_m$, $\iota^{-1}((m, \infty) \times A) =
        \varnothing$.
        \item For $m \le n$ and $A \in \mathcal{F}_m \le \mathcal{F}_n$ we have that
        $\pi^{-1}(\iota^{-1}((m, \infty) \times A)) = A$ which is $\mathcal{F}_n$ measurable by the
        monotonicity of the filtration.
    \end{itemize}
    
    Now, supposing $X_0$ is $\mathcal{F}_0$-measurable and $X_{n + 1}$ is
    $\mathcal{F}_n$-measurable, we will show that $X$ is predictable. Indeed, fixing $S \in
    \mathcal{B}(E)$, we have
    $$X^{-1}(S) = \bigcup_{n \in \mathbb{N}} \{n\} \times X_n^{-1}(S) = {0} \times X_0^{-1}(S) \cup
    \bigcup_{n \in \mathbb{N}} \{n + 1\} \times X_{n + 1}^{-1}(S).$$
    Thus, as $\{0\} \times X_0^{-1}(S) \in \Sigma_{\mathcal{F}}$ by construction and $\{n + 1\}
    \times X_{n + 1}^{-1}(S) = (n, n + 1] \times X_{n + 1}^{-1}(S) \in \Sigma_{\mathcal{F}}$ by
    Lemma~\ref{lem:predictable_Ioc_prod} and the fact that $X_{n + 1}^{-1}(S) \in \mathcal{F}_n$, we
    have that $X^{-1}(S) \in \Sigma_{\mathcal{F}}$ as required. -/)
  (latexEnv := "lemma")]
  MeasureTheory.isPredictable_iff_measurable_add_one

attribute [blueprint
  "def:predictablePart"
  (statement := /-- Let $X : \mathbb{N} \to \Omega \to E$ be a process indexed by $\mathbb{N}$, for
    $E$ a Banach space.
    Let $(\mathcal{F}_n)_{n\in\mathbb{N}}$ be a filtration on $\Omega$.
    The predictable part of $X$ is the process $A : \mathbb{N} \to \Omega \to E$ defined for $n \ge
    0$ by
    $$A_n = \sum_{k=0}^{n-1} \mathbb{E}[X_{k+1}-X_k \mid \mathcal{F}_k].$$ -/)]
  MeasureTheory.predictablePart

attribute [blueprint
  "lem:predictablePart_zero"
  (statement := /-- We have $A_0 = 0$. -/)
  (latexEnv := "lemma")]
  MeasureTheory.predictablePart_zero

attribute [blueprint
  "lem:adapted_predictablePart"
  (statement := /-- The predictable part $A$ is adapted to the filtration $(\mathcal{F}_{n+1})_{n
    \in \mathbb{N}}$. -/)
  (latexEnv := "lemma")]
  MeasureTheory.adapted_predictablePart

@[blueprint
  "lem:predictable_predictablePart"
  (statement := /-- The predictable part of a process is predictable. -/)
  (proof := /-- By Lemma~\ref{lem:predictable_nat_iff}, the process $A$ is predictable if $A_0$ is
    $\mathcal{F}_0$-measurable and for all integer $n$, $A_{n+1}$ is $\mathcal{F}_n$-measurable. As
    $A_0 = 0$ from Lemma~\ref{lem:predictablePart_zero}, it is $\mathcal{F}_0$-measurable.
    Lemma~\ref{lem:adapted_predictablePart} allows to conclude the proof. -/)
  (latexEnv := "lemma")]
lemma isPredictable_predictablePart : IsPredictable 𝓕 (predictablePart X 𝓕 μ) :=
  isPredictable_of_measurable_add_one (by simp [measurable_const'])
    fun n ↦ (adapted_predictablePart n).measurable

-- todo: feel free to replace `Preorder E` by something stonger if needed
attribute [blueprint
  "lem:condExp_sub_nonneg"
  (statement := /-- Let $X$ be a real-valued submartingale with respect to a filtration
    $\mathcal{F}$. Then for all $i \le j$, we have $0 \le P[M_j - M_i \mid \mathcal{F}_i]$ almost
    surely. -/)
  (latexEnv := "lemma")]
  MeasureTheory.Submartingale.condExp_sub_nonneg

@[blueprint
  "lem:nondecreasing_predictablePart_of_submartingale"
  (statement := /-- The predictable part of a real-valued submartingale is an almost surely
    nondecreasing process. -/)
  (proof := /-- Let $X$ be a submartingale and let $A$ be its predictable part. Then for all $n \geq
    0$, from Lemma~\ref{lem:condExp_sub_nonneg} we have that almost surely
    \begin{align*}
      A_{n+1} &= A_n + \mathbb{E}\left[ X_{n+1} - X_n | \mathcal{F}_n \right] \\
      &\ge A_n
      \: .
    \end{align*}
    The first equality comes from Lemma~\ref{lem:predictablePart_add_one}. As $\mathbb{N}$ is
    countable, we deduce that almost surely, for all $n \in \mathbb{N}$, $A_{n+1} \ge A_n$.
    Thus, $(A_n)_{n \in \mathbb{N}}$ is almost surely nondecreasing. -/)
  (latexEnv := "lemma")]
lemma Submartingale.monotone_predictablePart {X : ℕ → Ω → ℝ} (hX : Submartingale X 𝓕 μ) :
    ∀ᵐ ω ∂μ, Monotone (predictablePart X 𝓕 μ · ω) := by
  have := ae_all_iff.2 <| fun n : ℕ ↦ hX.condExp_sub_nonneg n.le_succ
  filter_upwards [this] with ω h
  simp only [Pi.zero_apply, Nat.succ_eq_add_one, ← ge_iff_le] at h
  refine monotone_nat_of_le_succ fun n ↦ (?_ : _ ≥ _)
  grw [predictablePart_add_one, Pi.add_apply, h n, add_zero]

end MeasureTheory
