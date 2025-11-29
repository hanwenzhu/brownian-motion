/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Architect
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! # cadlag functions

-/

open Filter TopologicalSpace Bornology
open scoped Topology

variable {ι E : Type*} [PartialOrder ι] [TopologicalSpace ι] [TopologicalSpace E]

/-- The predicate that a function is right continuous. -/
abbrev Function.RightContinuous (f : ι → E) :=
  ∀ a, ContinuousWithinAt f (Set.Ioi a) a

/-- A function is cadlag if it is right-continuous and has left limits. -/
structure IsCadlag (f : ι → E) : Prop where
  right_continuous : Function.RightContinuous f
  left_limit : ∀ x, ∃ l, Tendsto f (𝓝[<] x) (𝓝 l)

/-- A càdlàg function maps compact sets to bounded sets. -/
@[blueprint
  "lem:isBounded_image_of_isCadlag_of_isCompact"
  (statement := /-- Assume $T$ is a linear order endowed with a topology making it first countable
    and $E$ is a pseudometric space. If $X$ is a càdlàg process then it maps compact sets to bounded
    sets. -/)
  (proof := /-- Let $K \subseteq T$ be a compact set and $\omega \in \Omega$. Assume that
    $X(\omega)(K)$ is not bounded. Then there exists a sequence $(t_n)$ in $K$ such that for all $n
    \in N$, $d(X_{t_n}(\omega), x) \ge n$, for some arbitrary $x \in E$. Because $K$ is compact,
    there is a subsequence $(t_{\phi(n)})$ that converges. Then one can extract a subsequence
    $(t_{\phi(\psi(n))})$ which either converges from below or from above. In both cases the
    sequence $(X_{t_{\phi(\psi(n))}})$ will converge, contradicting the hypotheses. -/)
  (latexEnv := "lemma")]
lemma isBounded_image_of_isCadlag_of_isCompact {E : Type*}
    [FirstCountableTopology ι] [PseudoMetricSpace E] {f : ι → E}
    (hf : IsCadlag f) {s : Set ι} (hs : IsCompact s) :
    IsBounded (f '' s) := by
  sorry
