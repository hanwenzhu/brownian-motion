/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Architect
import BrownianMotion.StochasticIntegral.DoobMeyer

/-! # Quadratic variation of local martingales

-/

open MeasureTheory Filter
open scoped ENNReal

namespace ProbabilityTheory

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [MeasurableSpace ι] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → E} {𝓕 : Filtration ι mΩ}

@[blueprint
  "lem:IsLocalMartingale.isLocalSubmartingale_sq_norm"
  (statement := /-- If $M$ is a cadlag local martingale, then $\Vert M \Vert^2$ is a cadlag local
    sub-martingale. -/)
  (latexEnv := "lemma")]
lemma IsLocalMartingale.isLocalSubmartingale_sq_norm
    (hX : IsLocalMartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    IsLocalSubmartingale (fun t ω ↦ ‖X t ω‖ ^ 2) 𝓕 P := by
  sorry

/-- The quadratic variation of a local martingale, defined as the predictable part of the Doob-Meyer
decomposition of its squared norm. -/
@[blueprint
  "def:quadraticVariation"
  (title := "Quadratic variation")
  (statement := /-- For any continuous local martingale $M$, there exists a continuous process $[M]$
    with $[M]_0 = 0$ such that $\Vert M \Vert^2 - [M]$ is a local martingale. That process is a.s.
    unique and is called the \emph{quadratic variation} of $M$.
    $[M]$ is defined as the predictable part of the Doob-Meyer decomposition of the local
    sub-martingale $\Vert M \Vert^2$~. -/)
  (uses := ["thm:local_doobMeyer", "lem:IsLocalMartingale.isLocalSubmartingale_sq_norm",
    "def:IsLocalMartingale"])]
noncomputable
def quadraticVariation (hX : IsLocalMartingale X 𝓕 P) (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    ι → Ω → ℝ :=
  have hX2 : IsLocalSubmartingale (fun t ω ↦ ‖X t ω‖ ^ 2) 𝓕 P :=
    hX.isLocalSubmartingale_sq_norm hX_cadlag
  have hX2_cadlag : ∀ ω, IsCadlag (fun t ↦ ‖X t ω‖ ^ 2) := sorry
  hX2.predictablePart (fun t ω ↦ ‖X t ω‖ ^ 2) hX2_cadlag

end ProbabilityTheory
