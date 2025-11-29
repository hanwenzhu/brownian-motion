/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Architect
import BrownianMotion.StochasticIntegral.Locally
import BrownianMotion.StochasticIntegral.OptionalSampling
import Mathlib.Probability.Martingale.Basic
import BrownianMotion.Auxiliary.Martingale

/-! # Local (sub)martingales

-/

open MeasureTheory Filter TopologicalSpace Function
open scoped ENNReal

namespace ProbabilityTheory

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → E} {𝓕 : Filtration ι mΩ}

/-- A stochastic process is a local martingale if it satisfies the martingale property locally. -/
@[blueprint
  "def:IsLocalMartingale"
  (title := "Local martingale")
  (statement := /-- We say a stochastic process $(M_t)_{t \in T}$ is a local martingale if it is
    locally a cadlag martingale in the sense of
    Definition~\ref{def:locally}. That is, there exists a localizing sequence $(\tau_n)_{n \in
    \mathbb{N}}$ such that for all $n \in \mathbb{N}$, the process $M^{\tau_n}\mathbb{I}_{\tau_n >
    0}$ is a cadlag martingale. -/)]
def IsLocalMartingale (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω := by volume_tac) :
    Prop :=
  Locally (fun X ↦ Martingale X 𝓕 P ∧ ∀ ω, IsCadlag (X · ω)) 𝓕 X P

/-- A stochastic process is a local submartingale if it satisfies the submartingale property
locally. -/
@[blueprint
  "def:IsLocalSubmartingale"
  (statement := /-- A stochastic process is a local submartingale if it is locally a cadlag
    submartingale in the sense of Definition~\ref{def:locally}.
    That is, there exists a localizing sequence $(\tau_n)_{n \in \mathbb{N}}$ such that for all $n
    \in \mathbb{N}$, the process $M^{\tau_n}\mathbb{I}_{\tau_n > 0}$ is a cadlag submartingale. -/)]
def IsLocalSubmartingale [LE E] (X : ι → Ω → E) (𝓕 : Filtration ι mΩ)
    (P : Measure Ω := by volume_tac) : Prop :=
  Locally (fun X ↦ Submartingale X 𝓕 P ∧ ∀ ω, IsCadlag (X · ω)) 𝓕 X P

@[blueprint
  "lem:Martingale.IsLocalMartingale"
  (statement := /-- Every cadlag martingale is a local martingale. -/)
  (proof := /-- This follows from Lemma \ref{lem:implies_locally}. -/)
  (latexEnv := "lemma")]
lemma Martingale.IsLocalMartingale (hX : Martingale X 𝓕 P) (hC : ∀ ω, IsCadlag (X · ω)) :
    IsLocalMartingale X 𝓕 P :=
  locally_of_prop ⟨hX, hC⟩

lemma Submartingale.IsLocalSubmartingale [LE E]
    (hX : Submartingale X 𝓕 P) (hC : ∀ ω, IsCadlag (X · ω)) :
    IsLocalSubmartingale X 𝓕 P :=
  locally_of_prop ⟨hX, hC⟩

variable [MeasurableSpace ι] [SecondCountableTopology ι] [BorelSpace ι] [PseudoMetrizableSpace ι]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [IsFiniteMeasure P]
  [Approximable 𝓕 P]

/-- Martingales are a stable class. -/
@[blueprint
  "lem:stable_IsMartingale"
  (statement := /-- The class of cadlag martingales is stable. That is, if $M$ is a cadlag
    martingale and $\tau$ is a stopping time, then the stopped process cadlag
    $M^{\tau}\mathbb{I}_{\tau > 0}$ is also a martingale. -/)
  (proof := /-- Clearly, the stopped process $M^{\tau}\mathbb{I}_{\tau > 0}$ is cadlag and it
    remains to show that it is a martingale.
    
    Fixing $s \le t \in T$, as $\{\tau > 0\} \in \mathcal{F}_0 \subseteq \mathcal{F}_s$, we have
    $$P[M^{\tau}_t \mathbb{I}_{\tau > 0} \mid \mathcal{F}_s] = \mathbb{I}_{\tau > 0}P[M_{\tau \wedge
    t} \mid \mathcal{F}_{s}].$$
    Thus, as $\tau \wedge t$ is a bounded stopping time, we have by the optional stopping theorem
    (Lemma~\ref{lem:optionalSampling}) that $P[M_{\tau \wedge t} \mid \mathcal{F}_{s}] = M_{(\tau
    \wedge t) \wedge s} = M_{\tau \wedge s}$
    and so, $P[M^{\tau}_t \mathbb{I}_{\tau > 0} \mid \mathcal{F}_s] = M^{\tau}_s \mathbb{I}_{\tau >
    0}$ as required. -/)
  (latexEnv := "lemma")]
lemma isStable_martingale :
    IsStable 𝓕 (fun (X : ι → Ω → E) ↦ Martingale X 𝓕 P ∧ ∀ ω, IsCadlag (X · ω)) := by
  intro X ⟨hX, hC⟩ τ hτ
  refine ⟨⟨ProgMeasurable.adapted_stoppedProcess ?_ hτ, fun i j hij ↦ ?_⟩,
    isStable_isCadlag X hC τ hτ⟩
  · refine Adapted.progMeasurable_of_rightContinuous
      (fun i ↦ (hX.adapted i).indicator <| 𝓕.mono bot_le _ <| hτ.measurableSet_gt _) (fun ω ↦ ?_)
    by_cases hω : ω ∈ {ω | ⊥ < τ ω}
    · simp_rw [Set.indicator_of_mem hω]
      exact (hC ω).right_continuous
    · simp [Set.indicator_of_notMem hω, RightContinuous, continuousWithinAt_const]
  · have : Martingale (fun i ↦ {ω | ⊥ < τ ω}.indicator (X i)) 𝓕 P :=
      hX.indicator (hτ.measurableSet_gt _)
    conv_rhs => rw [← stoppedProcess_min_eq_stoppedProcess _ τ hij]
    refine EventuallyEq.trans ?_ (Martingale.condExp_stoppedValue_ae_eq_stoppedProcess
      (μ := P) (n := j) this (fun ω ↦ ?_) ((isStoppingTime_const 𝓕 j).min hτ)
      (fun ω ↦ min_le_left _ _) i)
    · rw [stoppedProcess_eq_stoppedValue]
    · by_cases hω : ω ∈ {ω | ⊥ < τ ω}
      · simp_rw [Set.indicator_of_mem hω]
        exact (hC ω).right_continuous
      · simp [Set.indicator_of_notMem hω, RightContinuous, continuousWithinAt_const]

/-- Submartingales are a stable class. -/
@[blueprint
  "lem:stable_IsSubmartingale"
  (statement := /-- The class of cadlag submartingales is stable. That is, if $M$ is a cadlag
    submartingale and $\tau$ is a stopping time, then the stopped process $M^{\tau}\mathbb{I}_{\tau
    > 0}$ is also a cadlag submartingale. -/)
  (proofUses := ["lem:optionalSampling"])
  (latexEnv := "lemma")]
lemma isStable_submartingale :
    IsStable 𝓕 (fun (X : ι → Ω → ℝ) ↦ Submartingale X 𝓕 P ∧ ∀ ω, IsCadlag (X · ω)) := by
  sorry

end ProbabilityTheory
