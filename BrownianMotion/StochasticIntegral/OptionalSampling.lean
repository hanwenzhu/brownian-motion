/-
Copyright (c) 2025 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Architect
import BrownianMotion.StochasticIntegral.ApproxSeq
import BrownianMotion.Auxiliary.Adapted

open Filter TopologicalSpace Function
open scoped NNReal ENNReal Topology

namespace MeasureTheory

namespace Martingale

variable {ι Ω E : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  [OrderBot ι] [MeasurableSpace ι] [SecondCountableTopology ι] [BorelSpace ι] [MetrizableSpace ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]
  {X : ι → Ω → E} {τ σ : Ω → WithTop ι} {n : ι}

theorem condExp_stoppedValue_stopping_time_ae_eq_restrict_le_of_countable_range
    (h : Martingale X 𝓕 μ) (hRC : ∀ ω, RightContinuous (X · ω)) {i : ι} (hτ_le : ∀ x, τ x ≤ i)
    (hτ : IsStoppingTime 𝓕 τ) (hσ : IsStoppingTime 𝓕 σ)
    (hτ_countable_range : (Set.range τ).Countable) :
    μ[stoppedValue X τ|hσ.measurableSpace] =ᵐ[μ.restrict {x : Ω | τ x ≤ σ x}] stoppedValue X τ := by
  rw [ae_eq_restrict_iff_indicator_ae_eq
    (hτ.measurableSpace_le _ (hτ.measurableSet_le_stopping_time hσ))]
  refine (condExp_indicator
    (h.integrable_stoppedValue_of_countable_range τ hτ hτ_le hτ_countable_range)
    (hτ.measurableSet_stopping_time_le hσ)).symm.trans ?_
  have h_int :
      Integrable ({ω : Ω | τ ω ≤ σ ω}.indicator (stoppedValue X τ)) μ :=
    Integrable.indicator
      (h.integrable_stoppedValue_of_countable_range τ hτ hτ_le hτ_countable_range)
      <| hτ.measurableSpace_le _ (hτ.measurableSet_le_stopping_time hσ)
  have h_meas : AEStronglyMeasurable[hσ.measurableSpace]
      ({ω : Ω | τ ω ≤ σ ω}.indicator (stoppedValue X τ)) μ := by
    refine StronglyMeasurable.aestronglyMeasurable ?_
    refine StronglyMeasurable.stronglyMeasurable_of_measurableSpace_le_on
      (hτ.measurableSet_le_stopping_time hσ) ?_ ?_ ?_
    · intro t ht
      rw [Set.inter_comm _ t] at ht ⊢
      rw [hτ.measurableSet_inter_le_iff hσ, IsStoppingTime.measurableSet_min_iff hτ hσ] at ht
      exact ht.2
    · exact (measurable_stoppedValue (h.adapted.progMeasurable_of_rightContinuous hRC)
        hτ).stronglyMeasurable.indicator (hτ.measurableSet_le_stopping_time hσ)
    · intro x hx
      simp only [hx, Set.indicator_of_notMem, not_false_iff]
  exact condExp_of_aestronglyMeasurable' hσ.measurableSpace_le h_meas h_int

theorem stoppedValue_min_ae_eq_condExp_of_countable_range
    (h : Martingale X 𝓕 μ) (hRC : ∀ ω, RightContinuous (X · ω))
    (hτ : IsStoppingTime 𝓕 τ) (hσ : IsStoppingTime 𝓕 σ) {n : ι} (hτ_le : ∀ x, τ x ≤ n)
    (hτ_countable_range : (Set.range τ).Countable) (hσ_countable_range : (Set.range σ).Countable) :
    (stoppedValue X fun x ↦ min (σ x) (τ x)) =ᵐ[μ] μ[stoppedValue X τ|hσ.measurableSpace] := by
  refine
    (h.stoppedValue_ae_eq_condExp_of_le_of_countable_range hτ
      (hσ.min hτ) (fun x ↦ min_le_right _ _) hτ_le hτ_countable_range ?_).trans ?_
  · exact (hτ_countable_range.union hσ_countable_range).mono <| by grind
  refine ae_of_ae_restrict_of_ae_restrict_compl {x | σ x ≤ τ x} ?_ ?_
  · exact condExp_min_stopping_time_ae_eq_restrict_le hσ hτ
  · suffices μ[stoppedValue X τ|(hσ.min hτ).measurableSpace] =ᵐ[μ.restrict {x | τ x ≤ σ x}]
        μ[stoppedValue X τ|hσ.measurableSpace] by
      rw [ae_restrict_iff' (hσ.measurableSpace_le _ (hσ.measurableSet_le_stopping_time hτ).compl)]
      rw [Filter.EventuallyEq, ae_restrict_iff'] at this
      swap; · exact hτ.measurableSpace_le _ (hτ.measurableSet_le_stopping_time hσ)
      filter_upwards [this] with x hx hx_mem
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hx_mem
      exact hx hx_mem.le
    apply Filter.EventuallyEq.trans _ ((condExp_min_stopping_time_ae_eq_restrict_le hτ hσ).trans _)
    · exact stoppedValue X τ
    · rw [IsStoppingTime.measurableSpace_min hσ hτ,
        IsStoppingTime.measurableSpace_min hτ hσ, inf_comm]
    · have h1 : μ[stoppedValue X τ|hτ.measurableSpace] = stoppedValue X τ := by
        apply condExp_of_stronglyMeasurable hτ.measurableSpace_le
        · exact Measurable.stronglyMeasurable <|
            measurable_stoppedValue (h.adapted.progMeasurable_of_rightContinuous hRC) hτ
        · exact h.integrable_stoppedValue_of_countable_range τ hτ hτ_le hτ_countable_range
      rw [h1]
      exact (h.condExp_stoppedValue_stopping_time_ae_eq_restrict_le_of_countable_range hRC hτ_le
        hτ hσ hτ_countable_range).symm

/-- **Optional sampling theorem** for general time indices
(assuming existence of `DiscreteApproxSequence`). -/
theorem stoppedValue_min_ae_eq_condExp_of_discreteApproxSequence
    (h : Martingale X 𝓕 μ) (hRC : ∀ ω, RightContinuous (X · ω))
    (hτ : IsStoppingTime 𝓕 τ) (hσ : IsStoppingTime 𝓕 σ) {n : ι} (hτ_le : ∀ x, τ x ≤ n)
    (τn : DiscreteApproxSequence 𝓕 τ μ) (σn : DiscreteApproxSequence 𝓕 σ μ) :
    (stoppedValue X fun x ↦ min (τ x) (σ x)) =ᵐ[μ] μ[stoppedValue X τ|hσ.measurableSpace] := by
  set τn' := (discreteApproxSequence_of 𝓕 hτ_le τn).inf σn
  have hint (m : ℕ) : stoppedValue X (τn' m) =ᵐ[μ]
      μ[stoppedValue X (discreteApproxSequence_of 𝓕 hτ_le τn m) |
        (σn.isStoppingTime m).measurableSpace] := by
    refine EventuallyEq.trans (Eq.eventuallyEq ?_)
      (h.stoppedValue_min_ae_eq_condExp_of_countable_range hRC
        ((discreteApproxSequence_of 𝓕 hτ_le τn).isStoppingTime m)
        (σn.isStoppingTime m) (discreteApproxSequence_of_le hτ_le τn m)
        (DiscreteApproxSequence.countable _ _) (σn.countable m))
    congr 1; ext ω; rw [min_comm]; rfl
  have hintgbl : Integrable (stoppedValue X τ) μ :=
    integrable_stoppedValue_of_discreteApproxSequence' h hRC hτ_le τn
  refine ae_eq_condExp_of_forall_setIntegral_eq _ hintgbl ?_ ?_
    ((measurable_stoppedValue (h.adapted.progMeasurable_of_rightContinuous hRC)
      (hτ.min hσ)).mono ((hτ.min hσ).measurableSpace_mono hσ <| fun ω ↦ min_le_right _ _)
      le_rfl).aestronglyMeasurable
  · exact fun s hs _ ↦ (integrable_stoppedValue_of_discreteApproxSequence' h hRC
      (fun _ ↦ min_le_of_left_le <| hτ_le _) <| τn.inf σn).integrableOn
  rintro s hs -
  have : (fun m ↦ ∫ ω in s, stoppedValue X (τn' m) ω ∂μ) =
    fun m ↦ ∫ ω in s, stoppedValue X (discreteApproxSequence_of 𝓕 hτ_le τn m) ω ∂μ := by
    ext m
    rw [setIntegral_congr_ae (g := μ[stoppedValue X (discreteApproxSequence_of 𝓕 hτ_le τn m) |
        (σn.isStoppingTime m).measurableSpace]) (hσ.measurableSpace_le _ hs)
        (by filter_upwards [hint m] with ω hω _ using hω)]
    exact setIntegral_condExp _
      (h.integrable_stoppedValue_of_countable_range _
        (DiscreteApproxSequence.isStoppingTime _ _) (discreteApproxSequence_of_le hτ_le τn m)
        (DiscreteApproxSequence.countable _ m))
      (hσ.measurableSpace_mono (σn.isStoppingTime m) (σn.le m) _ hs)
  refine tendsto_nhds_unique (f := (fun m ↦ ∫ (ω : Ω) in s, stoppedValue X (τn' m) ω ∂μ))
    (l := atTop) ?_ (this ▸ ?_)
  · refine tendsto_setIntegral_of_L1' _ (integrable_stoppedValue_of_discreteApproxSequence' h hRC
        (fun _ ↦ min_le_of_left_le <| hτ_le _) τn') ?_
      (tendsto_eLpNorm_stoppedValue_of_discreteApproxSequence_of_le h hRC τn'
        (τn.discreteApproxSequence_of_le_inf_le_of_left σn hτ_le)) _
    rw [eventually_atTop]
    exact ⟨0, fun m _ ↦ (h.integrable_stoppedValue_of_countable_range _
      (DiscreteApproxSequence.isStoppingTime _ _)
      (τn.discreteApproxSequence_of_le_inf_le_of_left σn hτ_le m)
      (DiscreteApproxSequence.countable _ m))⟩
  · refine tendsto_setIntegral_of_L1' _ hintgbl ?_
      (tendsto_eLpNorm_stoppedValue_of_discreteApproxSequence h hRC hτ_le τn) _
    rw [eventually_atTop]
    exact ⟨0, fun m _ ↦ (h.integrable_stoppedValue_of_countable_range _
        (DiscreteApproxSequence.isStoppingTime _ _) (discreteApproxSequence_of_le hτ_le τn m)
        (DiscreteApproxSequence.countable _ m))⟩

-- TODO: change name of `stoppedValue_min_ae_eq_condExp` in mathlib and remove the prime here
/-- **Optional sampling theorem** for approximable time indices. -/
@[blueprint
  "lem:optionalSampling"
  (title := "Optional sampling (continuous time)")
  (statement := /-- Let $X$ be a right-continuous $\mathcal{F}$-martingale on an approximable time
    index. Then, for
    any stopping times $\sigma, \tau$ with $\tau$ bounded, we have that
    $X_{\sigma \wedge \tau} = P[X_{\tau} \mid \mathcal{F}_{\sigma}]$ almost surely. -/)
  (proof := /-- Fixing $A \in \mathcal{F}_{\sigma}$, we need to show that $P[X_{\tau} \mathbb{I}_A]
    = P[X_{\sigma \wedge \tau} \mathbb{I}_A]$.
    
    Let $(\tau_n), (\sigma_n)$ be discrete approximation sequences of $\tau$ and $\sigma$
    respectively.
    As $\tau_n, \sigma_n$ take values in a countable set,
    we have by the discrete time optional sampling theorem
    (Lemma~\ref{lem:optionalSampling_discrete}) that
    $$X_{\sigma_n \wedge \tau_n} = P[X_{\tau_n} \mid \mathcal{F}_{\sigma_n}]$$
    and so, as \(\mathcal{F}_{\sigma} \subseteq \mathcal{F}_{\sigma_n}\) by
    Lemma~\ref{lem:StoppingTimeGenMono},
    we have that $P[X_{\sigma_n \wedge \tau_n} \mathbb{I}_A] = P[X_{\tau_n} \mathbb{I}_A]$.
    On the other hand, by Lemma~\ref{lem:uniformIntegrable_stoppedValue_martingale}, the families
    $\{X_{\tau_n}\}$ and $\{X_{\sigma_n \wedge \tau_n}\}$ are uniformly integrable.
    Thus, as $X$ is right-continuous, $(X_{\sigma_n \wedge \tau_n}, X_{\tau_n}) \to (X_{\sigma
    \wedge \tau}, X_{\tau})$ a.s.
    We have $P[X_{\tau} \mathbb{I}_A] = P[X_{\sigma \wedge \tau} \mathbb{I}_A]$
    by Lemma~\ref{lem:tendsto_eLpNorm_stoppedValue_discreteApproxSequence} as desired. -/)
  (latexEnv := "lemma")]
theorem stoppedValue_min_ae_eq_condExp'
    [Approximable 𝓕 μ] (h : Martingale X 𝓕 μ) (hRC : ∀ ω, RightContinuous (X · ω))
    (hτ : IsStoppingTime 𝓕 τ) (hσ : IsStoppingTime 𝓕 σ) {n : ι} (hτ_le : ∀ x, τ x ≤ n) :
    (stoppedValue X fun x ↦ min (τ x) (σ x)) =ᵐ[μ] μ[stoppedValue X τ|hσ.measurableSpace] :=
  stoppedValue_min_ae_eq_condExp_of_discreteApproxSequence h hRC hτ hσ hτ_le
    (hτ.discreteApproxSequence μ) (hσ.discreteApproxSequence μ)

theorem stoppedValue_ae_eq_condExp_of_le_const'
    [Approximable 𝓕 μ] (h : Martingale X 𝓕 μ) (hRC : ∀ ω, RightContinuous (X · ω))
    (hτ : IsStoppingTime 𝓕 τ) (hτ_le : ∀ x, τ x ≤ n) :
    stoppedValue X τ =ᵐ[μ] μ[X n|hτ.measurableSpace] := by
  convert stoppedValue_min_ae_eq_condExp_of_discreteApproxSequence h hRC
    (isStoppingTime_const 𝓕 n) hτ (fun _ ↦ le_rfl) (discreteApproxSequence_const 𝓕 n)
      (hτ.discreteApproxSequence μ) using 2
  ext ω
  rw [eq_comm, min_eq_right_iff]
  exact hτ_le ω

theorem condExp_stoppedValue_ae_eq_stoppedProcess [Approximable 𝓕 μ] {n : ι}
    (h : Martingale X 𝓕 μ) (hRC : ∀ ω, RightContinuous (X · ω))
    (hτ : IsStoppingTime 𝓕 τ) (hτ_le : ∀ x, τ x ≤ n) (i : ι) :
    μ[stoppedValue X τ|𝓕 i] =ᵐ[μ] stoppedProcess X τ i := by
  simp_rw [stoppedProcess_eq_stoppedValue, min_comm]
  exact EventuallyEq.trans (Eq.eventuallyEq <| by simp)
    (stoppedValue_min_ae_eq_condExp' h hRC hτ (isStoppingTime_const 𝓕 i) hτ_le).symm

end Martingale

section subsupermartingale

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

section Nat

variable {σ τ : Ω → WithTop ℕ} {X : ℕ → Ω → E} (𝓕 : Filtration ℕ mΩ)

@[blueprint
  "lem:optionalSampling_discrete_submartingale"
  (statement := /-- Let $X$ be a discrete time submartingale with respect to the filtration
    $\mathcal{F}$ taking values in a real Banach space $E$. Assume $E$ is an order-closed partial
    order, an ordered monoid and an ordered module. Let $\tau, \sigma$ be stopping times. Then, if
    $\tau$ is bounded, we have that almost surely, $X_{\tau \wedge \sigma} \le P[X_{\tau} \mid
    \mathcal{F}_{\sigma}]$. -/)
  (proof := /-- Use Doob decomposition to write $X_n = M_n + A_n$, where $M$
    (Definition~\ref{def:martingalePart}) is a martingale
    (Lemma~\ref{lem:martingale_martingalePart}) and $A$ (Definition~\ref{def:predictablePart}) is a
    predictable process (Lemma~\ref{lem:predictable_predictablePart}). By
    Lemma~\ref{lem:optionalSampling_discrete}, we have that almost surely, $M_{\tau \wedge \sigma} =
    P[M_{\tau} \mid \mathcal{F}_{\sigma}]$. Because $A$ is predictable and $\tau \wedge \sigma \le
    \sigma$, we deduce that almost surely, $A_{\tau \wedge \sigma} = P[A_{\tau \wedge \sigma} \mid
    \mathcal{F}_\sigma]$. Moreover, by
    Lemma~\ref{lem:nondecreasing_predictablePart_of_submartingale}, we know that almost surely, $A$
    is nondecreasing. Therefore, using the fact $\tau \wedge \sigma \le \tau$, we get that
    $P[A_{\tau \wedge \sigma} \mid \mathcal{F}_\sigma] \le P[A_\tau \mid \mathcal{F}_\sigma]$. We
    deduce that almost surely,
    $$X_{\tau \wedge \sigma} = M_{\tau \wedge \sigma} + A_{\tau \wedge \sigma} \le P[M_\tau \mid
    \mathcal{F}_\sigma] + P[A_\tau \mid \mathcal{F}_\sigma] = P[X_\tau \mid \mathcal{F}_\sigma],$$
    concluding the proof. -/)
  (proofUses := ["lem:predictable_predictablePart", "lem:martingale_martingalePart",
    "lem:nondecreasing_predictablePart_of_submartingale", "lem:optionalSampling_discrete"])
  (latexEnv := "lemma")]
theorem Submartingale.stoppedValue_min_ae_le_condExp_nat [PartialOrder E] [OrderClosedTopology E]
    [IsOrderedModule ℝ E] [IsOrderedAddMonoid E]
    (hX : Submartingale X 𝓕 P) {k : ℕ} (hτk : ∀ᵐ ω ∂P, τ ω ≤ k)
    (hσ : IsStoppingTime 𝓕 σ) (hτ : IsStoppingTime 𝓕 τ) :
    stoppedValue X (τ ⊓ σ) ≤ᵐ[P] P[stoppedValue X τ|hσ.measurableSpace] := by
  sorry

@[blueprint
  "lem:optionalSampling_discrete_supermartingale"
  (statement := /-- Let $X$ be a discrete time supermartingale with respect to the filtration
    $\mathcal{F}$ taking values in a real Banach space $E$. Assume $E$ is an order-closed partial
    order, an ordered monoid and an ordered module. Let $\tau, \sigma$ be stopping times. Then, if
    $\tau$ is bounded, we have that almost surely, $X_{\tau \wedge \sigma} \ge P[X_{\tau} \mid
    \mathcal{F}_{\sigma}]$. -/)
  (proof := /-- We know that $-X$ is a submartingale, so from
    Lemma~\ref{lem:optionalSampling_discrete_submartingale} we obtain that almost surely, $-X_{\tau
    \wedge \sigma} \le P[-X_{\tau} \mid \mathcal{F}_{\sigma}]$. Multiplying by $-1$ yields the
    desired result. -/)
  (proofUses := ["lem:optionalSampling_discrete_submartingale"])
  (latexEnv := "lemma")]
theorem Supermartingale.condExp_ae_le_stoppedValue_min_nat [PartialOrder E] [OrderClosedTopology E]
    [IsOrderedModule ℝ E] [IsOrderedAddMonoid E]
    (hX : Supermartingale X 𝓕 P) {k : ℕ} (hτk : ∀ᵐ ω ∂P, τ ω ≤ k)
    (hσ : IsStoppingTime 𝓕 σ) (hτ : IsStoppingTime 𝓕 τ) :
    P[stoppedValue X τ|hσ.measurableSpace] ≤ᵐ[P] stoppedValue X (τ ⊓ σ) := by
  sorry

end Nat

variable {ι : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  [OrderBot ι] [MeasurableSpace ι] [SecondCountableTopology ι] [BorelSpace ι] [MetrizableSpace ι]
  {σ τ : Ω → WithTop ι} {X : ι → Ω → E} (𝓕 : Filtration ι mΩ)

@[blueprint
  "lem:optionalSamplingSubmartingale"
  (statement := /-- Let $X$ be a right-continuous $\mathcal{F}$-submartingale on an approximable
    time index. Then, for
    any stopping times $\sigma, \tau$ with $\tau$ bounded, we have that
    $X_{\sigma \wedge \tau} \le P[X_{\tau} \mid \mathcal{F}_{\sigma}]$ almost surely. -/)
  (proof := /-- Fixing $A \in \mathcal{F}_{\sigma}$, we need to show that $P[X_{\tau} \mathbb{I}_A]
    \le P[X_{\sigma \wedge \tau} \mathbb{I}_A]$.
    
    Let $(\tau_n), (\sigma_n)$ be discrete approximation sequences of $\tau$ and $\sigma$
    respectively.
    As $\tau_n, \sigma_n$ take values in a countable set,
    we have by the discrete time optional sampling theorem
    (Lemma~\ref{lem:optionalSampling_discrete_submartingale}) that
    $$X_{\sigma_n \wedge \tau_n} \le P[X_{\tau_n} \mid \mathcal{F}_{\sigma_n}]$$
    and so, as \(\mathcal{F}_{\sigma} \subseteq \mathcal{F}_{\sigma_n}\) by
    Lemma~\ref{lem:StoppingTimeGenMono},
    we have that $P[X_{\sigma_n \wedge \tau_n} \mathbb{I}_A] \le P[X_{\tau_n} \mathbb{I}_A]$.
    On the other hand, by Lemma~\ref{lem:uniformIntegrable_stoppedValue_submartingale}, the families
    $\{X_{\tau_n}\}$ and $\{X_{\sigma_n \wedge \tau_n}\}$ are uniformly integrable.
    Thus, as $X$ is right-continuous, $(X_{\sigma_n \wedge \tau_n}, X_{\tau_n}) \to (X_{\sigma
    \wedge \tau}, X_{\tau})$ a.s.
    We have $P[X_{\tau} \mathbb{I}_A] \le P[X_{\sigma \wedge \tau} \mathbb{I}_A]$
    by Lemma~\ref{lem:tendsto_eLpNorm_stoppedValue_discreteApproxSequence} as desired. -/)
  (proofUses := ["lem:tendsto_eLpNorm_stoppedValue_discreteApproxSequence",
    "lem:stoppingTime_approximation", "lem:optionalSampling_discrete_submartingale",
    "lem:StoppingTimeGenMono", "lem:uniformIntegrable_stoppedValue_submartingale"])
  (latexEnv := "lemma")]
theorem Submartingale.stoppedValue_min_ae_le_condExp [PartialOrder E] [OrderClosedTopology E]
    [IsOrderedModule ℝ E] [IsOrderedAddMonoid E]
    (hX1 : Submartingale X 𝓕 P) (hX2 : ∀ ω, RightContinuous (X · ω)) {k : ι}
    (hτk : ∀ᵐ ω ∂P, τ ω ≤ k) (hσ : IsStoppingTime 𝓕 σ) (hτ : IsStoppingTime 𝓕 τ) :
    stoppedValue X (τ ⊓ σ) ≤ᵐ[P] P[stoppedValue X τ|hσ.measurableSpace] := by
  sorry

end subsupermartingale

end MeasureTheory
