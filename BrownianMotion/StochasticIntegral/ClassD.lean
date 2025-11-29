/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Architect
import BrownianMotion.Auxiliary.Martingale
import BrownianMotion.StochasticIntegral.ApproxSeq
import BrownianMotion.StochasticIntegral.Locally
import BrownianMotion.Auxiliary.Adapted
import BrownianMotion.StochasticIntegral.OptionalSampling
import Mathlib.Probability.Process.HittingTime

/-! # Locally integrable, class D, class DL

-/

open MeasureTheory Filter Function TopologicalSpace
open scoped ENNReal

namespace ProbabilityTheory

variable {ι Ω E : Type*} [NormedAddCommGroup E] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ι → Ω → E}

/-- The condition that the running supremum process `(t, ω) ↦ sup_{s ≤ t} ‖X s ω‖` is strongly
measurable as a function on the product. -/
def HasStronglyMeasurableSupProcess [LinearOrder ι] [MeasurableSpace ι] (X : ι → Ω → E) : Prop :=
  (StronglyMeasurable (fun (tω : ι × Ω) ↦ ⨆ s ≤ tω.1, ‖X s tω.2‖ₑ))

/-- A stochastic process has integrable supremum if the function `(t, ω) ↦ sup_{s ≤ t} ‖X s ω‖`
is strongly measurable and if for all `t`, the random variable `ω ↦ sup_{s ≤ t} ‖X s ω‖`
is integrable. -/
def HasIntegrableSup [LinearOrder ι] [MeasurableSpace ι] (X : ι → Ω → E)
    (P : Measure Ω := by volume_tac) : Prop :=
  (HasStronglyMeasurableSupProcess (mΩ:= mΩ) X) ∧
     (∀ t, Integrable (fun ω ↦ ⨆ s ≤ t, ‖X s ω‖ₑ) P)

/-- A stochastic process has locally integrable supremum if it satisfies locally the property that
for all `t`, the random variable `ω ↦ sup_{s ≤ t} ‖X s ω‖` is integrable. -/
@[blueprint
  "def:locallyIntegrableSup"
  (statement := /-- We say that a stochastic process is integrable if for all $t$, $X_t$ is
    integrable.
    A process has locally integrable supremum if $(\sup_{s \le t} \Vert X_s \Vert)_t$ is locally
    integrable. -/)]
def HasLocallyIntegrableSup [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    [MeasurableSpace ι] (X : ι → Ω → E) (𝓕 : Filtration ι mΩ)
    (P : Measure Ω := by volume_tac) : Prop :=
  Locally (HasIntegrableSup · P) 𝓕 X P

section Defs

variable [Preorder ι] [Nonempty ι] [MeasurableSpace ι]

/-- A stochastic process $(X_t)$ is of class D (or in the Doob-Meyer class) if it is adapted
and the set $\{X_\tau \mid \tau \text{ is a finite stopping time}\}$ is uniformly integrable. -/
@[blueprint
  "def:classD"
  (title := "Doob-Meyer class, class D")
  (statement := /-- A stochastic process $(X_t)$ is of class D (or in the Doob-Meyer class) if it is
    progressively measurable and the set $\{X_\tau \mid \tau \text{ is a finite stopping time}\}$ is
    uniformly integrable. -/)]
structure ClassD (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) :
    Prop where
  progMeasurable : ProgMeasurable 𝓕 X
  uniformIntegrable : UniformIntegrable
    (fun (τ : {T : Ω → WithTop ι | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≠ ⊤}) ↦ stoppedValue X τ.1) 1 P

/-- A stochastic process $(X_t)$ is of class DL if it is adapted and for all $t$, the set
$\{X_\tau \mid \tau \text{ is a stopping time with } \tau \le t\}$ is uniformly integrable. -/
@[blueprint
  "def:classDL"
  (title := "Class DL")
  (statement := /-- A stochastic process $(X_t)$ is of class DL if it is progressively measurable
    and for all $t \ge 0$, the set $\{X_\tau \mid \tau \text{ is a stopping time with } \tau \le
    t\}$ is uniformly integrable. -/)]
structure ClassDL (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) :
    Prop where
  progMeasurable : ProgMeasurable 𝓕 X
  uniformIntegrable (t : ι) : UniformIntegrable
    (fun (τ : {T : Ω → WithTop ι | IsStoppingTime 𝓕 T ∧ ∀ ω, T ω ≤ t}) ↦ stoppedValue X τ.1) 1 P

@[blueprint
  "lem:classDLOfClassD"
  (statement := /-- A stochastic process of class D is of class DL. -/)
  (proof := /-- This follows from the definitions and Lemma~\ref{lem:uniformIntegrableComp}. -/)
  (latexEnv := "lemma")]
lemma ClassD.classDL {𝓕 : Filtration ι mΩ} {X : ι → Ω → E} (hX : ClassD X 𝓕 P) :
    ClassDL X 𝓕 P := by
  let f (t : ι) : {T | IsStoppingTime 𝓕 T ∧ ∀ (ω : Ω), T ω ≤ t} →
      {T | IsStoppingTime 𝓕 T ∧ ∀ (ω : Ω), T ω ≠ ⊤} :=
    fun τ => ⟨τ, τ.2.1, fun ω => ne_of_lt
      (lt_of_le_of_lt (τ.2.2 ω) (WithTop.coe_lt_top t))⟩
  exact ⟨hX.1, fun t => hX.2.comp (f t)⟩

end Defs

section PartialOrder

variable [NormedSpace ℝ E] [CompleteSpace E] [LinearOrder ι] {𝓕 : Filtration ι mΩ}

section RightContinuous

variable [TopologicalSpace ι] [OrderTopology ι] [OrderBot ι] [MeasurableSpace ι]
  [SecondCountableTopology ι] [BorelSpace ι] [MetrizableSpace ι]

section Order

variable [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
  [IsFiniteMeasure P]

@[blueprint
  "lem:Submartingale.classDL"
  (statement := /-- Every nonnegative right-continuous submartingale is of class DL. -/)
  (proof := /-- Let $t \in T$ and $\tau \le t$ be a stopping time. By
    Lemma~\ref{lem:optionalSamplingSubmartingale} and nonnegativity we get that $0 \le X_\tau \le
    P[X_t \mid X_\tau]$. As $X$ is a submartingale, $X_t$ is integrable, thus $\{X_t\}$ is uniformly
    integrable, and we can conclude from Lemma~\ref{lem:uniformIntegrableDominated} and
    Lemma~\ref{lem:condExpUI}. -/)
  (latexEnv := "lemma")]
lemma _root_.MeasureTheory.Submartingale.classDL (hX1 : Submartingale X 𝓕 P)
    (hX2 : ∀ ω, RightContinuous (X · ω)) (hX3 : 0 ≤ X) :
    ClassDL X 𝓕 P := by
  refine ⟨Adapted.progMeasurable_of_rightContinuous hX1.1 hX2, fun t => ?_⟩
  have := (hX1.2.2 t).uniformIntegrable_condExp' (fun T :
    {T | IsStoppingTime 𝓕 T ∧ ∀ (ω : Ω), T ω ≤ t} => IsStoppingTime.measurableSpace_le T.2.1)
  refine uniformIntegrable_of_dominated le_rfl this (fun T => ?_) (fun T => ⟨T, ?_⟩)
  · exact ((stronglyMeasurable_stoppedValue_of_le (Adapted.progMeasurable_of_rightContinuous
      hX1.1 hX2) T.2.1 T.2.2).mono (𝓕.le' t)).aestronglyMeasurable
  · have : stoppedValue X T.1 ≤ᵐ[P] P[stoppedValue X (fun ω => t)|T.2.1.measurableSpace] := by
      suffices lem : stoppedValue X ((fun ω => t) ⊓ T.1) ≤ᵐ[P]
        P[stoppedValue X (fun ω => t)|T.2.1.measurableSpace] from by
        have : T.1 ⊓ (fun ω => t) = T.1 := by simpa [inf_eq_left] using T.2.2
        simpa [inf_comm, this] using lem
      exact hX1.stoppedValue_min_ae_le_condExp 𝓕 hX2
        (Eventually.of_forall (fun ω => le_rfl)) T.2.1 (isStoppingTime_const 𝓕 t)
    simp only [stoppedValue_const] at this
    filter_upwards [this] with ω hω
    have p1 : 0 ≤ stoppedValue X T.1 ω := by simpa [stoppedValue] using (hX3 (T.1 ω).untopA ω)
    have p2 := abs_of_nonneg (le_trans p1 hω)
    rw [← abs_of_nonneg p1, ← p2] at hω
    exact norm_le_norm_of_abs_le_abs hω

@[blueprint
  "lem:Submartingale.classD_iff_uniformIntegrable"
  (statement := /-- A nonnegative càdlàg submartingale is of class D if and only if it is uniformly
    integrable. -/)
  (proof := /-- Assume that $X$ is uniformly integrable. We know from
    Lemma~\ref{lem:Submartingale.classDL} that $X$ is of class DL. Moreover, for any finite stopping
    time $\tau$, We have that $X_\tau = \lim_{n \to +\infty} X_{\tau \land n}$. Thanks to
    Lemma~\ref{lem:uniformIntegrable_of_tendstoInMeasure}, we deduce that $X$ is of class D.
    
    Conversely, if $X$ is of class D, then applying Lemma~\ref{lem:uniformIntegrableComp} using
    constant stopping times will yield uniform integrability. -/)
  (proofUses := ["lem:uniformIntegrable_of_tendstoInMeasure", "lem:uniformIntegrableComp",
    "lem:Submartingale.classDL"])
  (latexEnv := "lemma")]
lemma _root_.MeasureTheory.Submartingale.classD_iff_uniformIntegrable
    [IsFiniteMeasure P] (hX1 : Submartingale X 𝓕 P)
    (hX2 : ∀ ω, RightContinuous (X · ω)) (hX3 : 0 ≤ X) :
    ClassD X 𝓕 P ↔ UniformIntegrable X 1 P := sorry

end Order

@[blueprint
  "lem:Martingale.classDL"
  (statement := /-- Every càdlàg martingale is of class DL. -/)
  (proof := /-- Let $X$ be càdlàg martingale. By
    Lemma~\ref{lem:Martingale.submartingale_convex_comp}, $(|X_t|)_{t \in T}$ is a nonnegative
    càdlàg submartingale, and the result follows from Lemma~\ref{lem:Submartingale.classDL} along
    with Lemma~\ref{lem:uniformIntegrableIffNorm}. -/)
  (proofUses := ["lem:uniformIntegrableIffNorm", "lem:Martingale.submartingale_convex_comp",
    "lem:Submartingale.classDL"])
  (latexEnv := "lemma")]
lemma _root_.MeasureTheory.Martingale.classDL (hX1 : Martingale X 𝓕 P)
    (hX2 : ∀ ω, RightContinuous (X · ω)) :
    ClassDL X 𝓕 P := sorry

@[blueprint
  "lem:Martingale.classD_iff_uniformIntegrable"
  (statement := /-- A càdlàg martingale is of class D if and only if it is uniformly integrable. -/)
  (proof := /-- Applying Lemma~\ref{lem:uniformIntegrableIffNorm}, this follows from
    Lemma~\ref{lem:Submartingale.classDL} along with
    Lemma~\ref{lem:Submartingale.classD_iff_uniformIntegrable}. -/)
  (proofUses := ["lem:Submartingale.classD_iff_uniformIntegrable",
    "lem:uniformIntegrableIffNorm", "lem:Submartingale.classDL"])
  (latexEnv := "lemma")]
lemma _root_.MeasureTheory.Martingale.classD_iff_uniformIntegrable (hX1 : Martingale X 𝓕 P)
    (hX2 : ∀ ω, RightContinuous (X · ω)) :
    ClassD X 𝓕 P ↔ UniformIntegrable X 1 P := sorry

end RightContinuous

end PartialOrder

section LinearOrder

variable [LinearOrder ι] {𝓕 : Filtration ι mΩ}

lemma isStable_hasStronglyMeasurableSupProcess [OrderBot ι] [TopologicalSpace ι]
    [SecondCountableTopology ι] [OrderTopology ι] [MeasurableSpace ι] [BorelSpace ι] :
    IsStable 𝓕 (HasStronglyMeasurableSupProcess (E := E) (mΩ := mΩ) · ) := by
  intro X hX τ hτ
  unfold HasStronglyMeasurableSupProcess at hX ⊢
  let M : ι × Ω → ι × Ω := fun p ↦ ((min ↑p.1 (τ p.2)).untopA, p.2)
  have hM : Measurable M := (WithTop.measurable_coe.comp measurable_fst).min
      (hτ.measurable'.comp measurable_snd) |>.untopA.prodMk measurable_snd
  have key_eq : (fun p : ι × Ω ↦ ⨆ s ≤ p.1, ‖stoppedProcess
          (fun i ↦ {ω | ⊥ < τ ω}.indicator (X i)) τ s p.2‖ₑ) =
      {p | ⊥ < τ p.2}.indicator (fun p ↦ ⨆ s ≤ (M p).1, ‖X s (M p).2‖ₑ) := by
    ext ⟨t, ω⟩; simp only [M, stoppedProcess, Set.indicator_apply, Set.mem_setOf_eq]
    split_ifs with h
    · apply le_antisymm
      · apply iSup₂_le
        intro s hst
        apply le_iSup₂_of_le (min ↑s (τ ω)).untopA ?_
        · simp only [le_refl]
        · rw [WithTop.le_untopA_iff, WithTop.untopA_eq_untop, WithTop.coe_untop]
          · exact min_le_min (WithTop.coe_le_coe.mpr hst) le_rfl
          all_goals simp
      · apply iSup₂_le
        intro u hu
        rw [WithTop.le_untopA_iff (by simp)] at hu
        · apply le_iSup₂_of_le (α := ℝ≥0∞) u ?_
          · rw [min_eq_left]
            · exact le_rfl
            · exact le_trans hu (min_le_right _ _)
          · exact WithTop.coe_le_coe.mp (le_trans hu (min_le_left _ _))
    · simp
  rw [key_eq]
  exact StronglyMeasurable.indicator (hX.comp_measurable hM)
    (measurableSet_lt measurable_const (hτ.measurable'.comp measurable_snd))


lemma isStable_hasIntegrableSup [OrderBot ι] [TopologicalSpace ι] [SecondCountableTopology ι]
    [OrderTopology ι] [MeasurableSpace ι] [BorelSpace ι] :
    IsStable 𝓕 (HasIntegrableSup (E := E) · P) := by
  refine (fun X hX τ hτ ↦ ⟨isStable_hasStronglyMeasurableSupProcess X hX.1 τ hτ, ?_⟩)
  refine fun t ↦ ⟨ (isStable_hasStronglyMeasurableSupProcess X hX.1 τ hτ).comp_measurable
      (measurable_const.prodMk measurable_id) |>.aestronglyMeasurable, ?_ ⟩
  have h_bound := (hX.2 t).hasFiniteIntegral
  simp_rw  [hasFiniteIntegral_def, enorm_eq_self] at h_bound ⊢
  refine lt_of_le_of_lt (lintegral_mono fun ω ↦ ?_) h_bound
  apply iSup₂_le
  intro s hs
  simp only [stoppedProcess, Set.indicator_apply, Set.mem_setOf_eq]
  split_ifs with h_bot
  · refine le_iSup₂_of_le (min ↑s (τ ω)).untopA ?_ (le_refl _)
    · rw [WithTop.untopA_le_iff]
      · exact le_trans (min_le_left _ _) (WithTop.coe_le_coe.mpr hs)
      · exact ne_of_lt (lt_of_le_of_lt (min_le_left _ _) (WithTop.coe_lt_top s))
  · simp only [enorm_zero, zero_le]

@[blueprint
  "lem:isStable_hasLocallyIntegrableSup"
  (statement := /-- The class of process with locally integrable supremum is stable. -/)
  (proof := /-- Let $X$ be a process with locally integrable supremum and $\tau$ be a stopping time.
    Let $t \in T$. Then $(X^\tau)^*_t = \sup_{s \le t} \|X_{\tau \land s}\| \le \sup_{s \le t}
    \|X_s\| = X^*_t$, and as $X^*_t$ is integrable, so is $(X^\tau)^*_t$. Thus $(X^\tau
    \mathbb{I}_{\tau > 0})^*_t$ is integrable, concluding the proof. -/)
  (latexEnv := "lemma")]
lemma isStable_hasLocallyIntegrableSup [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    [MeasurableSpace ι] [SecondCountableTopology ι] [BorelSpace ι] :
    IsStable 𝓕 (HasLocallyIntegrableSup (E := E) · 𝓕 P) :=
  IsStable.isStable_locally isStable_hasIntegrableSup

@[blueprint
  "lem:isStable_classD"
  (statement := /-- The class D is stable. -/)
  (proof := /-- Let $X$ be a process of class D and $\tau$ be a stopping time. For any finite
    stopping time $\sigma$, we have that $X_\sigma^\tau = X_{\sigma \land \tau}$. Because $\sigma
    \land \tau$ is finite and $X$ is of class D, we deduce from
    Lemma~\ref{lem:uniformIntegrableComp} that $\{X_{\sigma \land \tau} \mid \sigma \text{ is a
    finite stopping time}\}$ is uniformly integrable, and thus that $\{X^\tau_\sigma \mid \sigma
    \text{ is a finite stopping time}\}$ is uniformly integrable. Using
    Lemma~\ref{lem:uniformIntegrableDominated}, we obtain that $\{X^\tau_\sigma \mathbb{I}_{\tau >
    0} \mid \sigma \text{ is a finite stopping time}\}$ is uniformly integrable, which concludes the
    proof. -/)
  (proofUses := ["lem:uniformIntegrableDominated", "lem:uniformIntegrableComp"])
  (latexEnv := "lemma")]
lemma isStable_classD [OrderBot ι] [MeasurableSpace ι] : IsStable 𝓕 (ClassD (E := E) · 𝓕 P) := by
  sorry

@[blueprint
  "lem:isStable_classDL"
  (statement := /-- The class DL is stable. -/)
  (proof := /-- Let $X$ be a process of class DL, $\tau$ be a stopping time. Let $t \in T$. For any
    stopping time $\sigma \le t$, we have that $X_\sigma^\tau = X_{\sigma \land \tau}$. Because
    $\sigma \land \tau$ is bounded by $t$ and $X$ is of class DL, we deduce from
    Lemma~\ref{lem:uniformIntegrableComp} that $\{X_{\sigma \land \tau} \mid \sigma \text{ is a
    stopping time with } \sigma \le t\}$ is uniformly integrable, and thus that $\{X^\tau_\sigma
    \mid \sigma \text{ is a stopping time with } \sigma \le t\}$ is uniformly integrable. Using
    Lemma~\ref{lem:uniformIntegrableDominated}, we obtain that $\{X^\tau_\sigma \mathbb{I}_{\tau >
    0} \mid \sigma \text{ is a stopping time with } \sigma \le t\}$ is uniformly integrable, which
    concludes the proof. -/)
  (proofUses := ["lem:uniformIntegrableDominated", "lem:uniformIntegrableComp"])
  (latexEnv := "lemma")]
lemma isStable_classDL [OrderBot ι] [MeasurableSpace ι] : IsStable 𝓕 (ClassDL (E := E) · 𝓕 P) := by
  sorry

@[blueprint
  "lem:Integrable.classDL"
  (statement := /-- Let $X$ be a stochastic process such that for all $t \in T$, $X^*_t := \sup_{s
    \le t} \|X_t\|$ is integrable. Then $X$ is of class DL. -/)
  (proof := /-- Let $t \in T$. For every stopping time $\tau$ with $\tau \le t$, we have $\|X_\tau\|
    \le X^*_t$. Because by hypothesis $X^*_t$ is integrable, we deduce from
    Lemma~\ref{lem:uniformIntegrableDominatedSingleton} that $\{X_\tau \mid \tau \text{ is a
    stopping time with } \tau \le t\}$ is uniformly integrable. This proves that $X$ is of class DL.
    -/)
  (proofUses := ["lem:uniformIntegrableDominatedSingleton"])
  (latexEnv := "lemma")]
lemma _root_.MeasureTheory.Integrable.classDL [Nonempty ι] [MeasurableSpace ι]
    (hX : ∀ t, Integrable (fun ω ↦ ⨆ s ≤ t, ‖X t ω‖ₑ) P) :
    ClassDL X 𝓕 P := by
  sorry

@[blueprint
  "lem:HasLocallyIntegrableSup.locally_classDL"
  (statement := /-- Assume that the filtration is right-continuous. Let $X$ be a stochastic process
    with locally integrable supremum. Then $X$ is locally of class DL. -/)
  (proof := /-- Combine Lemma~\ref{lem:Integrable.classDL} and Lemma~\ref{lem:locally_mono}. -/)
  (proofUses := ["lem:locally_mono", "lem:Integrable.classDL"])
  (latexEnv := "lemma")]
lemma HasLocallyIntegrableSup.locally_classDL [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    [MeasurableSpace ι]
    (hX1 : HasLocallyIntegrableSup X 𝓕 P) (hX2 : Adapted 𝓕 X) (h𝓕 : 𝓕.IsRightContinuous) :
    Locally (ClassDL · 𝓕 P) 𝓕 X P := by
  sorry

@[blueprint
  "lem:ClassDL.locally_classD"
  (statement := /-- If $X$ is of class DL then it is locally of class D. -/)
  (proof := /-- Take $\tau_n := n$. Then
    \begin{align*}
      \{X^{\tau_n}_\sigma \mid \sigma \text{ is a finite stopping time}\} & = \{X_{\sigma \land n}
      \mid \sigma \text{ is a finite stopping time}\} \\
      & \subseteq \{X_\sigma \mid \sigma \text{ is a stopping time with } \sigma \le n\}.
    \end{align*}
    Because $X$ is of class DL, that last set is uniformly integrable, thus
    $$\{X^{\tau_n}_\sigma \mid \sigma \text{ is a finite stopping time}\}$$
    is uniformly integrable thanks to Lemma~\ref{lem:uniformIntegrableComp}.
    Lemma~\ref{lem:uniformIntegrableDominated} allows to conclude that
    $$\{X^{\tau_n}_\sigma \mathbb{I}_{\tau_n > 0} \mid \sigma \text{ is a finite stopping time}\}$$
    is uniformly integrable, thus $X^{\tau_n} \mathbb{I}_{\tau_n > 0}$ is of class D. Obviously
    $\tau_n \rightarrow +\infty$ as $n$ goes to infinity, so $X$ is locally of class D. -/)
  (proofUses := ["lem:uniformIntegrableDominated", "lem:uniformIntegrableComp"])
  (latexEnv := "lemma")]
lemma ClassDL.locally_classD [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι] [MeasurableSpace ι]
    (hX : ClassDL X 𝓕 P) :
    Locally (ClassD · 𝓕 P) 𝓕 X P := by
  sorry

@[blueprint
  "lem:locally_classD_of_locally_classDL"
  (statement := /-- If the filtration is right-continuous and $X$ is locally of class DL then it is
    locally of class D. -/)
  (proof := /-- Apply Lemma~\ref{lem:local_induction} using Lemma~\ref{lem:ClassDL.locally_classD}
    and Lemma~\ref{lem:isStable_classD}. -/)
  (proofUses := ["lem:isStable_classD", "lem:local_induction", "lem:ClassDL.locally_classD"])
  (latexEnv := "lemma")]
lemma locally_classD_of_locally_classDL [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [MeasurableSpace ι]
    (hX : Locally (ClassDL · 𝓕 P) 𝓕 X P) (h𝓕 : 𝓕.IsRightContinuous) :
    Locally (ClassD · 𝓕 P) 𝓕 X P := by
  sorry

-- TODO: The assumptions should be refined with those of Début theorem.
@[blueprint
  "lem:isLocalizingSequence_hittingAfter_Ici"
  (statement := /-- Assume $T$ has a bottom element $\bot$ and that its closed intervals are
    compact. If $X$ is a real-valued càdlàg and adapted process, and if the filtration is
    right-continuous, then the sequence $\tau_n := \inf \{t | X_t \ge n\}$ is a localizing sequence.
    -/)
  (proof := /-- By Corollary~\ref{cor:isStoppingTime_leastGE_of_rightContinuous}, each $\tau_n$ is a
    stopping time. Moreover, for all $n \in \mathbb{N}$, $X_t \ge n+1 \implies X_t \ge n$, thus
    $\tau_n \le \tau_{n+1}$. Finally, for every $\omega \in \Omega$ and $t_0 \in T$ there exists $N
    \in \mathbb{N}$ such that for all $s \le t_0$, $X_s \le N$ thanks to
    Lemma~\ref{lem:isBounded_image_of_cadlag_of_isCompact}. Thus for all $n \ge N$, $\tau_n(\omega)
    \ge t_0$, proving that $\tau_n$ tends to infinity as n goes to infinity. -/)
  (latexEnv := "lemma")]
lemma isLocalizingSequence_hittingAfter_Ici {ι : Type*} [PartialOrder ι] [TopologicalSpace ι]
    [OrderTopology ι] [FirstCountableTopology ι] [InfSet ι] [Bot ι] [CompactIccSpace ι]
    (𝓕 : Filtration ι mΩ) (τ : ℕ → Ω → WithTop ι) {X : ι → Ω → ℝ} (hX1 : Adapted 𝓕 X)
    (hX2 : ∀ ω, RightContinuous (X · ω)) (h𝓕 : 𝓕.IsRightContinuous) :
    IsLocalizingSequence 𝓕 (fun n ↦ hittingAfter X (Set.Ici n) ⊥) P := sorry

@[blueprint
  "lem:sup_stoppedProcess_le"
  (statement := /-- For $Y$ a stochastic process, let $Y^*_t = \sup_{s \le t} \Vert Y_s \Vert$.
    Let $X$ be a stochastic process and let $\tau = \inf \{t \mid \Vert X_t \Vert \ge n\}$ for some
    $n \in \mathbb{R}$.
    Then
    \begin{align*}
      (X^{\tau})^*_t
      \le n + \mathbb{1}_{\tau \le t} \Vert X_{\tau} \Vert
      \: .
    \end{align*} -/)
  (proof := /-- If $\tau > t$, then for all $s \le t$, $\|X_s\| \le n$, and thus $(X^\tau)^*_t =
    \sup_{s \le t} \|X_{\tau \land s}\| \le n = n + \mathbb{1}_{\tau \le t} \|X_{\tau}\|$. Otherwise
    $(X^\tau)^*_t = \sup_{s \le \tau} \|X_s\|$. For $s < \tau$, $\|X_s\| \le n$, and $\|X_\tau\| \le
    \|X_\tau\|$ so $\sup_{s \le \tau} \|X_s\| \le n \lor \|X_\tau\| \le n + \|X_\tau\| = n +
    \mathbb{I}_{\tau \le t} \|X_\tau\|$. -/)
  (latexEnv := "lemma")]
lemma sup_stoppedProcess_hittingAfter_Ici_le {E : Type*} [NormedAddCommGroup E] [InfSet ι] [Bot ι]
    {X : ι → Ω → E} (t : ι) (K : ℝ) (ω : Ω) :
    ⨆ s ≤ t, ‖stoppedProcess X (hittingAfter (fun t ω ↦ ‖X t ω‖) (Set.Ici K) ⊥) s ω‖ ≤
    K + Set.indicator {ω | hittingAfter (fun t ω ↦ ‖X t ω‖) (Set.Ici K) ⊥ ω ≤ t}
      (fun ω ↦ ‖stoppedValue X (hittingAfter (fun t ω ↦ ‖X t ω‖) (Set.Ici K) ⊥) ω‖) ω := sorry

@[blueprint
  "lem:ClassDL.hasLocallyIntegrableSup"
  (statement := /-- Assume $T$ has a bottom element $\bot$ and that its closed intervals are
    compact. If $X$ is a càdlàg and adapted process, and if the filtration is right-continuous, then
    any process of class DL has locally integrable supremum. -/)
  (proof := /-- Set $\tau_n := \inf \{t | X_t \ge n\}$. This is a localizing sequence by
    Lemma~\ref{lem:isLocalizingSequence_hittingAfter_Ici}. For every $t \in T$, we have by
    Lemma~\ref{lem:sup_stoppedProcess_le} that $(X^{\tau_n})^*_t \le n + \mathbb{I}_{\tau_n \le t}
    \|X_{\tau_n}\| = n + \mathbb{I}_{\tau_n \le t} \|X_{\tau_n \land t}\|$. Because X is of class
    DL, $X_{\tau_n \land t}$ is integrable, so $(X^{\tau_n})^*_t$ is integrable too, so $(X^{\tau_n}
    \mathbb{I}_{\tau_n > 0})^*_t$ is integrable. Thus $X$ has locally integrable supremum. -/)
  (proofUses := ["lem:sup_stoppedProcess_le", "lem:isLocalizingSequence_hittingAfter_Ici"])
  (latexEnv := "lemma")]
lemma ClassDL.hasLocallyIntegrableSup [TopologicalSpace ι] [OrderTopology ι]
    [FirstCountableTopology ι] [InfSet ι] [CompactIccSpace ι] [OrderBot ι] [MeasurableSpace ι]
    (hX1 : ∀ ω, IsCadlag (X · ω)) (hX2 : ClassDL X 𝓕 P)
    (h𝓕 : 𝓕.IsRightContinuous) :
    HasLocallyIntegrableSup X 𝓕 P := by
      sorry

end LinearOrder

section ConditionallyCompleteLinearOrderBot


variable [ConditionallyCompleteLinearOrderBot ι] {𝓕 : Filtration ι mΩ}
  [Filtration.HasUsualConditions 𝓕 P] [TopologicalSpace ι] [OrderTopology ι] [MeasurableSpace ι]
    [SecondCountableTopology ι] [DenselyOrdered ι] [NoMaxOrder ι] [BorelSpace ι]
    [IsFiniteMeasure P] [CompleteSpace E] [NormedSpace ℝ E]

@[blueprint
  "lem:hasLocallyIntegrableSup_of_locally_classDL"
  (statement := /-- Assume $T$ has a bottom element $\bot$ and that its closed intervals are
    compact. If $X$ is a càdlàg and adapted process, and if the filtration is right-continuous, then
    any process locally of class DL has locally integrable supremum. -/)
  (proof := /-- Apply Lemma~\ref{lem:local_induction} using
    Lemma~\ref{lem:ClassDL.hasLocallyIntegrableSup} and
    Lemma~\ref{lem:isStable_hasLocallyIntegrableSup}. -/)
  (latexEnv := "lemma")]
lemma hasLocallyIntegrableSup_of_locally_classDL (hX1 : ∀ᵐ (ω : Ω) ∂P, IsCadlag (X · ω))
    (hX2 : Locally (ClassDL · 𝓕 P) 𝓕 X P) (h𝓕 : 𝓕.IsRightContinuous) :
    HasLocallyIntegrableSup X 𝓕 P :=
  locally_induction₂ h𝓕 (fun _ hCad hDL ↦ ClassDL.hasLocallyIntegrableSup hCad hDL h𝓕)
     isStable_isCadlag isStable_classDL isStable_hasIntegrableSup (locally_isCadlag_iff.mpr hX1) hX2

end ConditionallyCompleteLinearOrderBot

end ProbabilityTheory
