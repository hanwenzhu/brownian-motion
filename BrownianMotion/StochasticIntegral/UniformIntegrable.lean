/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Architect
import BrownianMotion.Auxiliary.ENNReal
import Mathlib.Probability.Martingale.OptionalSampling
import BrownianMotion.Auxiliary.Jensen

/-!
# Uniform integrability

-/

open scoped NNReal ENNReal
open Filter

namespace MeasureTheory

variable {ι κ Ω E F : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

@[blueprint
  "lem:uniformIntegrableAdd"
  (statement := /-- Let $(X_t)_{t \in T}$ and $(Y_t)_{t \in T}$ be two families of uniformly
    integrable random variables.
    Then the family $(X_t + Y_t)_{t \in T}$ is uniformly integrable. -/)
  (proof := /-- The families $X$ and $Y$ are uniformly integrable in the measure-theoretic sense and
    almost-everywhere strongly measurable, so $X + Y$ is too (see
    \href{https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/UniformIntegrable.html#MeasureTheory.UnifIntegrable.add}{MeasureTheory.UnifIntegrable.add}).
    Moreover, $X$ and $Y$ are bounded in $L^p$, so $X + Y$ is too. So $X + Y$ is uniformly
    integrable. -/)
  (latexEnv := "lemma")]
lemma UniformIntegrable.add [NormedAddCommGroup E] {X Y : ι → Ω → E} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hX : UniformIntegrable X p μ) (hY : UniformIntegrable Y p μ) :
    UniformIntegrable (X + Y) p μ := by
  refine ⟨fun _ ↦ (hX.1 _).add (hY.1 _), ?_, ?_⟩
  · rcases hX with ⟨hX₁, hX₂, hX₃⟩
    rcases hY with ⟨hY₁, hY₂, hY₃⟩
    exact hX₂.add hY₂ hp hX₁ hY₁
  · obtain ⟨C_X, hC_X⟩ := hX.2.2
    obtain ⟨C_Y, hC_Y⟩ := hY.2.2
    exact ⟨C_X + C_Y,
      fun i ↦ le_trans (eLpNorm_add_le (hX.1 i) (hY.1 i) hp) (add_le_add (hC_X i) (hC_Y i))⟩

@[blueprint
  "lem:uniformIntegrableDominated"
  (statement := /-- Let $(X_s)_{s \in S}$ be a family of random variables and $(Y_t)_{t \in T}$ be a
    family of uniformly integrable random variables. If for all $s$, there exists $t$ such that
    $\|X_s\| \le \|Y_t\|$ almost surely, then $X$ is uniformly integrable. -/)
  (proof := /-- Let $\epsilon > 0$. The family $Y$ is uniformly integrable, thus there exists $C \ge
    0$ such that for $t \in T$, $P[\|Y_t\|^p \mathbb{I}_{\|Y_t\| \ge C}]^{1/p} \le \epsilon$. For
    all $s$, there exists $t$ such that $\|X_s\|^p \le \|Y_t\|^p$, so $P[\|X_s\|^p
    \mathbb{I}_{\|X_s\| \ge C}]^{1/p} \le \epsilon$. Thus $X$ is uniformly integrable. -/)
  (latexEnv := "lemma")]
lemma uniformIntegrable_of_dominated [NormedAddCommGroup E] [NormedAddCommGroup F]
    {X : ι → Ω → E} {Y : κ → Ω → F} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hY : UniformIntegrable Y p μ) (mX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hX : ∀ i, ∃ j, ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ ‖Y j ω‖) :
    UniformIntegrable X p μ := sorry

@[blueprint
  "lem:uniformIntegrableNorm"
  (statement := /-- If $(X_t)_{t \in T}$ is a family of uniformly integrable random variables, then
    so is $(\|X_t\|)_{t \in T}$. -/)
  (proof := /-- Apply Lemma~\ref{lem:uniformIntegrableDominated} with $Y := X$. -/)
  (latexEnv := "lemma")]
lemma UniformIntegrable.norm [NormedAddCommGroup E] {X : ι → Ω → E} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hY : UniformIntegrable X p μ) :
    UniformIntegrable (fun t ω ↦ ‖X t ω‖) p μ := by
  refine uniformIntegrable_of_dominated hp hY ?_ (fun i ↦ ⟨i, by simp⟩)
  exact fun i ↦ (UniformIntegrable.aestronglyMeasurable hY i).norm

@[blueprint
  "lem:uniformIntegrableIffNorm"
  (statement := /-- Let $(X_t)_{t \in T}$ be a family of uniformly integrable random variables. It
    is uniformly integrable if and only if $(\|X_t\|)_{t \in T}$ is. -/)
  (proof := /-- The forward direction is Lemma~\ref{lem:uniformIntegrableNorm}. The converse
    direction follows from Lemma~\ref{lem:uniformIntegrableDominated} with $Y := (\|X_t\|)_{t \in
    T}$. -/)
  (latexEnv := "lemma")]
lemma uniformIntegrable_iff_norm [NormedAddCommGroup E] {X : ι → Ω → E} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (mX : ∀ i, AEStronglyMeasurable (X i) μ) :
    UniformIntegrable X p μ ↔ UniformIntegrable (fun t ω ↦ ‖X t ω‖) p μ := by
  refine ⟨UniformIntegrable.norm hp, fun hNorm ↦ uniformIntegrable_of_dominated hp hNorm mX ?_⟩
  exact fun i ↦ ⟨i, by simp⟩

@[blueprint
  "lem:uniformIntegrableDominatedSingleton"
  (statement := /-- Let $(X_t)_{t \in T}$ be a family of random variables and $Y$ be a real random
    variable in $L^p$. If for all $t$, $\|X_t\| \le Y$ almost surely, then $X$ is uniformly
    integrable. -/)
  (proof := /-- Because $Y$ is in $L^p$, we deduce that $\{Y\}$ is uniformly integrable. The
    conclusion then follows from Lemma~\ref{lem:uniformIntegrableDominated}. -/)
  (proofUses := ["lem:uniformIntegrableDominated"])
  (latexEnv := "lemma")]
lemma uniformIntegrable_of_dominated_singleton [NormedAddCommGroup E] {X : ι → Ω → E} {Y : Ω → ℝ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hY : MemLp Y p μ) (mX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hX : ∀ i, ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ Y ω) :
    UniformIntegrable X p μ := sorry

@[blueprint
  "lem:condExpUI"
  (statement := /-- If $(X_i)_{i \in \iota}$ is a family of (probabilistically) uniformly integrable
    functions and $(\mathcal{F}_j)_{j \in \kappa}$ is a family of $\sigma$-algebras,
    then the family $(P[X_i \mid \mathcal{F}_j])_{i \in \iota, j \in \kappa}$ is uniformly
    integrable. -/)
  (proof := /-- Since $(X_i)_{i \in \iota}$ is uniformly integrable, it is uniformly bounded in
    $L^1$, thus so is $(P[X_i \mid \mathcal{F}_j])_{i \in \iota, j \in \kappa}$. Moreover, for any
    \(\epsilon > 0\),
    there exists some \(\delta > 0\) such that
    for any measurable set \(A\) with \(P(A) < \delta\), we have that \(\sup_{i \in \iota} P[|X_i|
    \mathbb{I}_A] < \epsilon\).
    
    On the other hand, by Markov's inequality, for any $\lambda > 0$, $i \in \iota$ and $j \in
    \kappa$ we have that
    \[P(|P[X_i \mid \mathcal{F}_j]| \ge \lambda) \le \lambda^{-1}P[|P[X_i \mid \mathcal{F}_j]|] \le
    \lambda^{-1}P[|X_i|].\]
    Now set \(\lambda := \delta^{-1} \sup_{i \in \iota} P[|X_i|] + 1\). Then for any $i \in \iota$
    and $j \in \kappa$ we have that
    \[P(|P[X_i \mid \mathcal{F}_j]| \ge \lambda) \le \frac{P[|X_i|]}{\delta^{-1} \sup_{k \in \iota}
    P[|X_k|] + 1} < \delta,\]
    and so,
    \begin{align*}
      P[|P[X_i \mid \mathcal{F}_j]| \mathbb{I}_{|P[X_i \mid \mathcal{F}_i]| \ge \lambda}]
      & = P[|P[X_i \mid \mathcal{F}_j] \mathbb{I}_{|P[X_i \mid \mathcal{F}_i]| \ge \lambda}|] \\
      & = P[|P[X_i \mathbb{I}_{|P[X_i \mid \mathcal{F}_i]| \ge \lambda} \mid \mathcal{F}_j]|] \\
      & \le P[P[|X_i|\mathbb{I}_{|P[X_i \mid \mathcal{F}_j]| \ge \lambda} \mid \mathcal{F}_j]] \\
      & = P[|X_i|\mathbb{I}_{|P[X_i \mid \mathcal{F}_j]| \ge \lambda}] < \epsilon,
    \end{align*}
    showing that \((P[X_i \mid \mathcal{F}_j])_{i \in \iota, j \in \kappa}\) is uniformly
    integrable. -/)
  (latexEnv := "lemma")]
lemma UniformIntegrable.condExp' {X : ι → Ω → E} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [IsFiniteMeasure μ] (hX : UniformIntegrable X 1 μ)
    {𝓕 : κ → MeasurableSpace Ω} (h𝓕 : ∀ i, 𝓕 i ≤ mΩ) :
    UniformIntegrable (fun (p : ι × κ) ↦ μ[X p.1 | 𝓕 p.2]) 1 μ := by
  have hX' := hX
  obtain ⟨hX1, hX2, ⟨C, hC⟩⟩ := hX
  refine ⟨fun p ↦ (stronglyMeasurable_condExp.mono (h𝓕 p.2)).aestronglyMeasurable, ?_,
    ⟨C, fun p ↦ (eLpNorm_condExp_le_eLpNorm le_rfl (X p.1)).trans (hC p.1)⟩⟩
  refine unifIntegrable_of le_rfl (by simp)
    (fun p ↦ (stronglyMeasurable_condExp.mono (h𝓕 p.2)).aestronglyMeasurable) fun ε hε ↦ ?_
  obtain ⟨δ, δ_pos, hδ⟩ := hX2 hε
  lift δ to ℝ≥0 using δ_pos.le
  have hδ' : δ ≠ 0 := by
    convert δ_pos.ne'
    simp
  refine ⟨(⨆ i, eLpNorm (X i) 1 μ).toNNReal / δ + 1, fun p ↦ ?_⟩
  rw [eLpNorm_congr_ae (condExp_indicator ?_ ?_).symm]
  rotate_left
  · exact memLp_one_iff_integrable.1 (hX'.memLp p.1)
  · exact stronglyMeasurable_const.measurableSet_le stronglyMeasurable_condExp.nnnorm
  grw [eLpNorm_condExp_le_eLpNorm le_rfl, hδ]
  · exact stronglyMeasurable_const.measurableSet_le <|
      stronglyMeasurable_condExp.mono (h𝓕 p.2) |>.nnnorm
  calc
  _ ≤ eLpNorm μ[X p.1 | 𝓕 p.2] 1 μ / ((⨆ i, eLpNorm (X i) 1 μ).toNNReal / δ + 1) := by
    simp_rw [← ENNReal.coe_le_coe, ← enorm_eq_nnnorm]
    grw [meas_ge_le_lintegral_div (by fun_prop) (by simp) (by simp),
      ← eLpNorm_one_eq_lintegral_enorm]
    norm_cast
  _ ≤ eLpNorm μ[X p.1 | 𝓕 p.2] 1 μ / ((⨆ i, eLpNorm (X i) 1 μ) / δ) := by
    grw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top (by simp) <| iSup_le hC),
      ENNReal.div_le_div_left (a := (⨆ i, eLpNorm (X i) 1 μ) / δ)]
    simp
  _ = eLpNorm μ[X p.1 | 𝓕 p.2] 1 μ / (⨆ i, eLpNorm (X i) 1 μ) * δ := by
    rw [← ENNReal.div_mul _ (Or.inr <| ENNReal.coe_ne_zero.2 hδ') (by simp)]
  _ ≤ 1 * δ := by
    grw [eLpNorm_condExp_le_eLpNorm le_rfl]
    gcongr
    exact ENNReal.div_le_one_of_le <| le_iSup (α := ℝ≥0∞) _ p.1
  _ = _ := by simp

lemma UnifIntegrable.comp {κ : Type*} [NormedAddCommGroup E]
    {X : ι → Ω → E} {p : ℝ≥0∞} (hX : UnifIntegrable X p μ) (f : κ → ι) :
    UnifIntegrable (X ∘ f) p μ := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hX hε
  exact ⟨δ, ⟨hδ, fun i ↦ h (f i)⟩⟩

@[blueprint
  "lem:uniformIntegrableComp"
  (statement := /-- If $(X_t)_{t \in T}$ is uniformly integrable and $\phi : S \to T$, then
    $(X_{\phi(s)})_{s \in S}$ is uniformly integrable. -/)
  (proof := /-- This is immediate from the definition. -/)
  (latexEnv := "lemma")]
lemma UniformIntegrable.comp {κ : Type*} [NormedAddCommGroup E]
    {X : ι → Ω → E} {p : ℝ≥0∞} (hX : UniformIntegrable X p μ) (f : κ → ι) :
    UniformIntegrable (X ∘ f) p μ := by
  obtain ⟨hX1, hX2, ⟨C, hC⟩⟩ := hX
  exact ⟨fun _ ↦ hX1 _, hX2.comp f, ⟨C, fun i ↦ hC (f i)⟩⟩

lemma UniformIntegrable.condExp {X : ι → Ω → E} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [IsFiniteMeasure μ] (hX : UniformIntegrable X 1 μ) {𝓕 : ι → MeasurableSpace Ω}
    (h𝓕 : ∀ i, 𝓕 i ≤ mΩ) :
    UniformIntegrable (fun i ↦ μ[X i | 𝓕 i]) 1 μ :=
  (hX.condExp' h𝓕).comp (fun i ↦ (i, i))

variable {ι : Type*} [LinearOrder ι] [OrderBot ι] [Countable ι] [TopologicalSpace ι]
  [OrderTopology ι] [FirstCountableTopology ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {𝓕 : Filtration ι mΩ} [SigmaFiniteFiltration μ 𝓕]

lemma Martingale.ae_eq_condExp_of_isStoppingTime {X : ι → Ω → E}
    (hX : Martingale X 𝓕 μ) {τ : Ω → WithTop ι} (hτ : IsStoppingTime 𝓕 τ) {n : ι}
    (hτ_le : ∀ ω, τ ω ≤ n) :
    stoppedValue X τ =ᵐ[μ] μ[X n | hτ.measurableSpace] :=
  stoppedValue_ae_eq_condExp_of_le hX (isStoppingTime_const 𝓕 n) hτ (n := n) hτ_le
    (fun _ ↦ le_rfl)

attribute [blueprint
  "def:IsStoppingTime"
  (title := "Stopping time")
  (statement := /-- A stopping time with respect to some filtration $\mathcal{F}$ indexed by $T$ is
    a function $\tau : \Omega \to T \cup \{\infty\}$ such that for all $i$, the preimage of $\{j
    \mid j \le i\}$ along $\tau$ is measurable with respect to $\mathcal{F}_i$. -/)]
  MeasureTheory.IsStoppingTime

attribute [blueprint
  "lem:optionalSampling_discrete"
  (title := "Optional sampling (discrete time)")
  (statement := /-- Let $X$ be a discrete time martingale with respect to the filtration
    $\mathcal{F}$ and let
    $\tau, \sigma$ be stopping times. Then, if $\tau$ is bounded, we have that almost surely,
    $X_{\tau \wedge \sigma} = P[X_{\tau} \mid \mathcal{F}_{\sigma}]$. -/)
  (latexEnv := "lemma")]
  MeasureTheory.Martingale.stoppedValue_min_ae_eq_condExp

@[blueprint
  "lem:uniformIntegrable_stoppedValue_martingale"
  (statement := /-- Let $X$ be a martingale on a discrete index set and let $(\tau_k)_{k \in
    \mathbb{N}}$ be a sequence of stopping times that are uniformly bounded by $n$.
    Then, the family of stopped values $\{X_{\tau_k}\}_{k \in \mathbb{N}}$ is uniformly integrable.
    -/)
  (proof := /-- By optional sampling (Lemma~\ref{lem:optionalSampling_discrete}), we have that for
    each $k$, $X_{\tau_k} = P[X_n \mid \mathcal{F}_{\tau_k}]$.
    Thus, the result follows by Lemma~\ref{lem:condExpUI} as $\{X_n\}$ is uniformly integrable. -/)
  (latexEnv := "lemma")]
lemma Martingale.uniformIntegrable_stoppedValue {X : ι → Ω → E} {𝓕 : Filtration ι mΩ}
    [SigmaFiniteFiltration μ 𝓕] [IsFiniteMeasure μ]
    (hX : Martingale X 𝓕 μ) (τ : ℕ → Ω → WithTop ι) (hτ : ∀ i, IsStoppingTime 𝓕 (τ i))
    {n : ι} (hτ_le : ∀ i ω, τ i ω ≤ n) :
    UniformIntegrable (fun i ↦ stoppedValue X (τ i)) 1 μ :=
  (((uniformIntegrable_subsingleton (f := fun _ : Unit ↦ X n) le_rfl (by simp)
    (fun _ ↦ memLp_one_iff_integrable.2 <| hX.integrable n)).condExp'
    (fun i ↦ (hτ i).measurableSpace_le)).ae_eq <| fun m ↦
      (hX.ae_eq_condExp_of_isStoppingTime (hτ m.2) (hτ_le m.2)).symm).comp (fun i ↦ ((), i))

@[blueprint
  "lem:uniformIntegrable_stoppedValue_submartingale"
  (statement := /-- Let $X$ be a submartingale on a discrete index set and let $(\tau_k)_{k \in
    \mathbb{N}}$ be a sequence of stopping times that are uniformly bounded by $p$.
    Then, the family of stopped values $\{X_{\tau_k}\}_{k \in \mathbb{N}}$ is uniformly integrable.
    -/)
  (proof := /-- Use Doob decomposition to write $X_n = M_n + A_n$, where $M$
    (Definition~\ref{def:martingalePart}) is a martingale
    (Lemma~\ref{lem:martingale_martingalePart}) and $A$ (Definition~\ref{def:predictablePart}) is a
    predictable process (Lemma~\ref{lem:predictable_predictablePart}).
    We know from Lemma~\ref{lem:uniformIntegrable_stoppedValue_martingale} that $(M_{\tau_k})_{k \in
    \mathbb{N}}$ is uniformly integrable. Combining Lemma~\ref{lem:uniformIntegrableAdd} and
    Lemma~\ref{lem:uniformIntegrableDominatedSingleton}, it suffices to show that $(A_{\tau_k})_{k
    \in \mathbb{N}}$ is dominated. It is dominated by $A_p$ thanks to
    Lemma~\ref{lem:predictablePart_zero} and
    Lemma~\ref{lem:nondecreasing_predictablePart_of_submartingale}. -/)
  (proofUses := ["lem:uniformIntegrableAdd", "lem:predictable_predictablePart",
    "lem:uniformIntegrableDominatedSingleton", "lem:predictablePart_zero",
    "lem:uniformIntegrable_stoppedValue_martingale", "lem:martingale_martingalePart",
    "lem:nondecreasing_predictablePart_of_submartingale", "def:predictablePart",
    "def:martingalePart"])
  (latexEnv := "lemma")]
lemma Submartingale.uniformIntegrable_stoppedValue {X : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ}
    [SigmaFiniteFiltration μ 𝓕]
    (hX : Submartingale X 𝓕 μ) (τ : ℕ → Ω → WithTop ι) (hτ : ∀ i, IsStoppingTime 𝓕 (τ i))
    {n : ι} (hτ_le : ∀ i ω, τ i ω ≤ n) :
    UniformIntegrable (fun i ↦ stoppedValue X (τ i)) 1 μ :=
  sorry

omit [Countable ι]

@[blueprint
  "lem:uniformIntegrable_stoppedValue_martingale_of_countable_range"
  (statement := /-- Let $X$ be a martingale and let $(\tau_k)_{k \in \mathbb{N}}$ be a sequence of
    stopping times that are uniformly bounded by $n$.
    Then, the family of stopped values $\{X_{\tau_k}\}_{k \in \mathbb{N}}$ is uniformly integrable
    if for each $k$, $\tau_k$ takes value in a countable set. -/)
  (proof := /-- Same proof as in Lemma~\ref{lem:uniformIntegrable_stoppedValue_martingale}. -/)
  (latexEnv := "lemma")]
lemma Martingale.uniformIntegrable_stoppedValue_of_countable_range
    {X : ι → Ω → E} {𝓕 : Filtration ι mΩ} [SigmaFiniteFiltration μ 𝓕] [IsFiniteMeasure μ]
    (hX : Martingale X 𝓕 μ) (τ : ℕ → Ω → WithTop ι) (hτ : ∀ i, IsStoppingTime 𝓕 (τ i))
    {n : ι} (hτ_le : ∀ i ω, τ i ω ≤ n) (hτ_countable : ∀ i, (Set.range <| τ i).Countable) :
    UniformIntegrable (fun i ↦ stoppedValue X (τ i)) 1 μ :=
  (((uniformIntegrable_subsingleton (f := fun _ : Unit ↦ X n) le_rfl (by simp)
    (fun _ ↦ memLp_one_iff_integrable.2 <| hX.integrable n)).condExp'
    (fun i ↦ (hτ i).measurableSpace_le)).ae_eq fun _ ↦
      (hX.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range (hτ _) (hτ_le _)
      (hτ_countable _)).symm).comp (fun i ↦ ((), i))

lemma Martingale.integrable_stoppedValue_of_countable_range
    {X : ι → Ω → E} {𝓕 : Filtration ι mΩ} [SigmaFiniteFiltration μ 𝓕] [IsFiniteMeasure μ]
    (hX : Martingale X 𝓕 μ) (τ : Ω → WithTop ι) (hτ : IsStoppingTime 𝓕 τ)
    {n : ι} (hτ_le : ∀ ω, τ ω ≤ n) (hτ_countable : (Set.range τ).Countable) :
    Integrable (stoppedValue X τ) μ := by
  rw [← memLp_one_iff_integrable]
  exact (hX.uniformIntegrable_stoppedValue_of_countable_range (fun _ ↦ τ)
    (fun _ ↦ hτ) (fun _ _ ↦ hτ_le _) (fun _ ↦ hτ_countable)).memLp 0

lemma TendstoInMeasure.aestronglyMeasurable
    {α β ι : Type*} {m : MeasurableSpace α} {μ : Measure α} [PseudoEMetricSpace β]
    {u : Filter ι} [NeBot u] [IsCountablyGenerated u]
    {f : ι → α → β} {g : α → β} (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (h_tendsto : TendstoInMeasure μ f u g) : AEStronglyMeasurable g μ := by
  obtain ⟨ns, -, hns⟩ := h_tendsto.exists_seq_tendsto_ae'
  exact aestronglyMeasurable_of_tendsto_ae atTop (fun n => hf (ns n)) hns

lemma seq_tendsto_ae_bounded
    {α β : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]
    {f : ℕ → α → β} {g : α → β} {C : ℝ≥0∞} (p : ℝ≥0∞) (bound : ∀ n, eLpNorm (f n) p μ ≤ C)
    (h_tendsto : ∀ᵐ (x : α) ∂μ, Tendsto (fun n => f n x) atTop (nhds (g x)))
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) : eLpNorm g p μ ≤ C := by
  calc
    _ ≤ atTop.liminf (fun (n : ℕ) => eLpNorm (f n) p μ) :=
      Lp.eLpNorm_lim_le_liminf_eLpNorm (fun n => hf n) g h_tendsto
    _ ≤ C := by
      refine liminf_le_of_le (by isBoundedDefault) (fun b hb => ?_)
      obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp hb
      exact le_trans (hn n (by linarith)) (bound n)

lemma tendstoInMeasure_bounded
    {α β ι : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]
    {u : Filter ι} [NeBot u] [IsCountablyGenerated u]
    {f : ι → α → β} {g : α → β} {C : ℝ≥0∞} (p : ℝ≥0∞) (bound : ∀ i, eLpNorm (f i) p μ ≤ C)
    (h_tendsto : TendstoInMeasure μ f u g)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) : eLpNorm g p μ ≤ C := by
  obtain ⟨l, hl⟩ := h_tendsto.exists_seq_tendsto_ae'
  exact seq_tendsto_ae_bounded p (fun n => bound (l n)) hl.2 (fun n => hf (l n))

@[blueprint
  "lem:memLp_of_tendstoInMeasure"
  (statement := /-- Let $(X_n)_{n \in \mathbb{N}}$ be a sequence of $p$-uniformly integrable
    stochastic processes and suppose $X_n \to X$
    in probability as $n \to \infty$. Then, $X$ is $L^p$. -/)
  (proof := /-- Since $X_n \to X$ in probability, it has a subsequence $(X_{n_k}) \subseteq (X_n)$
    which converges
    to $X$ almost surely. Thus, we have by Fatou's lemma that
    \[P[|X|^p] = P[\liminf_{k \to \infty} |X_{n_k}|^p] \le \liminf_{k \to \infty} P[|X_{n_k}|^p] <
    \infty\]
    where the last inequality follows as uniform integrability implies that $(X_n)$ is uniform
    bounded in $L^p$. -/)
  (latexEnv := "lemma")]
lemma UniformIntegrable.memLp_of_tendstoInMeasure
    {α β : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]
    {fn : ℕ → α → β} {f : α → β} (p : ℝ≥0∞) (hUI : UniformIntegrable fn p μ)
    (htends : TendstoInMeasure μ fn atTop f) :
    MemLp f p μ := by
  refine ⟨htends.aestronglyMeasurable hUI.1, ?_⟩
  obtain ⟨C, hC⟩ := hUI.2.2
  exact lt_of_le_of_lt (tendstoInMeasure_bounded p (fun i => hC i) htends (fun i => hUI.1 i))
    ENNReal.coe_lt_top

lemma UnifIntegrable.unifIntegrable_of_tendstoInMeasure
    {α β ι : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]
    {fn : ι → α → β} (p : ℝ≥0∞) (hUI : UnifIntegrable fn p μ)
    (hfn : ∀ i, AEStronglyMeasurable (fn i) μ) :
    UnifIntegrable (fun (f : {g : α → β | ∃ ni : ℕ → ι,
      TendstoInMeasure μ (fn ∘ ni) atTop g}) ↦ f.1) p μ := by
  refine fun ε hε => ?_
  obtain ⟨δ, hδ, hδ'⟩ := hUI hε
  refine ⟨δ, hδ, fun ⟨f, s, hs⟩ t ht ht' => ?_⟩
  obtain ⟨u, hu⟩ := hs.exists_seq_tendsto_ae
  refine seq_tendsto_ae_bounded p (fun n => hδ' (s (u n)) t ht ht') ?_ ?_
  · filter_upwards [hu.2] with a ha
    by_cases memt : a ∈ t
    · simpa [memt]
    · simp [memt]
  · exact fun n => (hfn (s (u n))).indicator ht

@[blueprint
  "lem:uniformIntegrable_of_tendstoInMeasure"
  (statement := /-- Let $(X_t)_{t \in T}$ be a family of $p$-uniformly integrable stochastic
    processes. Then the family of limits in probability of sequences of $X$ is uniformly integrable.
    -/)
  (proof := /-- Let $\epsilon > 0$. There exists $\delta > 0$ such that for all $t\in T$ and all
    measurable set $S$ such that $P(S)<\delta$,
    \[P[\|X_t\|^p\mathbb{I}_S]^{1/p}\le \varepsilon.\]
    Let $(t_n)_{n \in \mathbb{N}}$ be a sequence in $T$ such that $X_{t_n}$ converges in probability
    to $Y$. Then it has a subsequence $(X_{t_{n_k}})$ which converges to $Y$ almost surely. Thus, we
    have by Fatou's lemma that
    \[P[\|Y\|^p \mathbb{I}_{S}]^{1/p} = P[\liminf_{k \to \infty} \|X_{t_{n_k}}\|^p
    \mathbb{I}_{S}]^{1/p} \le \liminf_{k \to \infty} P[\|X_{t_{n_k}}\|^p \mathbb{I}_{S}]^{1/p} \le
    \epsilon.\]
    This proves that the family of limits in probability of sequences of $X$ is uniformly integrable
    in the measure theory sense. One can prove uniform boundedness of this family by using Fatou's
    lemma and the existence of an almost everywhere convergent subsequence in a similar way. -/)
  (latexEnv := "lemma")]
lemma UniformIntegrable.uniformIntegrable_of_tendstoInMeasure
    {α β ι : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]
    {fn : ι → α → β} (p : ℝ≥0∞) (hUI : UniformIntegrable fn p μ) :
    UniformIntegrable (fun (f : {g : α → β | ∃ ni : ℕ → ι,
      TendstoInMeasure μ (fn ∘ ni) atTop g}) ↦ f.1) p μ := by
  refine ⟨fun ⟨f, s, hs⟩ => ?_, hUI.2.1.unifIntegrable_of_tendstoInMeasure p (fun i => hUI.1 i), ?_⟩
  · exact hs.aestronglyMeasurable (fun n => hUI.1 (s n))
  · obtain ⟨C, hC⟩ := hUI.2.2
    refine ⟨C, fun ⟨f, s, hs⟩ => ?_⟩
    exact tendstoInMeasure_bounded p (fun n => hC (s n)) hs (fun n => hUI.1 (s n))

lemma UniformIntegrable.integrable_of_tendstoInMeasure
    {α β : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]
    {fn : ℕ → α → β} {f : α → β} (hUI : UniformIntegrable fn 1 μ)
    (htends : TendstoInMeasure μ fn atTop f) :
    Integrable f μ := by
  rw [← memLp_one_iff_integrable]
  exact hUI.memLp_of_tendstoInMeasure 1 htends

end MeasureTheory
