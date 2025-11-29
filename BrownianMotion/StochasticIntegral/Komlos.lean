/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Architect
import Mathlib.Probability.Moments.Basic

/-!
# Komlos lemmas

-/

variable {E Ω : Type*} {mΩ : MeasurableSpace Ω}

open Filter MeasureTheory
open scoped Topology NNReal ENNReal

@[blueprint
  "lem:komlos_convex"
  (statement := /-- Let $(f_n)_{n\in\mathbb{N}}$ be a sequence in a vector space $E$ and $\phi : E
    \to \mathbb{R}_+$ be a function such that $\phi(f_n)$ is a bounded sequence.
    For $\delta > 0$, let $S_\delta = \{(f, g) \mid \phi(f)/2 + \phi(g)/2 - \phi((f+g)/2) \ge
    \delta\}$.
    Then there exist $g_n\in convex(f_n,f_{n+1},\cdots)$ such that for all $\delta > 0$, for $N$
    large enough and $n, m \ge N$, $(g_n, g_m) \notin S_\delta$. -/)
  (proof := /-- Let $B$ be the bound of $(\phi(f_n))_{n\in\mathbb{N}}$.
    Then for all $n\in\mathbb{N}$ and $g\in convex(f_n,f_{n+1},\cdots)$ we have $\phi(g)\le B$ by
    convexity of $\phi$.
    Let $r_n = \inf(\phi(g) \mid g\in convex(f_n, f_{n+1},\ldots))$.
    By construction $(r_n)_{n\in\mathbb{N}}$ is nondecreasing.
    Let $A = \sup_{n \ge 1} r_n$, which is finite (as $A \le B$) and for each $n$ we may pick some
    $g_n\in convex(f_n, f_{n+1},\ldots)$ such that $\phi(g_n) \le A+1/n$ by $\inf$ and $\sup$
    definitions.
    
    Let $\varepsilon \in (0, \delta/4)$.
    By properties of $\sup$ there exists $\bar{n}$ such that $r_{\bar{n}} \ge A-\varepsilon$ and
    such that $\frac{1}{\bar{n}} \le \varepsilon$.
    Let $m \ge k \ge \bar{n}$.
    We have $(g_k+g_m)/2 \in convex(f_k,f_{k+1},\ldots)$ and it follows since
    $(r_n)_{n\in\mathbb{N}}$ is nondecreasing that $\phi((g_k+g_m)/2) \ge A - \varepsilon$.
    Hence due to the ordering of $m,k,\bar{n}$,
    \begin{align*}
      \phi(g_k)/2 + \phi(g_m)/2 - \phi((g_k+g_m)/2)
      &\le 2(A + \frac{1}{\bar{n}}) - 2(A - \varepsilon)
      \\
      &\le 4 \varepsilon
      \\
      &< \delta
      \: .
    \end{align*}
    Thus, for $n, m \ge \bar{n}$, $(g_n, g_m) \notin S_\delta$. -/)
  (latexEnv := "lemma")]
lemma komlos_convex [AddCommMonoid E] [Module ℝ≥0 E]
  {f : ℕ → E} {φ : E → ℝ} (hφ_nonneg : 0 ≤ φ)
  (hφ_bdd : ∃ M : ℝ, ∀ n, φ (f n) ≤ M) :
  ∃ g : ℕ → E, (∀ n, g n ∈ convexHull ℝ≥0 (Set.range fun m ↦ f (n + m))) ∧
    ∀ δ > 0, ∃ N, ∀ n m, N ≤ n → N ≤ m →
      2⁻¹ * φ (g n) + 2⁻¹ * φ (g m) - φ ((2 : ℝ≥0)⁻¹ • (g n + g m)) < δ := by
  obtain ⟨M, hM⟩ := hφ_bdd
  let r : ℕ → ℝ := fun n ↦ sInf (Set.image φ (convexHull ℝ≥0 (Set.range (fun m ↦ f (n + m)))))
  have hr_nondec n : r n ≤ r (n + 1) := by
    apply_rules [csInf_le_csInf]
    · exact ⟨0, Set.forall_mem_image.2 fun x hx ↦ hφ_nonneg x⟩
    · exact ⟨_, ⟨ _, subset_convexHull ℝ≥0 _ ⟨0, rfl⟩, rfl⟩⟩
    · refine Set.image_mono <| convexHull_min ?_ (convex_convexHull ℝ≥0 _)
      rintro _ ⟨m, rfl⟩; exact subset_convexHull ℝ≥0 _ ⟨m + 1, by simp [add_comm, add_left_comm]⟩
  obtain ⟨A, hA⟩ : ∃ A, Filter.Tendsto r Filter.atTop (nhds A) := by
    refine ⟨_, tendsto_atTop_ciSup (monotone_nat_of_le_succ hr_nondec) ?_⟩
    exact ⟨M, Set.forall_mem_range.mpr fun n ↦ csInf_le
      ⟨0, Set.forall_mem_image.mpr fun x hx ↦ hφ_nonneg x⟩
        (Set.mem_image_of_mem _ <| subset_convexHull ℝ≥0 _
          <| Set.mem_range_self 0) |> le_trans <| by simpa using hM n⟩
  obtain ⟨g, hg⟩ :
      ∃ g : ℕ → E, (∀ n, g n ∈ convexHull ℝ≥0 (Set.range (fun m ↦ f (n + m))))
          ∧ (∀ n, φ (g n) ≤ A + 1 / (n + 1)) := by
    have h_exists_g :
        ∀ n, ∃ g ∈ convexHull ℝ≥0 (Set.range (fun m ↦ f (n + m))), φ g ≤ A + 1 / (n + 1) := by
      intro n
      have h_exists_g :
          ∃ g ∈ convexHull ℝ≥0 (Set.range (fun m ↦ f (n + m))), φ g < A + 1 / (n + 1) := by
        have h_exists_g : r n < A + 1 / (n + 1) := by
          exact lt_add_of_le_of_pos (le_of_tendsto_of_tendsto tendsto_const_nhds hA
            (Filter.eventually_atTop.2 ⟨n, fun m hm ↦ by
              induction hm <;> [tauto; linarith [hr_nondec ‹_›]]⟩)) (by positivity)
        contrapose! h_exists_g
        exact le_csInf ⟨ _, Set.mem_image_of_mem _ <| subset_convexHull ℝ≥0 _
          <| Set.mem_range_self 0 ⟩ fun x hx ↦ by
            rcases hx with ⟨ g, hg, rfl ⟩; exact h_exists_g g hg
      exact ⟨h_exists_g.choose, h_exists_g.choose_spec.1, le_of_lt h_exists_g.choose_spec.2⟩
    exact ⟨fun n ↦ Classical.choose (h_exists_g n),
      fun n ↦ Classical.choose_spec (h_exists_g n) |>.1,
        fun n ↦ Classical.choose_spec (h_exists_g n) |>.2⟩
  refine ⟨g, hg.1, fun δ δpos ↦ ?_⟩
  obtain ⟨ε, εpos, hε⟩ := exists_between (div_pos δpos zero_lt_four)
  obtain ⟨N, hN⟩ : ∃ N, r N ≥ A - ε ∧ 1 / (N + 1) ≤ ε := by
    rcases Metric.tendsto_atTop.mp hA ε εpos with ⟨N, hN⟩
    exact ⟨N + ⌈ε⁻¹⌉₊, by linarith [abs_lt.mp (hN (N + ⌈ε⁻¹⌉₊) (by grind))], by
      simpa using inv_le_of_inv_le₀ εpos (by linarith [Nat.le_ceil (ε⁻¹)])⟩
  refine ⟨N, fun n m hn hm ↦ ?_⟩
  have h_convex : φ ((1 / 2 : ℝ≥0) • (g n + g m)) ≥ A - ε := by
    have h_convex :
        (1 / 2 : ℝ≥0) • (g n + g m) ∈ convexHull ℝ≥0 (Set.range (fun m ↦ f (N + m))) := by
      simp only [one_div, gt_iff_lt, ge_iff_le, tsub_le_iff_right, smul_add] at *
      refine convex_convexHull ℝ≥0 _ ?_ ?_ ?_ ?_ ?_ <;> norm_num
      · refine convexHull_mono (Set.range_subset_iff.2 fun m ↦ ?_) (hg.1 n)
        exact ⟨m + (n - N), by grind⟩
      · refine convexHull_mono ?_ (hg.1 m)
        exact Set.range_subset_iff.2 fun k ↦ ⟨k + (m - N), by
          simp [show N + (k + (m - N)) = m + k by grind]⟩
    refine le_trans hN.1 ?_
    exact csInf_le ⟨0, Set.forall_mem_image.2 fun x hx ↦ hφ_nonneg _⟩ ⟨_, h_convex, rfl⟩
  norm_num at *
  linarith [hg.2 n, hg.2 m, inv_anti₀
    (by positivity) (by norm_cast; grind : (n : ℝ) + 1 ≥ N + 1), inv_anti₀
      (by positivity) (by norm_cast; grind : (m : ℝ) + 1 ≥ N + 1)]

@[blueprint
  "lem:komlos_aux"
  (statement := /-- Let $H$ be a Hilbert space and $(f_n)_{n\in\mathbb{N}}$ a bounded sequence in
    $H$. Then there exist functions $g_n\in convex(f_n,f_{n+1},\cdots)$ such that
    $(g_n)_{n\in\mathbb{N}}$ converges in $H$. -/)
  (proof := /-- Consider $\phi : H \to \mathbb{R}_+$ defined by $\phi(f) = \|f\|_2^2$, which is
    convex.
    Then Lemma \ref{lem:komlos_convex} applied to $(f_n)_{n\in\mathbb{N}}$ and $\phi$ gives us
    functions $g_n\in convex(f_n,f_{n+1},\cdots)$ such that for every $\delta>0$ there exists $N$
    such that for $n,m\geq N$, $(g_n,g_m)\notin S_\delta$.
    Thus for every $\delta>0$ there exists $N$ such that for $n,m\geq N$,
    \begin{align*}
      \|g_n\|_2^2/2 + \|g_m\|_2^2/2 - \|(g_n+g_m)/2\|_2^2
      &< \delta
      \: .
    \end{align*}
    But the left-hand side is equal to $\|g_n - g_m\|_2^2/4$ by the parallelogram identity, hence
    $(g_n)_{n\in\mathbb{N}}$ is a Cauchy sequence in $H$ and thus converges in $H$ by completeness.
    -/)
  (proofUses := ["lem:komlos_convex"])
  (latexEnv := "lemma")]
lemma komlos_norm [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : ℕ → E} (h_bdd : ∃ M : ℝ, ∀ n, ‖f n‖ ≤ M) :
    ∃ (g : ℕ → E) (x : E), (∀ n, g n ∈ convexHull ℝ (Set.range fun m ↦ f (n + m))) ∧
    Tendsto g atTop (𝓝 x) :=
  sorry

-- todo: check measurability hypothesis/conclusion
@[blueprint
  "lem:komlos_ennreal"
  (statement := /-- Let $(f_n)_{n\in\mathbb{N}}$ be a sequence of random variables with values in
    $[0, \infty]$.
    Then there exist random variables $g_n \in convex( f_n, f_{n+1}, \cdots)$ such that
    $(g_n)_{n\in\mathbb{N}}$ converges almost surely to a random variable $g$. -/)
  (proof := /-- Let $\phi : (\Omega \to [0, \infty]) \to [0, \infty]$ be defined by $\phi(X) =
    \mathbb{E}[e^{-X}]$.
    Then $\phi$ is convex and $\phi(f_n) \le 1$ for all $n$.
    By Lemma~\ref{lem:komlos_convex}, there exist $g_n \in convex( f_n, f_{n+1}, \cdots)$ such that
    for all $\delta>0$, for $N$ large enough and $n, m \ge N$,
    \begin{align*}
      \mathbb{E}[e^{-g_n}]/2 + \mathbb{E}[e^{-g_m}]/2 - \mathbb{E}[e^{-(g_n + g_m)/2}] < \delta
      \: .
    \end{align*}
    
    For $\varepsilon > 0$, let $B_\varepsilon = \{(x, y) \in [0, \infty]^2 \mid \vert x - y \vert
    \ge \varepsilon \text{ and } \min\{x, y\} \le 1/\varepsilon \}$.
    Then for all $x, y$,
    \begin{align*}
      \left\vert e^{-x} - e^{-y} \right\vert
      &\le \varepsilon + 2 e^{-1/\varepsilon} + 2 \mathbb{1}_{B_\varepsilon}(x, y)
      \: .
    \end{align*}
    Hence for any pair of random variables $(X, Y)$ with values in $[0, \infty]$,
    \begin{align*}
      \mathbb{E}\left[\left\vert e^{-X} - e^{-Y} \right\vert\right]
      &\le \varepsilon + 2 e^{-1/\varepsilon} + 2 P((X, Y) \in B_\varepsilon) \: .
    \end{align*}
    On the other hand, for $(x, y) \in B_\varepsilon$, there exists $\delta_\varepsilon > 0$ such
    that
    \begin{align*}
      e^{-x}/2 + e^{-y}/2 - e^{-(x + y)/2} \ge \delta_\varepsilon
      \: .
    \end{align*}
    Thus,
    \begin{align*}
      P((X, Y) \in B_\varepsilon)
      &\le \frac{1}{\delta_\varepsilon} \mathbb{E}\left[ e^{-X}/2 + e^{-Y}/2 - e^{-(X + Y)/2}
      \right]
      \: .
    \end{align*}
    For $n, m \ge N$ large enough so that we can apply the first inequality of this proof with
    $\delta = \varepsilon \delta_\varepsilon$, we deduce that
    \begin{align*}
      \mathbb{E}\left[\left\vert e^{-g_n} - e^{-g_m} \right\vert\right]
      &\le \varepsilon + 2 e^{-1/\varepsilon} + \frac{2}{\delta_\varepsilon} \mathbb{E}\left[
      e^{-g_n}/2 + e^{-g_m}/2 - e^{-(g_n + g_m)/2} \right] \\
      &\le \varepsilon + 2 e^{-1/\varepsilon} + 2 \varepsilon
      \: .
    \end{align*}
    As $\varepsilon$ is arbitrary, we deduce that $(e^{-g_n})_{n\in\mathbb{N}}$ is a Cauchy sequence
    in $L^1$ and thus converges in $L^1$ to some random variable $h$.
    Therefore, it has a subsequence $(e^{-g_{n_k}})_{k\in\mathbb{N}}$ converging almost surely to
    $h$.
    Finally, the subsequence of $g_n$ converges almost surely to $g = -\log(h)$. -/)
  (proofUses := ["lem:komlos_convex"])
  (latexEnv := "lemma")]
lemma komlos_ennreal (X : ℕ → Ω → ℝ≥0∞) (hX : ∀ n, Measurable (X n))
    {P : Measure Ω} [IsProbabilityMeasure P] :
    ∃ (Y : ℕ → Ω → ℝ≥0∞) (Y_lim : Ω → ℝ≥0∞),
      (∀ n, Y n ∈ convexHull ℝ≥0∞ (Set.range fun m ↦ X (n + m))) ∧ Measurable Y_lim ∧
      ∀ᵐ ω ∂P, Tendsto (Y · ω) atTop (𝓝 (Y_lim ω)) :=
  sorry
