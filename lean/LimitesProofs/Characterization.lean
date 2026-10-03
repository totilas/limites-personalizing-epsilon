import LimitesProofs.PublicPrivate
import LimitesProofs.GeneralCase

/-!
# Exact characterizations of the two risks

* `capped_feasible`, `capped_weights` — Lemma `lem:reduction`, Part 1 (capped weights):
  `𝓡_pers(u; A, B) = inf_{τ>0} (A q_τ + B)/s_τ²`, each value attained by the weights
  `min{uᵢ, τ}/s_τ` with noise level `1/s_τ`.
* `threshold_vs_affine` — Lemma `lem:threshold-vs-affine-sectionX`, as stated (for every
  cap `τ`), derived from the pointwise bounds of `GeneralCase`.
* `threshold_characterization` — Lemma `clm:threshold_characterization`, second
  equality of Eq. `eq:mseafftedious` (the first one is in `MeanEstimation`).
* `thrRisk_eq_min_levels` — Section `sec:learning-formal`: "an optimal `t` can be
  chosen among the distinct effective budgets".
* `public_thrRisk_eq`, `public_persRisk_eq` — the two risks in the public-private
  regime (proof of Thm. `thm:public-data-factor-2`): `𝓡_thr = min{T₁, A/n₂}` and
  `𝓡_pers = ab/(a+b)`.
* `public_factor_two_tight` — "This bound is tight": the ratio approaches 2.
* `public_example` — the ratio `≈ 1.95` for `ε₁ = 0.001`, `n₁ = 10⁴`, `n₂ = 12`.
* `two_level_example` — Example `ex:two-level` (Appendix `app:example`).
* `cap_objective_hasDerivAt`, `cap_objective_ge_stationary`,
  `cap_objective_antitone`, `cap_objective_monotone` — the closed form for the
  optimal cap (proof of Prop. `prop:affine-gradient-formal`).
-/

open Finset Filter Topology

namespace Limites

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Lemma `lem:reduction`, Part 1 (capped weights) -/

/-- Capped budget `min{uᵢ, τ}` (`= τ` for a public record). -/
noncomputable def cap (pub : Finset ι) (u : ι → ℝ) (τ : ℝ) (i : ι) : ℝ :=
  if i ∈ pub then τ else min (u i) τ

/-- `s_τ = ∑ᵢ min{uᵢ, τ}`. -/
noncomputable def capS (pub : Finset ι) (u : ι → ℝ) (τ : ℝ) : ℝ := ∑ i, cap pub u τ i

/-- `q_τ = ∑ᵢ min{uᵢ, τ}²`. -/
noncomputable def capQ (pub : Finset ι) (u : ι → ℝ) (τ : ℝ) : ℝ := ∑ i, cap pub u τ i ^ 2

/-- The values `(A q_τ + B)/s_τ²`, `τ > 0`. -/
def capSet (pub : Finset ι) (u : ι → ℝ) (A B : ℝ) : Set ℝ :=
  {r | ∃ τ, 0 < τ ∧ (A * capQ pub u τ + B) / capS pub u τ ^ 2 = r}

section Capped

variable {pub : Finset ι} {u : ι → ℝ}

omit [Fintype ι] in
lemma cap_pos (hu : ∀ i ∉ pub, 0 < u i) {τ : ℝ} (hτ : 0 < τ) (i : ι) : 0 < cap pub u τ i := by
  unfold cap
  split_ifs with h
  · exact hτ
  · exact lt_min (hu i h) hτ

lemma capS_pos [Nonempty ι] (hu : ∀ i ∉ pub, 0 < u i) {τ : ℝ} (hτ : 0 < τ) :
    0 < capS pub u τ :=
  sum_pos (fun i _ => cap_pos hu hτ i) univ_nonempty

lemma capQ_nonneg (τ : ℝ) : 0 ≤ capQ pub u τ := sum_nonneg fun _ _ => sq_nonneg _

/-- **Lemma `lem:reduction`, Part 1, attainment.**  For each `τ > 0` the weights
`wᵢ = min{uᵢ, τ}/s_τ` with noise level `1/s_τ` are feasible and have objective
`(A q_τ + B)/s_τ²`. -/
theorem capped_feasible [Nonempty ι] (hu : ∀ i ∉ pub, 0 < u i) (A B : ℝ) {τ : ℝ}
    (hτ : 0 < τ) :
    Feasible pub u (fun i => cap pub u τ i / capS pub u τ) (1 / capS pub u τ) ∧
      persObj A B (fun i => cap pub u τ i / capS pub u τ) (1 / capS pub u τ)
        = (A * capQ pub u τ + B) / capS pub u τ ^ 2 := by
  have hs := capS_pos hu hτ
  refine ⟨⟨fun i => (div_pos (cap_pos hu hτ i) hs).le, ?_, by positivity, fun i hi => ?_⟩, ?_⟩
  · rw [← sum_div]
    exact div_self hs.ne'
  · have hle : cap pub u τ i ≤ u i := by simp [cap, hi]
    calc cap pub u τ i / capS pub u τ = 1 / capS pub u τ * cap pub u τ i := by ring
      _ ≤ 1 / capS pub u τ * u i := mul_le_mul_of_nonneg_left hle (by positivity)
  · have hq : ∑ i, (cap pub u τ i / capS pub u τ) ^ 2 = capQ pub u τ / capS pub u τ ^ 2 := by
      simp only [div_pow]
      rw [← sum_div]
      rfl
    unfold persObj
    rw [hq]
    field_simp

/-- Water-filling: every feasible `(w, M)` with `M > 0` is dominated by a capped
mechanism. -/
lemma exists_cap_le (hu : ∀ i ∉ pub, 0 < u i) {A B : ℝ} (hA : 0 ≤ A)
    {w : ι → ℝ} {M : ℝ} (hf : Feasible pub u w M) (hM : 0 < M) :
    ∃ τ, 0 < τ ∧ (A * capQ pub u τ + B) / capS pub u τ ^ 2 ≤ persObj A B w M := by
  obtain ⟨hw, hsum, -, hMu⟩ := hf
  set g : ℝ → ℝ := fun b => ∑ i, (if i ∈ pub then b else min (M * u i) b) with hg
  have hg_cont : Continuous g :=
    continuous_finsetSum _ fun i _ =>
      continuous_if_const _ (fun _ => continuous_id) (fun _ => continuous_const.min continuous_id)
  have hg0 : g 0 = 0 := by
    refine sum_eq_zero fun i _ => ?_
    split_ifs with h
    · rfl
    · exact min_eq_right (mul_nonneg hM.le (hu i h).le)
  have hw1 : ∀ i, w i ≤ 1 := fun i => by
    have := single_le_sum (fun j _ => hw j) (mem_univ i)
    rwa [hsum] at this
  set b₁ : ℝ := 1 + ∑ i ∈ univ.filter (· ∉ pub), M * u i
  have hb₁ : 1 ≤ b₁ := by
    have : 0 ≤ ∑ i ∈ univ.filter (· ∉ pub), M * u i :=
      sum_nonneg fun i hi => mul_nonneg hM.le (hu i (mem_filter.mp hi).2).le
    linarith
  have hg1 : 1 ≤ g b₁ := by
    rw [← hsum, hg]
    refine sum_le_sum fun i _ => ?_
    split_ifs with h
    · linarith [hw1 i]
    · exact le_min (hMu i h) (by linarith [hw1 i])
  obtain ⟨b₀, hb₀mem, hgb₀⟩ :=
    intermediate_value_Icc (by linarith : (0:ℝ) ≤ b₁) hg_cont.continuousOn
      ⟨by rw [hg0]; norm_num, hg1⟩
  have hb₀ : 0 < b₀ := by
    rcases hb₀mem.1.lt_or_eq with h | h
    · exact h
    · rw [← h, hg0] at hgb₀; norm_num at hgb₀
  set τ := b₀ / M with hτ_def
  refine ⟨τ, div_pos hb₀ hM, ?_⟩
  have hcap : ∀ i, M * cap pub u τ i = if i ∈ pub then b₀ else min (M * u i) b₀ := by
    intro i
    unfold cap
    split_ifs
    · rw [hτ_def]; field_simp
    · rw [mul_min_of_nonneg _ _ hM.le, hτ_def]
      congr 1
      field_simp
  set w' : ι → ℝ := fun i => M * cap pub u τ i with hw'
  have hsum' : ∑ i, w' i = 1 := by
    rw [← hgb₀, hg]
    exact sum_congr rfl fun i _ => hcap i
  have hS : capS pub u τ = 1 / M := by
    have : M * capS pub u τ = 1 := by
      unfold capS
      rw [mul_sum]
      exact hsum'
    field_simp
    linarith
  have hQ : capQ pub u τ = (∑ i, w' i ^ 2) / M ^ 2 := by
    unfold capQ
    rw [eq_div_iff (by positivity), sum_mul]
    exact sum_congr rfl fun i _ => by rw [hw']; ring
  have hval : (A * capQ pub u τ + B) / capS pub u τ ^ 2 = A * ∑ i, w' i ^ 2 + B * M ^ 2 := by
    rw [hS, hQ]
    field_simp
  -- first-order optimality of the water-filled weights
  have hfo : ∀ i, b₀ * (w i - w' i) ≤ w' i * (w i - w' i) := by
    intro i
    simp only [hw', hcap]
    split_ifs with h
    · exact le_rfl
    · rcases le_total (M * u i) b₀ with h' | h'
      · rw [min_eq_left h']
        nlinarith [hMu i h]
      · rw [min_eq_right h']
  have hcross : 0 ≤ ∑ i, w' i * (w i - w' i) := by
    have h1 : ∑ i, b₀ * (w i - w' i) = 0 := by
      rw [← mul_sum, sum_sub_distrib, hsum, hsum', sub_self, mul_zero]
    linarith [sum_le_sum fun i (_ : i ∈ univ) => hfo i]
  have hw'w : ∑ i, w' i ^ 2 ≤ ∑ i, w i ^ 2 := by
    have hexp : ∑ i, w i ^ 2
        = ∑ i, w' i ^ 2 + 2 * ∑ i, w' i * (w i - w' i) + ∑ i, (w i - w' i) ^ 2 := by
      rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun i _ => by ring
    have : 0 ≤ ∑ i, (w i - w' i) ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
    linarith
  rw [hval]
  unfold persObj
  nlinarith [mul_le_mul_of_nonneg_left hw'w hA]

/-- **Lemma `lem:reduction`, Part 1.**  `𝓡_pers(u; A, B) = inf_{τ>0} (A q_τ + B)/s_τ²`. -/
theorem capped_weights [Nonempty ι] (hu : ∀ i ∉ pub, 0 < u i) {A B : ℝ} (hA : 0 < A)
    (hB : 0 < B) :
    persRisk pub u A B = sInf (capSet pub u A B) := by
  have hbdd : BddBelow (capSet pub u A B) := ⟨0, by
    rintro _ ⟨τ, -, rfl⟩
    exact div_nonneg (by nlinarith [capQ_nonneg (pub := pub) (u := u) τ]) (sq_nonneg _)⟩
  apply le_antisymm
  · refine le_csInf ⟨_, 1, one_pos, rfl⟩ ?_
    rintro _ ⟨τ, hτ, rfl⟩
    obtain ⟨hf, he⟩ := capped_feasible hu A B hτ
    rw [← he]
    exact persRisk_le hA.le hB.le hf
  · obtain ⟨w₀, M₀, hf₀⟩ := feasible_nonempty hu
    refine le_csInf ⟨_, w₀, M₀, hf₀, rfl⟩ ?_
    rintro _ ⟨w, M, hf, rfl⟩
    have key : ∀ δ ∈ Set.Ioi (0:ℝ), sInf (capSet pub u A B) ≤ persObj A B w (M + δ) := by
      intro δ hδ
      obtain ⟨hw, hsum, hM0, hMu⟩ := hf
      have hδ' : (0:ℝ) < δ := hδ
      have hf' : Feasible pub u w (M + δ) :=
        ⟨hw, hsum, by linarith, fun i hi => (hMu i hi).trans (by nlinarith [hu i hi])⟩
      obtain ⟨τ, hτ, hle⟩ := exists_cap_le hu hA.le hf' (by linarith)
      exact (csInf_le hbdd ⟨τ, hτ, rfl⟩).trans hle
    have hcont : Tendsto (fun δ => persObj A B w (M + δ)) (𝓝[>] 0) (𝓝 (persObj A B w M)) := by
      have : Continuous fun δ => persObj A B w (M + δ) := by
        unfold persObj
        fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    exact ge_of_tendsto hcont (eventually_nhdsWithin_of_forall key)

end Capped

/-- **Lemma `lem:threshold-vs-affine-sectionX`.**  If the finite budgets take at most
`m` distinct values, then for every `τ > 0` there is a threshold `ε* > 0` (retaining at
least one record) with
`𝓡_thr ≤ A/n_{ε*} + B/(ε* n_{ε*})² ≤ min{m², H_n²} · (A q_τ + B)/s_τ²`. -/
theorem threshold_vs_affine [Nonempty ι] (u : ι → ℝ) (hu : ∀ i, 0 < u i) {m : ℕ}
    (hm : #(univ.image u) ≤ m) {A B : ℝ} (hA : 0 < A) (hB : 0 < B) {τ : ℝ} (hτ : 0 < τ) :
    ∃ ε, 0 < ε ∧ 0 < nThr ∅ u ε ∧ thrRisk ∅ u A B ≤ thrObj A B ε (nThr ∅ u ε) ∧
      thrObj A B ε (nThr ∅ u ε)
        ≤ min ((m : ℝ) ^ 2) ((harmonic (Fintype.card ι) : ℝ) ^ 2)
            * ((A * capQ ∅ u τ + B) / capS ∅ u τ ^ 2) := by
  obtain ⟨hf, hval⟩ := capped_feasible (pub := ∅) (u := u) (fun i _ => hu i) A B hτ
  rw [← hval]
  have hm' : ((#(univ.image u) : ℕ) : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hm) 2
  have hf0 := persObj_nonneg hA.le hB.le (fun i => cap ∅ u τ i / capS ∅ u τ) (1 / capS ∅ u τ)
  rcases le_total ((m : ℝ) ^ 2) ((harmonic (Fintype.card ι) : ℝ) ^ 2) with h | h
  · obtain ⟨v, hv, hle⟩ := direct_factor_m_sq u hu hA hB hf
    obtain ⟨i, -, rfl⟩ := mem_image.mp hv
    have hN : 0 < nThr ∅ u (u i) := card_pos.mpr ⟨i, by simp⟩
    refine ⟨u i, hu i, hN, thrRisk_le hA.le hB.le (hu i) hN, ?_⟩
    rw [min_eq_left h]
    exact hle.trans (mul_le_mul_of_nonneg_right hm' hf0)
  · obtain ⟨t, ht, hN, hle⟩ := direct_factor_harmonic u hA hB hf
    refine ⟨t, ht, hN, thrRisk_le hA.le hB.le ht hN, ?_⟩
    rwa [min_eq_right h]

/-- **Lemma `clm:threshold_characterization`**, second equality of
Eq. `eq:mseafftedious`: with finite budgets `ε`,
`MSE_aff(ε) = inf_{τ>0} (q_τ/(4 s_τ²) + 2/s_τ²)`, attained for each `τ` by the
weights `min{εᵢ, τ}/s_τ` and the noise scale `1/s_τ` (`capped_feasible`). -/
theorem threshold_characterization [Nonempty ι] (ε : ι → ℝ) (hε : ∀ i, 0 < ε i) :
    persRisk ∅ ε (1/4) 2
      = sInf {r | ∃ τ, 0 < τ ∧ capQ ∅ ε τ / (4 * capS ∅ ε τ ^ 2) + 2 / capS ∅ ε τ ^ 2 = r} := by
  rw [capped_weights (fun i _ => hε i) (by norm_num) (by norm_num)]
  congr 1
  ext r
  simp only [capSet, Set.mem_ofPred_eq]
  constructor <;> rintro ⟨τ, hτ, rfl⟩ <;> exact ⟨τ, hτ, by ring⟩

omit [Fintype ι] in
lemma cap_empty (u : ι → ℝ) (τ : ℝ) (i : ι) : cap ∅ u τ i = min (u i) τ := by
  simp [cap]

/-! ## The threshold risk is attained at a budget level -/

/-- **Section `sec:learning-formal`** ("an optimal `t` can be chosen among the
distinct effective budgets"): with finite positive budgets, `𝓡_thr` is the minimum
of the threshold objective over the budget values. -/
theorem thrRisk_eq_min_levels [Nonempty ι] (u : ι → ℝ) (hu : ∀ i, 0 < u i) {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B) :
    ∃ v ∈ univ.image u, thrRisk ∅ u A B = thrObj A B v (nThr ∅ u v) ∧
      ∀ v' ∈ univ.image u, thrObj A B v (nThr ∅ u v) ≤ thrObj A B v' (nThr ∅ u v') := by
  obtain ⟨v, hv, hmin⟩ :=
    (univ.image u).exists_min_image (fun v => thrObj A B v (nThr ∅ u v)) (univ_nonempty.image u)
  refine ⟨v, hv, le_antisymm ?_ ?_, hmin⟩
  · obtain ⟨i, -, rfl⟩ := mem_image.mp hv
    exact thrRisk_le hA.le hB.le (hu i) (card_pos.mpr ⟨i, by simp⟩)
  · obtain ⟨i₀⟩ := ‹Nonempty ι›
    refine le_thrRisk ⟨u i₀, hu i₀, card_pos.mpr ⟨i₀, by simp⟩⟩ fun t ht hN => ?_
    have hR : (univ.filter fun i => i ∈ (∅ : Finset ι) ∨ t ≤ u i).Nonempty := card_pos.mp hN
    obtain ⟨j, hjR, hjmin⟩ :=
      (univ.filter fun i => i ∈ (∅ : Finset ι) ∨ t ≤ u i).exists_min_image u hR
    have htj : t ≤ u j := by simpa using hjR
    have hNeq : nThr ∅ u (u j) = nThr ∅ u t := by
      unfold nThr
      congr 1
      ext i
      simp only [mem_filter, mem_univ, true_and, notMem_empty, false_or]
      exact ⟨fun h => htj.trans h, fun h => hjmin i (by simp [h])⟩
    have hNpos : (0:ℝ) < nThr ∅ u t := Nat.cast_pos.mpr hN
    calc thrObj A B v (nThr ∅ u v) ≤ thrObj A B (u j) (nThr ∅ u (u j)) :=
          hmin (u j) (mem_image_of_mem u (mem_univ j))
      _ ≤ thrObj A B t (nThr ∅ u t) := by
          rw [hNeq]
          unfold thrObj
          have : B / (u j * nThr ∅ u t) ^ 2 ≤ B / (t * nThr ∅ u t) ^ 2 :=
            div_le_div_of_nonneg_left hB.le (by positivity)
              (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right htj hNpos.le) 2)
          linarith

/-! ## The public-private regime (proof of Thm. `thm:public-data-factor-2`) -/

section Public

variable (pub : Finset ι) (u : ι → ℝ) (ε₁ : ℝ) {A B : ℝ}

/-- `𝓡_thr = min{T₁, A/n₂}`: the threshold at `ε₁` keeping all `n` records, or the
public records alone (an infimum over `t → ∞`). -/
theorem public_thrRisk_eq (hε₁ : 0 < ε₁) (hA : 0 < A) (hB : 0 < B) (hpub : pub.Nonempty)
    (hu : ∀ i ∉ pub, u i = ε₁) :
    thrRisk pub u A B = min (thrObj A B ε₁ (Fintype.card ι)) (A / #pub) := by
  have hall : ∀ t, t ≤ ε₁ → nThr pub u t = Fintype.card ι := by
    intro t ht
    unfold nThr
    rw [filter_true_of_mem, card_univ]
    intro i _
    by_cases hi : i ∈ pub
    · exact Or.inl hi
    · exact Or.inr (by rw [hu i hi]; exact ht)
  have hpubonly : ∀ t, ε₁ < t → nThr pub u t = #pub := by
    intro t ht
    unfold nThr
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and, or_iff_left_iff_imp]
    intro hti
    by_contra hi
    rw [hu i hi] at hti
    linarith
  have hn : (0:ℝ) < Fintype.card ι := by
    have : Nonempty ι := ⟨hpub.choose⟩
    exact_mod_cast Fintype.card_pos
  apply le_antisymm
  · refine le_min ?_ (thrRisk_le_public pub u hA hB hpub)
    have := thrRisk_le (pub := pub) (u := u) hA.le hB.le hε₁
      (by rw [hall ε₁ le_rfl]; exact_mod_cast hn)
    rwa [hall ε₁ le_rfl] at this
  · refine le_thrRisk ⟨ε₁, hε₁, by rw [hall ε₁ le_rfl]; exact_mod_cast hn⟩ fun t ht hN => ?_
    rcases le_or_gt t ε₁ with h | h
    · refine (min_le_left _ _).trans ?_
      rw [hall t h]
      unfold thrObj
      have : B / (ε₁ * (Fintype.card ι : ℝ)) ^ 2 ≤ B / (t * (Fintype.card ι : ℝ)) ^ 2 :=
        div_le_div_of_nonneg_left hB.le (by positivity)
          (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right h hn.le) 2)
      linarith
    · refine (min_le_right _ _).trans ?_
      rw [hpubonly t h]
      unfold thrObj
      have : 0 ≤ B / (t * (#pub : ℝ)) ^ 2 := by positivity
      linarith

/-- `𝓡_pers = ab/(a+b)` with `a = A/n₁ + B/(ε₁ n₁)²` and `b = A/n₂`: the best
affine estimator is the optimal combination of the private and public means. -/
theorem public_persRisk_eq (hε₁ : 0 < ε₁) (hA : 0 < A) (hB : 0 < B) (hpub : pub.Nonempty)
    (hpriv : pubᶜ.Nonempty) (hu : ∀ i ∉ pub, u i = ε₁) :
    persRisk pub u A B
      = (A / #pubᶜ + B / (ε₁ * #pubᶜ) ^ 2) * (A / #pub)
        / ((A / #pubᶜ + B / (ε₁ * #pubᶜ) ^ 2) + A / #pub) := by
  have : Nonempty ι := ⟨hpub.choose⟩
  set n₁ : ℝ := (#pubᶜ : ℝ) with hn₁
  set n₂ : ℝ := (#pub : ℝ) with hn₂
  have hn₁pos : 0 < n₁ := by rw [hn₁]; exact_mod_cast card_pos.mpr hpriv
  have hn₂pos : 0 < n₂ := by rw [hn₂]; exact_mod_cast card_pos.mpr hpub
  set a : ℝ := A / n₁ + B / (ε₁ * n₁) ^ 2 with ha
  set b : ℝ := A / n₂ with hb
  have hapos : 0 < a := by positivity
  have hbpos : 0 < b := by positivity
  apply le_antisymm
  · -- the optimal mixture W₁ = b/(a+b)
    set W₁ := b / (a + b) with hW₁
    set W₂ := a / (a + b) with hW₂
    set w : ι → ℝ := fun i => if i ∈ pub then W₂ / n₂ else W₁ / n₁ with hw
    have hsum : ∑ i, w i = 1 := by
      rw [← sum_add_sum_compl pub w]
      rw [sum_congr rfl fun i hi => (if_pos hi : w i = W₂ / n₂),
        sum_congr rfl fun i hi => (if_neg (mem_compl.mp hi) : w i = W₁ / n₁)]
      rw [sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul, ← hn₁, ← hn₂, hW₁, hW₂]
      field_simp
    have hf : Feasible pub u w (W₁ / (n₁ * ε₁)) := by
      refine ⟨fun i => by simp only [hw]; split_ifs <;> positivity, hsum, by positivity,
        fun i hi => le_of_eq ?_⟩
      simp only [hw, if_neg hi, hu i hi]
      field_simp
    have hsq : ∑ i, w i ^ 2 = n₂ * (W₂ / n₂) ^ 2 + n₁ * (W₁ / n₁) ^ 2 := by
      rw [← sum_add_sum_compl pub (fun i => w i ^ 2)]
      rw [sum_congr rfl fun i hi => (by simp [hw, hi] : w i ^ 2 = (W₂ / n₂) ^ 2),
        sum_congr rfl fun i hi => (by simp [hw, mem_compl.mp hi] : w i ^ 2 = (W₁ / n₁) ^ 2)]
      rw [sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul, ← hn₁, ← hn₂]
    calc persRisk pub u A B ≤ persObj A B w (W₁ / (n₁ * ε₁)) := persRisk_le hA.le hB.le hf
      _ = W₁ ^ 2 * a + W₂ ^ 2 * b := by
          unfold persObj
          rw [hsq, ha, hb]
          field_simp
          ring
      _ = a * b / (a + b) := by
          rw [hW₁, hW₂]
          field_simp
          ring
  · obtain ⟨w₀, M₀, hf₀⟩ := feasible_nonempty (pub := pub) (u := u)
      (fun i hi => (hu i hi).symm ▸ hε₁)
    refine le_csInf ⟨_, w₀, M₀, hf₀, rfl⟩ ?_
    rintro _ ⟨w, M, ⟨hw, hsum, -, hM⟩, rfl⟩
    have hmix := mixture_le_persObj pubᶜ pub disjoint_compl_left (by rw [union_comm, union_compl])
      ε₁ A B hε₁ hA hB hpriv hpub w hw M fun i hi => by
        have := hM i (mem_compl.mp hi)
        rwa [hu i (mem_compl.mp hi)] at this
    have hsplit : (∑ i ∈ pubᶜ, w i) + ∑ i ∈ pub, w i = 1 := by
      rw [add_comm, sum_add_sum_compl, hsum]
    exact (harmonic_le_mixture a b _ _ hapos hbpos hsplit).trans hmix

end Public

/-- The public-private instance with `n₁` private records (left) and `n₂` public
records (right). -/
def pubOf (n₁ n₂ : ℕ) : Finset (Fin n₁ ⊕ Fin n₂) := univ.map Function.Embedding.inr

lemma pubOf_card (n₁ n₂ : ℕ) : #(pubOf n₁ n₂) = n₂ := by simp [pubOf]

lemma pubOf_compl (n₁ n₂ : ℕ) : (pubOf n₁ n₂)ᶜ = univ.map Function.Embedding.inl := by
  ext x
  cases x <;> simp [pubOf]

lemma pubOf_compl_card (n₁ n₂ : ℕ) : #(pubOf n₁ n₂)ᶜ = n₁ := by
  rw [pubOf_compl]; simp

/-- Exact ratio `𝓡_thr/𝓡_pers` in the public-private instance, from
`public_thrRisk_eq` and `public_persRisk_eq`. -/
lemma pubOf_risks (n₁ n₂ : ℕ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) {ε₁ A B : ℝ} (hε₁ : 0 < ε₁)
    (hA : 0 < A) (hB : 0 < B) :
    thrRisk (pubOf n₁ n₂) (fun _ => ε₁) A B
        = min (thrObj A B ε₁ (n₁ + n₂ : ℕ)) (A / n₂) ∧
      persRisk (pubOf n₁ n₂) (fun _ => ε₁) A B
        = (A / n₁ + B / (ε₁ * n₁) ^ 2) * (A / n₂) / ((A / n₁ + B / (ε₁ * n₁) ^ 2) + A / n₂) := by
  have hpub : (pubOf n₁ n₂).Nonempty := card_pos.mp (by rw [pubOf_card]; exact hn₂)
  have hpriv : (pubOf n₁ n₂)ᶜ.Nonempty := card_pos.mp (by rw [pubOf_compl_card]; exact hn₁)
  constructor
  · rw [public_thrRisk_eq _ _ ε₁ hε₁ hA hB hpub (fun _ _ => rfl), pubOf_card]
    simp
  · rw [public_persRisk_eq _ _ ε₁ hε₁ hA hB hpub hpriv (fun _ _ => rfl), pubOf_card,
      pubOf_compl_card]

/-- **Tightness of Thm. `thm:public-data-factor-2`** ("This bound is tight and can be
approached"): for every `A, B > 0` and `δ > 0` there is a public-private instance
with `𝓡_thr ≥ (2 − δ) 𝓡_pers`.  The instance takes `n₂ = N`, `n₁ = N²` and `ε₁`
with `A/n₁ + B/(n₁ε₁)² = A/n₂`, i.e. the balance condition
`n₂ = n₁/(1 + 8/(n₁ε₁²))` at `A = 1/4`, `B = 2`. -/
theorem public_factor_two_tight {A B : ℝ} (hA : 0 < A) (hB : 0 < B) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n₁ n₂ : ℕ, ∃ ε₁ : ℝ, 0 < n₁ ∧ 0 < n₂ ∧ 0 < ε₁ ∧
      (2 - δ) * persRisk (pubOf n₁ n₂) (fun _ => ε₁) A B
        ≤ thrRisk (pubOf n₁ n₂) (fun _ => ε₁) A B := by
  set N : ℕ := ⌈4 / δ⌉₊ + 1 with hN_def
  have hceil : (1:ℝ) ≤ ⌈4 / δ⌉₊ := by exact_mod_cast Nat.ceil_pos.mpr (by positivity)
  have hN2 : (2:ℝ) ≤ N := by rw [hN_def]; push_cast; linarith
  have hNδ : 4 / δ ≤ N + 1 := by
    rw [hN_def]; push_cast; linarith [Nat.le_ceil (4 / δ)]
  have hNpos : (0:ℝ) < N := by linarith
  have hNN : (N:ℝ) < N ^ 2 := by nlinarith
  -- ε₁ balancing the all-private and all-public risks
  set c : ℝ := A / N - A / N ^ 2 with hc
  have hcpos : 0 < c := sub_pos.mpr (div_lt_div_of_pos_left hA hNpos hNN)
  set ε₁ : ℝ := Real.sqrt (B / (N ^ 4 * c)) with hε₁_def
  have hε₁ : 0 < ε₁ := Real.sqrt_pos.mpr (by positivity)
  have hε₁sq : ε₁ ^ 2 = B / (N ^ 4 * c) := Real.sq_sqrt (by positivity)
  refine ⟨N ^ 2, N, ε₁, by positivity, by omega, hε₁, ?_⟩
  obtain ⟨hthr, hpers⟩ := pubOf_risks (N ^ 2) N (by positivity) (by omega) hε₁ hA hB
  rw [hthr, hpers]
  push_cast
  have hab : A / (N:ℝ) ^ 2 + B / (ε₁ * (N:ℝ) ^ 2) ^ 2 = A / N := by
    rw [mul_pow, ← pow_mul, hε₁sq, hc]
    field_simp
    ring
  rw [hab]
  have hpers' : A / N * (A / N) / (A / N + A / N) = A / N / 2 := by field_simp; ring
  rw [hpers']
  -- both thresholds are at least ρ² A/N with ρ = N/(N+1)
  set ρ : ℝ := (N:ℝ) / (N + 1) with hρ
  have hρ' : ρ = 1 - 1 / ((N:ℝ) + 1) := by rw [hρ]; field_simp; ring
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ ≤ 1 := by rw [hρ']; have : 0 ≤ 1 / ((N:ℝ) + 1) := by positivity
                         linarith
  have hρsq : 1 - δ / 2 ≤ ρ ^ 2 := by
    have h1 : 1 - 2 / ((N:ℝ) + 1) ≤ ρ ^ 2 := by
      rw [hρ']
      have e : 2 / ((N:ℝ) + 1) = 2 * (1 / ((N:ℝ) + 1)) := by ring
      rw [e]
      nlinarith [sq_nonneg (1 / ((N:ℝ) + 1))]
    have h2 : 2 / ((N:ℝ) + 1) ≤ δ / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have := (div_le_iff₀ hδ).mp hNδ
      linarith
    linarith
  have hT1 : ρ ^ 2 * (A / N) ≤ thrObj A B ε₁ ((N:ℝ) ^ 2 + N) := by
    unfold thrObj
    rw [← hab, mul_add]
    have e1 : ρ ^ 2 * (A / (N:ℝ) ^ 2) = A / ((N:ℝ) + 1) ^ 2 := by rw [hρ]; field_simp
    have e2 : ρ ^ 2 * (B / (ε₁ * (N:ℝ) ^ 2) ^ 2) = B / (ε₁ * ((N:ℝ) ^ 2 + N)) ^ 2 := by
      rw [hρ]; field_simp
    rw [e1, e2]
    have : A / ((N:ℝ) + 1) ^ 2 ≤ A / ((N:ℝ) ^ 2 + N) :=
      div_le_div_of_nonneg_left hA.le (by positivity) (by nlinarith)
    linarith
  have hT2 : ρ ^ 2 * (A / N) ≤ A / N := by
    have : ρ ^ 2 ≤ 1 := by nlinarith
    exact mul_le_of_le_one_left (div_pos hA hNpos).le this
  have hAN : 0 ≤ A / N := (div_pos hA hNpos).le
  calc (2 - δ) * (A / N / 2) = (1 - δ / 2) * (A / N) := by ring
    _ ≤ ρ ^ 2 * (A / N) := mul_le_mul_of_nonneg_right hρsq hAN
    _ ≤ _ := le_min hT1 hT2

/-- **The numerical claim after Thm. `thm:public-data-factor-2`**: for `ε₁ = 0.001`,
`n₁ = 10⁴`, `n₂ = 12` (mean estimation, `A = 1/4`, `B = 2`) the ratio
`MSE_thr/MSE_aff` is close to `1.95`: it lies in `(1.95, 1.96)`. -/
theorem public_example :
    1.95 * persRisk (pubOf 10000 12) (fun _ => (1/1000 : ℝ)) (1/4) 2
        < thrRisk (pubOf 10000 12) (fun _ => (1/1000 : ℝ)) (1/4) 2 ∧
      thrRisk (pubOf 10000 12) (fun _ => (1/1000 : ℝ)) (1/4) 2
        < 1.96 * persRisk (pubOf 10000 12) (fun _ => (1/1000 : ℝ)) (1/4) 2 := by
  obtain ⟨hthr, hpers⟩ := pubOf_risks 10000 12 (by norm_num) (by norm_num)
    (by norm_num : (0:ℝ) < 1/1000) (by norm_num : (0:ℝ) < 1/4) (by norm_num : (0:ℝ) < 2)
  rw [hthr, hpers]
  unfold thrObj
  norm_num [min_def]

/-! ## Example `ex:two-level` (Appendix `app:example`) -/

/-- The two-level profile: 57 records of budget `1/20` (left) and 7 of budget `1/2`
(right). -/
noncomputable def exBudget : Fin 57 ⊕ Fin 7 → ℝ := Sum.elim (fun _ => 1/20) (fun _ => 1/2)

lemma ex_nThr (t : ℝ) :
    nThr ∅ exBudget t = (if t ≤ 1/20 then 57 else 0) + (if t ≤ 1/2 then 7 else 0) := by
  unfold nThr
  rw [card_filter, Fintype.sum_sum_type]
  simp [exBudget]

lemma ex_capS (τ : ℝ) : capS ∅ exBudget τ = 57 * min (1/20) τ + 7 * min (1/2) τ := by
  unfold capS
  rw [Fintype.sum_sum_type]
  simp [cap_empty, exBudget]

lemma ex_capQ (τ : ℝ) : capQ ∅ exBudget τ = 57 * min (1/20) τ ^ 2 + 7 * min (1/2) τ ^ 2 := by
  unfold capQ
  rw [Fintype.sum_sum_type]
  simp [cap_empty, exBudget]

/-- **Example `ex:two-level`.**  For `n₁ = 57`, `n₂ = 7`, `ε₁ = 1/20`, `ε₂ = 1/2`:
`MSE_thr = 39/196`, `MSE_aff = 3957/64516` (attained at `τ = 1/2`), and the ratio is
`209677/64631 > 3.24`. -/
theorem two_level_example :
    thrRisk ∅ exBudget (1/4) 2 = 39 / 196 ∧ persRisk ∅ exBudget (1/4) 2 = 3957 / 64516 ∧
      thrRisk ∅ exBudget (1/4) 2 / persRisk ∅ exBudget (1/4) 2 = 209677 / 64631 ∧
      (3.24 : ℝ) < 209677 / 64631 := by
  have hthr : thrRisk ∅ exBudget (1/4) 2 = 39 / 196 := by
    apply le_antisymm
    · have h := thrRisk_le (pub := ∅) (u := exBudget) (A := 1/4) (B := 2) (by norm_num)
        (by norm_num) (by norm_num : (0:ℝ) < 1/2) (by rw [ex_nThr]; norm_num)
      rw [ex_nThr] at h
      unfold thrObj at h
      norm_num at h
      linarith
    · refine le_thrRisk ⟨1/2, by norm_num, by rw [ex_nThr]; norm_num⟩ fun t ht hN => ?_
      rw [ex_nThr] at hN ⊢
      unfold thrObj
      by_cases h1 : t ≤ 1/20
      · have h2 : t ≤ 1/2 := by linarith
        simp only [h1, h2, if_true]
        norm_num
        rw [div_add_div _ _ (by norm_num) (by positivity), le_div_iff₀ (by positivity)]
        nlinarith
      · by_cases h2 : t ≤ 1/2
        · simp only [h1, h2, if_true, if_false]
          norm_num
          rw [div_add_div _ _ (by norm_num) (by positivity), le_div_iff₀ (by positivity)]
          nlinarith
        · rw [if_neg h1, if_neg h2] at hN
          simp at hN
  have hpers : persRisk ∅ exBudget (1/4) 2 = 3957 / 64516 := by
    rw [capped_weights (fun i _ => by cases i <;> simp [exBudget]) (by norm_num) (by norm_num)]
    apply le_antisymm
    · refine csInf_le ⟨0, ?_⟩ ⟨1/2, by norm_num, ?_⟩
      · rintro _ ⟨τ, -, rfl⟩
        have hq := capQ_nonneg (pub := (∅ : Finset (Fin 57 ⊕ Fin 7))) (u := exBudget) τ
        exact div_nonneg (by linarith) (sq_nonneg _)
      · rw [ex_capS, ex_capQ]
        norm_num [min_def]
    · refine le_csInf ⟨_, 1, one_pos, rfl⟩ ?_
      rintro _ ⟨τ, hτ, rfl⟩
      rw [ex_capS, ex_capQ]
      rw [le_div_iff₀ (by positivity)]
      rcases le_total τ (1/20) with h1 | h1
      · rw [min_eq_right h1, min_eq_right (by linarith : τ ≤ 1/2)]
        nlinarith
      · rw [min_eq_left h1]
        rcases le_total τ (1/2) with h2 | h2
        · rw [min_eq_right h2]
          nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]
        · rw [min_eq_left h2]
          norm_num
  refine ⟨hthr, hpers, ?_, by norm_num⟩
  rw [hthr, hpers]
  norm_num

/-! ## The optimal cap in closed form (proof of Prop. `prop:affine-gradient-formal`)

On an interval of `τ` where the set `L_τ = {i : uᵢ < τ}` is constant, with
`k = n − |L_τ|`, `A₁ = ∑_{L_τ} uᵢ`, `A₂ = ∑_{L_τ} uᵢ²`, the objective is
`h(τ) = (V (A₂ + kτ²) + c)/(A₁ + kτ)²` (`c = 2dC²`).  It has a unique stationary
point `τ* = (A₂ + c/V)/A₁`, is decreasing before it and increasing after it. -/

/-- `h(τ) = (V (A₂ + kτ²) + c)/(A₁ + kτ)²`. -/
noncomputable def capObjective (V c A₁ A₂ k τ : ℝ) : ℝ :=
  (V * (A₂ + k * τ ^ 2) + c) / (A₁ + k * τ) ^ 2

/-- On such an interval, `s_τ = A₁ + kτ` and `q_τ = A₂ + kτ²`. -/
lemma capS_capQ_split (u : ι → ℝ) (τ : ℝ) :
    capS ∅ u τ = (∑ i ∈ univ.filter (fun i => u i < τ), u i)
        + (#(univ.filter fun i => ¬ u i < τ) : ℝ) * τ ∧
      capQ ∅ u τ = (∑ i ∈ univ.filter (fun i => u i < τ), u i ^ 2)
        + (#(univ.filter fun i => ¬ u i < τ) : ℝ) * τ ^ 2 := by
  constructor
  · unfold capS
    rw [← sum_filter_add_sum_filter_not univ (fun i => u i < τ)]
    congr 1
    · exact sum_congr rfl fun i hi => by
        rw [cap_empty, min_eq_left (mem_filter.mp hi).2.le]
    · rw [sum_congr rfl fun i hi => by
        rw [cap_empty, min_eq_right (not_lt.mp (mem_filter.mp hi).2)], sum_const, nsmul_eq_mul]
  · unfold capQ
    rw [← sum_filter_add_sum_filter_not univ (fun i => u i < τ)]
    congr 1
    · exact sum_congr rfl fun i hi => by
        rw [cap_empty, min_eq_left (mem_filter.mp hi).2.le]
    · rw [sum_congr rfl fun i hi => by
        rw [cap_empty, min_eq_right (not_lt.mp (mem_filter.mp hi).2)], sum_const, nsmul_eq_mul]

/-- The derivative of `h` has numerator `2 k s_τ [V (τ A₁ − A₂) − c]`. -/
theorem cap_objective_hasDerivAt (V c A₁ A₂ k τ : ℝ) (hs : A₁ + k * τ ≠ 0) :
    HasDerivAt (capObjective V c A₁ A₂ k)
      (2 * k * (A₁ + k * τ) * (V * (τ * A₁ - A₂) - c) / ((A₁ + k * τ) ^ 2) ^ 2) τ := by
  have hnum : HasDerivAt (fun τ => V * (A₂ + k * τ ^ 2) + c) (V * (k * (2 * τ))) τ := by
    have := ((hasDerivAt_pow 2 τ).const_mul k).const_add A₂ |>.const_mul V |>.add_const c
    simpa using this
  have hlin : HasDerivAt (fun τ => A₁ + k * τ) k τ := by
    simpa using ((hasDerivAt_id τ).const_mul k).const_add A₁
  have hden : HasDerivAt (fun τ => (A₁ + k * τ) ^ 2) (2 * (A₁ + k * τ) * k) τ :=
    (hlin.pow 2).congr_deriv (by norm_num)
  have h := hnum.div hden (pow_ne_zero 2 hs)
  have e : capObjective V c A₁ A₂ k = fun τ => (V * (A₂ + k * τ ^ 2) + c) / (A₁ + k * τ) ^ 2 :=
    rfl
  rw [e]
  exact h.congr_deriv (by congr 1; ring)

/-- `h = P/s² − Q/s + V/k` with `s = A₁ + kτ`, a quadratic in `1/s`. -/
lemma capObjective_quadratic (V c A₁ A₂ k τ : ℝ) (hk : 0 < k) (hs : A₁ + k * τ ≠ 0) :
    capObjective V c A₁ A₂ k τ
      = (V * A₂ + c + V * A₁ ^ 2 / k) * (1 / (A₁ + k * τ)) ^ 2
        - 2 * V * A₁ / k * (1 / (A₁ + k * τ)) + V / k := by
  unfold capObjective
  field_simp
  ring

/-- The stationary point `τ* = (A₂ + c/V)/A₁` is the minimizer of `h` over `s_τ > 0`. -/
theorem cap_objective_ge_stationary (V c A₁ A₂ k : ℝ) (hV : 0 < V) (hc : 0 ≤ c)
    (hA₁ : 0 < A₁) (hA₂ : 0 ≤ A₂) (hk : 0 < k) (τ : ℝ) (hs : 0 < A₁ + k * τ) :
    capObjective V c A₁ A₂ k ((A₂ + c / V) / A₁) ≤ capObjective V c A₁ A₂ k τ := by
  set τs := (A₂ + c / V) / A₁
  have hss : 0 < A₁ + k * τs := by positivity
  rw [capObjective_quadratic V c A₁ A₂ k τ hk hs.ne',
    capObjective_quadratic V c A₁ A₂ k τs hk hss.ne']
  set P := V * A₂ + c + V * A₁ ^ 2 / k
  have hP : 0 < P := by positivity
  have hx : 1 / (A₁ + k * τs) = (2 * V * A₁ / k) / (2 * P) := by
    simp only [τs, P]
    field_simp
    ring
  rw [hx]
  set x := 1 / (A₁ + k * τ)
  set Q := 2 * V * A₁ / k
  have : P * (Q / (2 * P)) ^ 2 - Q * (Q / (2 * P)) ≤ P * x ^ 2 - Q * x := by
    have e : P * x ^ 2 - Q * x - (P * (Q / (2 * P)) ^ 2 - Q * (Q / (2 * P)))
        = P * (x - Q / (2 * P)) ^ 2 := by field_simp; ring
    nlinarith [mul_nonneg hP.le (sq_nonneg (x - Q / (2 * P)))]
  linarith

/-- `h` is decreasing on `{τ : s_τ > 0, τ ≤ τ*}`. -/
theorem cap_objective_antitone (V c A₁ A₂ k : ℝ) (hV : 0 < V) (hc : 0 ≤ c)
    (hA₁ : 0 < A₁) (hA₂ : 0 ≤ A₂) (hk : 0 < k) {τ₁ τ₂ : ℝ} (hs₁ : 0 < A₁ + k * τ₁)
    (h₁₂ : τ₁ ≤ τ₂) (h₂ : τ₂ ≤ (A₂ + c / V) / A₁) :
    capObjective V c A₁ A₂ k τ₂ ≤ capObjective V c A₁ A₂ k τ₁ := by
  have hs₂ : 0 < A₁ + k * τ₂ := by nlinarith
  rw [capObjective_quadratic V c A₁ A₂ k τ₁ hk hs₁.ne',
    capObjective_quadratic V c A₁ A₂ k τ₂ hk hs₂.ne']
  set P := V * A₂ + c + V * A₁ ^ 2 / k
  have hP : 0 < P := by positivity
  set Q := 2 * V * A₁ / k
  set x₁ := 1 / (A₁ + k * τ₁)
  set x₂ := 1 / (A₁ + k * τ₂)
  have hx : x₂ ≤ x₁ := one_div_le_one_div_of_le hs₁ (by nlinarith)
  -- `x₂ ≥ 1/s_{τ*} = Q/(2P)`
  have hss : 0 < A₁ + k * ((A₂ + c / V) / A₁) := by positivity
  have hxs : Q / (2 * P) ≤ x₂ := by
    have e : 1 / (A₁ + k * ((A₂ + c / V) / A₁)) = Q / (2 * P) := by
      simp only [Q, P]; field_simp; ring
    rw [← e]
    exact one_div_le_one_div_of_le hs₂ (by nlinarith)
  have key : (P * x₂ ^ 2 - Q * x₂) - (P * x₁ ^ 2 - Q * x₁) = (x₂ - x₁) * (P * (x₁ + x₂) - Q) := by
    ring
  have h2 : 0 ≤ P * (x₁ + x₂) - Q := by
    have : Q ≤ 2 * P * x₂ := by
      have := (div_le_iff₀ (by positivity : 0 < 2 * P)).mp hxs
      linarith
    nlinarith
  nlinarith [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) h2]

/-- `h` is increasing on `{τ ≥ τ*}`. -/
theorem cap_objective_monotone (V c A₁ A₂ k : ℝ) (hV : 0 < V) (hc : 0 ≤ c)
    (hA₁ : 0 < A₁) (hA₂ : 0 ≤ A₂) (hk : 0 < k) {τ₁ τ₂ : ℝ}
    (h₁ : (A₂ + c / V) / A₁ ≤ τ₁) (h₁₂ : τ₁ ≤ τ₂) :
    capObjective V c A₁ A₂ k τ₁ ≤ capObjective V c A₁ A₂ k τ₂ := by
  have hss : 0 < A₁ + k * ((A₂ + c / V) / A₁) := by positivity
  have hs₁ : 0 < A₁ + k * τ₁ := by nlinarith
  have hs₂ : 0 < A₁ + k * τ₂ := by nlinarith
  rw [capObjective_quadratic V c A₁ A₂ k τ₁ hk hs₁.ne',
    capObjective_quadratic V c A₁ A₂ k τ₂ hk hs₂.ne']
  set P := V * A₂ + c + V * A₁ ^ 2 / k
  have hP : 0 < P := by positivity
  set Q := 2 * V * A₁ / k
  set x₁ := 1 / (A₁ + k * τ₁)
  set x₂ := 1 / (A₁ + k * τ₂)
  have hx : x₂ ≤ x₁ := one_div_le_one_div_of_le hs₁ (by nlinarith)
  have hxs : x₁ ≤ Q / (2 * P) := by
    have e : 1 / (A₁ + k * ((A₂ + c / V) / A₁)) = Q / (2 * P) := by
      simp only [Q, P]; field_simp; ring
    rw [← e]
    exact one_div_le_one_div_of_le hss (by nlinarith)
  have key : (P * x₂ ^ 2 - Q * x₂) - (P * x₁ ^ 2 - Q * x₁) = (x₂ - x₁) * (P * (x₁ + x₂) - Q) := by
    ring
  have h2 : P * (x₁ + x₂) - Q ≤ 0 := by
    have : 2 * P * x₁ ≤ Q := by
      have := (le_div_iff₀ (by positivity : 0 < 2 * P)).mp hxs
      linarith
    nlinarith
  nlinarith [mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hx) h2]

end Limites
