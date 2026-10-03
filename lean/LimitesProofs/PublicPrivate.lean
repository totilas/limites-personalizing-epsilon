import LimitesProofs.Risks

/-!
# Section `sec:public_case`: limits of public-private combination

* `public_data_factor_two` — Thm. `thm:public-data-factor-2`, at every `A, B > 0`:
  with one finite budget level and public records, `𝓡_thr ≤ 2 𝓡_pers`.
* `direct_factor_two` — Prop. `prop:direct-two`, the direct proof used for it.
* `mixture_le_persObj`, `harmonic_le_mixture`, `mixture_min_le` — the steps of that proof.
-/

open Finset

namespace Limites

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `ab/(a+b) ≤ W₁² a + W₂² b` whenever `W₁ + W₂ = 1`: the best two-point mixture of
two unbiased estimators of risks `a, b` has risk `ab/(a+b)`. -/
lemma harmonic_le_mixture (a b W₁ W₂ : ℝ) (ha : 0 < a) (hb : 0 < b) (hsum : W₁ + W₂ = 1) :
    a * b / (a + b) ≤ W₁ ^ 2 * a + W₂ ^ 2 * b := by
  rw [div_le_iff₀ (by linarith), show W₂ = 1 - W₁ by linarith]
  nlinarith [sq_nonneg (W₁ * (a + b) - b)]

/-- For `a, b > 0` and any split `W₁ + W₂ = 1`, `min a b ≤ 2 (W₁² a + W₂² b)`:
the mixture value is at least `ab/(a+b)`, and `min a b ≤ 2ab/(a+b)`. -/
lemma mixture_min_le (a b W₁ W₂ : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hsum : W₁ + W₂ = 1) :
    min a b ≤ 2 * (W₁ ^ 2 * a + W₂ ^ 2 * b) := by
  have hab : 0 < a + b := by linarith
  have hmin : min a b ≤ 2 * (a * b / (a + b)) := by
    rw [← mul_div_assoc, le_div_iff₀ hab]
    rcases le_total a b with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  linarith [harmonic_le_mixture a b W₁ W₂ ha hb hsum]

/-- The personalized objective dominates the two-point mixture value
`W₁² a + W₂² b`, with `a = A/n₁ + B/(ε₁n₁)²` (all-private threshold) and
`b = A/n₂` (all-public threshold). -/
lemma mixture_le_persObj
    (s₁ s₂ : Finset ι) (hdisj : Disjoint s₁ s₂) (hcover : s₁ ∪ s₂ = univ)
    (ε₁ A B : ℝ) (hε₁ : 0 < ε₁) (hA : 0 < A) (hB : 0 < B)
    (hs₁ : s₁.Nonempty) (hs₂ : s₂.Nonempty)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (M : ℝ) (hM₁ : ∀ i ∈ s₁, w i ≤ M * ε₁) :
    (∑ i ∈ s₁, w i) ^ 2 * (A / s₁.card + B / (ε₁ * s₁.card) ^ 2)
      + (∑ i ∈ s₂, w i) ^ 2 * (A / s₂.card) ≤ persObj A B w M := by
  unfold persObj
  set n₁ : ℝ := (s₁.card : ℝ) with hn₁
  set n₂ : ℝ := (s₂.card : ℝ) with hn₂
  have hn₁pos : 0 < n₁ := by rw [hn₁]; exact_mod_cast card_pos.mpr hs₁
  have hn₂pos : 0 < n₂ := by rw [hn₂]; exact_mod_cast card_pos.mpr hs₂
  set W₁ : ℝ := ∑ i ∈ s₁, w i with hW₁
  set W₂ : ℝ := ∑ i ∈ s₂, w i with hW₂
  have hW₁nonneg : 0 ≤ W₁ := sum_nonneg fun i _ => hw i
  have hCS₁ : W₁ ^ 2 ≤ n₁ * ∑ i ∈ s₁, (w i) ^ 2 := sq_sum_le_card_mul_sum_sq
  have hCS₂ : W₂ ^ 2 ≤ n₂ * ∑ i ∈ s₂, (w i) ^ 2 := sq_sum_le_card_mul_sum_sq
  have hSsplit : ∑ i, (w i) ^ 2 = (∑ i ∈ s₁, (w i) ^ 2) + ∑ i ∈ s₂, (w i) ^ 2 := by
    rw [← hcover, sum_union hdisj]
  have hW₁M : W₁ ≤ n₁ * ε₁ * M := by
    have h1 : W₁ ≤ ∑ _i ∈ s₁, M * ε₁ := sum_le_sum hM₁
    rw [sum_const, nsmul_eq_mul, ← hn₁] at h1
    linarith
  clear_value n₁ n₂ W₁ W₂
  have h₁ : W₁ ^ 2 * (A / n₁) ≤ A * ∑ i ∈ s₁, (w i) ^ 2 := by
    rw [mul_div_assoc', div_le_iff₀ hn₁pos]
    nlinarith [mul_le_mul_of_nonneg_left hCS₁ hA.le]
  have h₂ : W₂ ^ 2 * (A / n₂) ≤ A * ∑ i ∈ s₂, (w i) ^ 2 := by
    rw [mul_div_assoc', div_le_iff₀ hn₂pos]
    nlinarith [mul_le_mul_of_nonneg_left hCS₂ hA.le]
  have h₃ : W₁ ^ 2 * (B / (ε₁ * n₁) ^ 2) ≤ B * M ^ 2 := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    have hsq : W₁ ^ 2 ≤ (n₁ * ε₁ * M) ^ 2 := pow_le_pow_left₀ hW₁nonneg hW₁M 2
    nlinarith [mul_le_mul_of_nonneg_left hsq hB.le]
  rw [hSsplit]
  nlinarith

/-- **Prop. `prop:direct-two`.**  Group `s₁` has
budget `ε₁`; group `s₂` is public (its weights are unconstrained).  For every
feasible `(w, M)`, the better of the two thresholds — all `n` records at level
`ε₁`, or the public records alone (risk `A/n₂`) — is within a factor 2 of the
personalized objective. -/
theorem direct_factor_two
    (s₁ s₂ : Finset ι) (hdisj : Disjoint s₁ s₂) (hcover : s₁ ∪ s₂ = univ)
    (ε₁ A B : ℝ) (hε₁ : 0 < ε₁) (hA : 0 < A) (hB : 0 < B)
    (hs₁ : s₁.Nonempty) (hs₂ : s₂.Nonempty)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (M : ℝ) (hM₁ : ∀ i ∈ s₁, w i ≤ M * ε₁) :
    min (thrObj A B ε₁ (Fintype.card ι)) (A / s₂.card) ≤ 2 * persObj A B w M := by
  have hmix := mixture_le_persObj s₁ s₂ hdisj hcover ε₁ A B hε₁ hA hB hs₁ hs₂ w hw M hM₁
  unfold thrObj
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  set n₁ : ℝ := (s₁.card : ℝ) with hn₁
  set n₂ : ℝ := (s₂.card : ℝ) with hn₂
  have hn₁pos : 0 < n₁ := by rw [hn₁]; exact_mod_cast card_pos.mpr hs₁
  have hn₂pos : 0 < n₂ := by rw [hn₂]; exact_mod_cast card_pos.mpr hs₂
  have hn₁len : n₁ ≤ n := by rw [hn₁, hn]; exact_mod_cast card_le_univ s₁
  have hsplit : (∑ i ∈ s₁, w i) + (∑ i ∈ s₂, w i) = 1 := by
    rw [← sum_union hdisj, hcover]
    simpa using hsum
  set a : ℝ := A / n₁ + B / (ε₁ * n₁) ^ 2 with ha
  set b : ℝ := A / n₂ with hb
  -- using all records at level ε₁ is no worse than using the private records alone
  have hthr₁ : A / n + B / (ε₁ * n) ^ 2 ≤ a := by
    have h1 : A / n ≤ A / n₁ := div_le_div_of_nonneg_left hA.le hn₁pos hn₁len
    have h2 : B / (ε₁ * n) ^ 2 ≤ B / (ε₁ * n₁) ^ 2 :=
      div_le_div_of_nonneg_left hB.le (by positivity)
        (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hn₁len hε₁.le) 2)
    linarith
  calc min (A / n + B / (ε₁ * n) ^ 2) (A / n₂)
      ≤ min a b := min_le_min hthr₁ le_rfl
    _ ≤ 2 * ((∑ i ∈ s₁, w i) ^ 2 * a + (∑ i ∈ s₂, w i) ^ 2 * b) :=
        mixture_min_le a b _ _ (by positivity) (by positivity) hsplit
    _ ≤ 2 * persObj A B w M := by linarith

/-- Thresholds above every finite budget keep only the public records, so
`𝓡_thr ≤ A/n₂` (the all-public threshold, reached as `t → ∞`). -/
lemma thrRisk_le_public (pub : Finset ι) (u : ι → ℝ) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hpub : pub.Nonempty) :
    thrRisk pub u A B ≤ A / #pub := by
  set n₂ : ℝ := (#pub : ℝ) with hn₂
  have hn₂1 : 1 ≤ n₂ := by rw [hn₂]; exact_mod_cast card_pos.mpr hpub
  by_contra hlt
  rw [not_le] at hlt
  set δ := thrRisk pub u A B - A / n₂ with hδ
  have hδpos : 0 < δ := by linarith
  set t := 1 + B / δ + ∑ i, |u i| with ht
  have habs : 0 ≤ ∑ i, |u i| := sum_nonneg fun i _ => abs_nonneg _
  have hBδ : 0 < B / δ := div_pos hB hδpos
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hN : nThr pub u t = #pub := by
    unfold nThr
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and, or_iff_left_iff_imp]
    intro hti
    have : |u i| ≤ ∑ j, |u j| := single_le_sum (fun j _ => abs_nonneg (u j)) (mem_univ i)
    linarith [le_abs_self (u i)]
  have hle := thrRisk_le hA.le hB.le ht0 (by rw [hN]; exact card_pos.mpr hpub)
  rw [hN] at hle
  unfold thrObj at hle
  rw [← hn₂] at hle
  have hx : t ≤ t * n₂ := le_mul_of_one_le_right ht0.le hn₂1
  have hnoise : B / (t * n₂) ^ 2 ≤ B / t :=
    div_le_div_of_nonneg_left hB.le ht0
      (by nlinarith [mul_nonneg (show 0 ≤ t * n₂ by linarith) (show 0 ≤ t * n₂ - 1 by linarith)])
  have hsmall : B / t < δ := by
    rw [div_lt_iff₀ ht0]
    have : B / δ < t := by linarith
    rwa [div_lt_iff₀ hδpos, mul_comm] at this
  linarith

/-- **Thm. `thm:public-data-factor-2`.**  If every non-public record has the
same budget `ε₁ > 0`, and there are both public and private records, then
`𝓡_thr(u; A, B) ≤ 2 𝓡_pers(u; A, B)` for every `A, B > 0`. -/
theorem public_data_factor_two (pub : Finset ι) (u : ι → ℝ) (ε₁ A B : ℝ)
    (hε₁ : 0 < ε₁) (hA : 0 < A) (hB : 0 < B)
    (hpub : pub.Nonempty) (hpriv : pubᶜ.Nonempty) (hu : ∀ i ∉ pub, u i = ε₁) :
    thrRisk pub u A B ≤ 2 * persRisk pub u A B := by
  have : Nonempty ι := ⟨hpub.choose⟩
  refine thrRisk_le_mul_persRisk two_pos
    (feasible_nonempty fun i hi => (hu i hi).symm ▸ hε₁) fun w M ⟨hw, hsum, _, hM⟩ => ?_
  have hall : nThr pub u ε₁ = Fintype.card ι := by
    unfold nThr
    rw [filter_true_of_mem, card_univ]
    intro i _
    by_cases hi : i ∈ pub
    · exact Or.inl hi
    · exact Or.inr (hu i hi).ge
  have h1 : thrRisk pub u A B ≤ thrObj A B ε₁ (Fintype.card ι) := by
    have := thrRisk_le (pub := pub) (u := u) hA.le hB.le hε₁ (by rw [hall]; exact Fintype.card_pos)
    rwa [hall] at this
  have h3 := direct_factor_two pubᶜ pub disjoint_compl_left (by rw [union_comm, union_compl]) ε₁ A B
    hε₁ hA hB hpriv hpub w hw hsum M fun i hi => by
      have := hM i (mem_compl.mp hi)
      rwa [hu i (mem_compl.mp hi)] at this
  exact (le_min h1 (thrRisk_le_public pub u hA hB hpub)).trans h3

end Limites
