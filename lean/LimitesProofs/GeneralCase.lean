import LimitesProofs.Risks

/-!
# Section `sec:general_case`: general choice of privacy budgets

* `rescaling_pers`, `rescaling_thr` — Lemma `lem:reduction`, Part 2 (exact rescaling)
* `upper_bound` — Thm. `thm:upper-bound-general-m-levels`:
  `𝓡_thr ≤ min{(1 + log₂ n)², m²} 𝓡_pers` for every `A, B > 0`, where `m` is the
  number of distinct budgets.  The two halves are proved pointwise by
  `direct_factor_harmonic` (the `H_n²` bound, cf. Lemma
  `lem:threshold-vs-affine-sectionX`) and `direct_factor_m_sq` (Prop. `prop:direct-msq`).
* `two_level_factor_four` — Cor. `thm:two-level-factor-4`;
  `direct_factor_four` — its direct proof, Prop. `prop:direct-four`.
* `LowerBound.lower_bound`, `LowerBound.lower_bound_log` — Thm.
  `thm:lower-bound-general-m-levels`, for every `A, B > 0`.

The `H_n²` bound is proved directly for every feasible mechanism, thresholding at
`w_j / M` for the record `j` maximizing `w_j · #{k : w_k ≥ w_j}`; this avoids Part 1
of Lemma `lem:reduction` (capped weights), which is not formalized.
-/

open Finset

namespace Limites

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Lemma `lem:reduction`, Part 2 (exact rescaling)

With `γ = √(8A/B)`: `𝓡_pers(u; A, B) = 4A · MSE_aff(γu)` and
`𝓡_thr(u; A, B) = 4A · MSE_thr(γu)`. -/

omit [DecidableEq ι] in
theorem rescaling_pers (pub : Finset ι) (u : ι → ℝ) {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    persRisk pub u A B = 4 * A * persRisk pub (fun i => Real.sqrt (8 * A / B) * u i) (1/4) 2 := by
  set γ := Real.sqrt (8 * A / B)
  have hγ : 0 < γ := Real.sqrt_pos.mpr (by positivity)
  have hγ2 : γ ^ 2 = 8 * A / B := Real.sq_sqrt (by positivity)
  have h1 := persRisk_scale pub u (1/4) 2 hγ one_pos
  have h2 := persRisk_scale pub u (1/4) (2 / γ ^ 2) one_pos (by positivity : (0:ℝ) < 4 * A)
  have e : (fun i => (1:ℝ) * u i) = u := funext fun i => one_mul _
  have e1 : 4 * A * (1/4) = A := by ring
  have e2 : 4 * A * (2 / γ ^ 2) = B := by rw [hγ2]; field_simp; ring
  rw [e, e1, e2, one_pow, div_one] at h2
  rw [one_mul, one_mul, one_mul] at h1
  rw [h2, h1]

theorem rescaling_thr (pub : Finset ι) (u : ι → ℝ) {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    thrRisk pub u A B = 4 * A * thrRisk pub (fun i => Real.sqrt (8 * A / B) * u i) (1/4) 2 := by
  set γ := Real.sqrt (8 * A / B)
  have hγ : 0 < γ := Real.sqrt_pos.mpr (by positivity)
  have hγ2 : γ ^ 2 = 8 * A / B := Real.sq_sqrt (by positivity)
  have h1 := thrRisk_scale pub u (1/4) 2 hγ one_pos
  have h2 := thrRisk_scale pub u (1/4) (2 / γ ^ 2) one_pos (by positivity : (0:ℝ) < 4 * A)
  have e : (fun i => (1:ℝ) * u i) = u := funext fun i => one_mul _
  have e1 : 4 * A * (1/4) = A := by ring
  have e2 : 4 * A * (2 / γ ^ 2) = B := by rw [hγ2]; field_simp; ring
  rw [e, e1, e2, one_pow, div_one] at h2
  rw [one_mul, one_mul, one_mul] at h1
  rw [h2, h1]

/-! ## Thm. `thm:upper-bound-general-m-levels`, the `(1 + log₂ n)²` half -/

omit [Fintype ι] [DecidableEq ι] in
/-- Harmonic-sum estimate: if `#{k : x_k ≥ x_i} · x_i ≤ V` for every `i`, then
`∑ x ≤ V · H_{|s|}`. -/
lemma sum_le_mul_harmonic (x : ι → ℝ) (V : ℝ) (s : Finset ι) (hx : ∀ i ∈ s, 0 ≤ x i)
    (hV : ∀ i ∈ s, (#{k ∈ s | x i ≤ x k} : ℝ) * x i ≤ V) :
    ∑ i ∈ s, x i ≤ V * harmonic #s := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  obtain ⟨i₀, hi₀, hmin⟩ := s.exists_min_image x hs
  have h0 : (#s : ℝ) * x i₀ ≤ V := by
    have := hV i₀ hi₀
    rwa [filter_true_of_mem hmin] at this
  have hcard : #s = #(s.erase i₀) + 1 := (card_erase_add_one hi₀).symm
  have ih' := ih (s.erase i₀) (erase_ssubset hi₀) (fun i hi => hx i (mem_of_mem_erase hi))
    fun i hi => by
      have hsub : #{k ∈ s.erase i₀ | x i ≤ x k} ≤ #{k ∈ s | x i ≤ x k} :=
        card_le_card (filter_subset_filter _ (erase_subset _ _))
      calc (#{k ∈ s.erase i₀ | x i ≤ x k} : ℝ) * x i
          ≤ #{k ∈ s | x i ≤ x k} * x i :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hsub) (hx i (mem_of_mem_erase hi))
        _ ≤ V := hV i (mem_of_mem_erase hi)
  rw [← add_sum_erase s x hi₀, hcard, harmonic_succ]
  rw [hcard] at h0
  push_cast at h0 ⊢
  have hk : (0:ℝ) < #(s.erase i₀) + 1 := by positivity
  have hx0 : x i₀ ≤ V * ((#(s.erase i₀) : ℝ) + 1)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hk]
    linarith
  rw [mul_add]
  linarith

omit [DecidableEq ι] in
lemma univ_nonempty_of_feasible {pub : Finset ι} {u w : ι → ℝ} {M : ℝ}
    (hf : Feasible pub u w M) : (univ : Finset ι).Nonempty := by
  rcases (univ : Finset ι).eq_empty_or_nonempty with h | h
  · have hsum := hf.2.1
    rw [h, sum_empty] at hsum
    norm_num at hsum
  · exact h

/-- **The `H_n²` bound, pointwise.**  For every feasible `(w, M)` there is a
threshold `t > 0` with `n_t ≥ 1` whose objective is at most `H_n²` times the
personalized objective. -/
theorem direct_factor_harmonic (u : ι → ℝ) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    {w : ι → ℝ} {M : ℝ} (hf : Feasible ∅ u w M) :
    ∃ t, 0 < t ∧ 0 < nThr ∅ u t ∧
      thrObj A B t (nThr ∅ u t) ≤ (harmonic (Fintype.card ι) : ℝ) ^ 2 * persObj A B w M := by
  have hne := univ_nonempty_of_feasible hf
  obtain ⟨hw, hsum, hM0, hM⟩ := hf
  have hM' : ∀ i, w i ≤ M * u i := fun i => hM i (by simp)
  obtain ⟨j, -, hj⟩ := univ.exists_max_image (fun i => (#{k | w i ≤ w k} : ℝ) * w i) hne
  set F : Finset ι := {k | w j ≤ w k} with hF
  set N' : ℝ := (#F : ℝ) with hN'
  set H : ℝ := (harmonic (Fintype.card ι) : ℝ) with hH
  have hHV : 1 ≤ N' * w j * H := by
    have := sum_le_mul_harmonic w (N' * w j) univ (fun i _ => hw i) fun i _ => hj i (mem_univ i)
    rwa [hsum, card_univ] at this
  have hj0 : 0 < w j := by
    rcases (hw j).lt_or_eq with h | h
    · exact h
    · rw [← h] at hHV; norm_num at hHV
  have hMpos : 0 < M := by
    rcases hM0.lt_or_eq with h | h
    · exact h
    · have := hM' j; rw [← h, zero_mul] at this; linarith
  set t := w j / M with ht_def
  have ht : 0 < t := div_pos hj0 hMpos
  have hsub : F ⊆ univ.filter fun i => i ∈ (∅ : Finset ι) ∨ t ≤ u i := by
    intro k hk
    simp only [hF, mem_filter, mem_univ, true_and] at hk ⊢
    right
    rw [ht_def, div_le_iff₀ hMpos, mul_comm]
    exact hk.trans (hM' k)
  have hjF : j ∈ F := by simp [hF]
  have hN'pos : 0 < N' := by rw [hN']; exact_mod_cast card_pos.mpr ⟨j, hjF⟩
  have hN'N : N' ≤ (nThr ∅ u t : ℝ) := Nat.cast_le.mpr (card_le_card hsub)
  have hNpos : 0 < nThr ∅ u t := Nat.lt_of_lt_of_le (card_pos.mpr ⟨j, hjF⟩) (card_le_card hsub)
  refine ⟨t, ht, hNpos, ?_⟩
  set N : ℝ := (nThr ∅ u t : ℝ) with hN
  have hH0 : 0 < H := by
    by_contra h
    rw [not_lt] at h
    nlinarith [mul_pos hN'pos hj0]
  have hS : N' * w j ^ 2 ≤ ∑ i, w i ^ 2 :=
    calc N' * w j ^ 2 = ∑ _k ∈ F, w j ^ 2 := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ k ∈ F, w k ^ 2 := sum_le_sum fun k hk =>
          pow_le_pow_left₀ (hw j) (by simpa [hF] using hk) 2
      _ ≤ ∑ i, w i ^ 2 := sum_le_sum_of_subset_of_nonneg (subset_univ F)
          fun _ _ _ => sq_nonneg _
  have h1 : 1 ≤ (N' * w j * H) ^ 2 := by nlinarith
  have g1 : A / N ≤ H ^ 2 * (A * ∑ i, w i ^ 2) :=
    calc A / N ≤ A / N' := div_le_div_of_nonneg_left hA.le hN'pos hN'N
      _ ≤ (A * H ^ 2) * (N' * w j ^ 2) := by
          rw [div_le_iff₀ hN'pos,
            show A * H ^ 2 * (N' * w j ^ 2) * N' = A * (N' * w j * H) ^ 2 by ring]
          nlinarith
      _ ≤ (A * H ^ 2) * ∑ i, w i ^ 2 := mul_le_mul_of_nonneg_left hS (by positivity)
      _ = H ^ 2 * (A * ∑ i, w i ^ 2) := by ring
  have htN : N' * w j / M ≤ t * N := by
    have e : t * N' = N' * w j / M := by rw [ht_def]; ring
    rw [← e]
    exact mul_le_mul_of_nonneg_left hN'N ht.le
  have g2 : B / (t * N) ^ 2 ≤ H ^ 2 * (B * M ^ 2) :=
    calc B / (t * N) ^ 2 ≤ B / (N' * w j / M) ^ 2 :=
          div_le_div_of_nonneg_left hB.le (by positivity)
            (pow_le_pow_left₀ (by positivity) htN 2)
      _ ≤ H ^ 2 * (B * M ^ 2) := by
          rw [div_le_iff₀ (by positivity),
            show H ^ 2 * (B * M ^ 2) * (N' * w j / M) ^ 2 = B * (N' * w j * H) ^ 2 by
              field_simp]
          nlinarith
  unfold thrObj persObj
  linarith

/-- `H_n ≤ 1 + log₂ n`. -/
lemma harmonic_le_one_add_logb (n : ℕ) : (harmonic n : ℝ) ≤ 1 + Real.logb 2 n := by
  have h := harmonic_le_one_add_log n
  have hlog : Real.log n ≤ Real.logb 2 n := by
    rw [Real.logb, le_div_iff₀ (Real.log_pos one_lt_two)]
    have h0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have h2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; norm_num at this; linarith
    nlinarith
  linarith

/-! ## Thm. `thm:upper-bound-general-m-levels`, the `m²` half -/

/-- **Prop. `prop:direct-msq`.**  Let `m` be the number of distinct budgets.  For
every feasible `(w, M)` there is a budget level `v` whose threshold has objective
at most `m²` times the personalized objective. -/
theorem direct_factor_m_sq (u : ι → ℝ) (hu : ∀ i, 0 < u i) {A B : ℝ} (hA : 0 < A)
    (hB : 0 < B) {w : ι → ℝ} {M : ℝ} (hf : Feasible ∅ u w M) :
    ∃ v ∈ univ.image u,
      thrObj A B v (nThr ∅ u v) ≤ (#(univ.image u) : ℝ) ^ 2 * persObj A B w M := by
  have hne := univ_nonempty_of_feasible hf
  obtain ⟨hw, hsum, hM0, hM⟩ := hf
  have hM' : ∀ i, w i ≤ M * u i := fun i => hM i (by simp)
  set m : ℝ := (#(univ.image u) : ℝ) with hm
  have him : (univ.image u).Nonempty := hne.image u
  have hm' : 0 < m := by rw [hm]; exact_mod_cast card_pos.mpr him
  -- pigeonhole: some budget level carries weight at least 1/m
  have hfib : ∑ v ∈ univ.image u, ∑ i ∈ univ with u i = v, w i = 1 := by
    rw [sum_fiberwise_of_maps_to fun i _ => mem_image_of_mem u (mem_univ i)]
    exact hsum
  have hpigeon : ∃ v ∈ univ.image u, 1 / m ≤ ∑ i ∈ univ with u i = v, w i := by
    by_contra hcon
    simp only [not_exists, not_and, not_le] at hcon
    have hlt : ∑ v ∈ univ.image u, ∑ i ∈ univ with u i = v, w i
        < ∑ _v ∈ univ.image u, 1 / m := sum_lt_sum_of_nonempty him hcon
    rw [hfib, sum_const, nsmul_eq_mul, ← hm, mul_one_div_cancel hm'.ne'] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨v, hv, hk⟩ := hpigeon
  have hvpos : 0 < v := by
    obtain ⟨i, -, rfl⟩ := mem_image.mp hv
    exact hu i
  refine ⟨v, hv, ?_⟩
  set Gk : Finset ι := univ.filter fun i => u i = v with hGk
  set Rk : Finset ι := univ.filter fun i => i ∈ (∅ : Finset ι) ∨ v ≤ u i with hRk
  set W : ℝ := ∑ i ∈ Gk, w i with hW
  have hWpos : 0 < W := lt_of_lt_of_le (div_pos one_pos hm') hk
  have hsubset : Gk ⊆ Rk := by
    intro i hi
    simp only [hGk, hRk, mem_filter, mem_univ, true_and] at hi ⊢
    exact Or.inr hi.ge
  have hGkne : Gk.Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    rw [hW, hemp, sum_empty] at hWpos
    exact lt_irrefl _ hWpos
  set nk : ℝ := (#Gk : ℝ) with hnk
  set Nk : ℝ := (nThr ∅ u v : ℝ) with hNk
  have hnkpos : 0 < nk := by rw [hnk]; exact_mod_cast card_pos.mpr hGkne
  have hNkge : nk ≤ Nk := Nat.cast_le.mpr (card_le_card hsubset)
  have hNkpos : 0 < Nk := lt_of_lt_of_le hnkpos hNkge
  set S : ℝ := ∑ i, (w i) ^ 2 with hS
  have hSnonneg : 0 ≤ S := sum_nonneg fun i _ => sq_nonneg _
  -- Cauchy–Schwarz on the level, then extend to the full sum
  have hCS : W ^ 2 ≤ nk * S := by
    have h1 : W ^ 2 ≤ nk * ∑ i ∈ Gk, (w i) ^ 2 := sq_sum_le_card_mul_sum_sq
    have h2 : (∑ i ∈ Gk, (w i) ^ 2) ≤ S :=
      sum_le_sum_of_subset_of_nonneg (subset_univ Gk) fun i _ _ => sq_nonneg _
    nlinarith
  -- the privacy constraint: the level weight is at most nk · v · M
  have hWM : W ≤ nk * v * M := by
    have h1 : W ≤ ∑ _i ∈ Gk, M * v := by
      apply sum_le_sum
      intro i hi
      rw [hGk, mem_filter] at hi
      simpa [hi.2] using hM' i
    rw [sum_const, nsmul_eq_mul, ← hnk] at h1
    linarith
  have hMpos : 0 < M := by
    by_contra hMle
    rw [not_lt] at hMle
    have h1 : nk * v * M ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hnkpos.le hvpos.le) hMle
    linarith
  have hmW : 1 ≤ m * W := by
    rw [div_le_iff₀ hm'] at hk
    linarith
  have goal₁ : A / Nk ≤ m ^ 2 * (A * S) := by
    rw [div_le_iff₀ hNkpos]
    have h1 : W ^ 2 ≤ Nk * S := le_trans hCS (mul_le_mul_of_nonneg_right hNkge hSnonneg)
    have h2 : (1:ℝ) ≤ m ^ 2 * (Nk * S) := by
      nlinarith [sq_nonneg (m * W - 1), mul_le_mul_of_nonneg_left h1 (sq_nonneg m)]
    nlinarith [mul_le_mul_of_nonneg_left h2 hA.le]
  have goal₂ : B / (v * Nk) ^ 2 ≤ m ^ 2 * (B * M ^ 2) := by
    rw [div_le_iff₀ (pow_pos (mul_pos hvpos hNkpos) 2)]
    have hchain : W ≤ Nk * v * M := by
      nlinarith [mul_le_mul_of_nonneg_right hNkge (mul_nonneg hvpos.le hMpos.le)]
    have h4 : (1:ℝ) ≤ m * (Nk * v * M) := by
      nlinarith [mul_le_mul_of_nonneg_left hchain hm'.le]
    have h5 : (1:ℝ) ≤ (m * (Nk * v * M)) ^ 2 := by
      nlinarith [sq_nonneg (m * (Nk * v * M) - 1)]
    nlinarith [mul_le_mul_of_nonneg_left h5 hB.le]
  unfold thrObj persObj
  linarith

/-- **Thm. `thm:upper-bound-general-m-levels`.**  For finite positive budgets
taking `m` distinct values among `n` records, and every `A, B > 0`,
`𝓡_thr(u; A, B) ≤ min{(1 + log₂ n)², m²} · 𝓡_pers(u; A, B)`. -/
theorem upper_bound [Nonempty ι] (u : ι → ℝ) (hu : ∀ i, 0 < u i) {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B) :
    thrRisk ∅ u A B ≤ min ((1 + Real.logb 2 (Fintype.card ι)) ^ 2) ((#(univ.image u) : ℝ) ^ 2)
      * persRisk ∅ u A B := by
  have hlog0 : 0 ≤ Real.logb 2 (Fintype.card ι) :=
    Real.logb_nonneg one_lt_two (by exact_mod_cast Fintype.card_pos)
  have hm1 : (1:ℝ) ≤ #(univ.image u) := by exact_mod_cast card_pos.mpr (univ_nonempty.image u)
  refine thrRisk_le_mul_persRisk (lt_min (by positivity) (by positivity))
    (feasible_nonempty fun i _ => hu i) fun w M hf => ?_
  have hf0 : 0 ≤ persObj A B w M := persObj_nonneg hA.le hB.le w M
  rw [min_mul_of_nonneg _ _ hf0]
  refine le_min ?_ ?_
  · obtain ⟨t, ht, hN, hle⟩ := direct_factor_harmonic u hA hB hf
    have hH0 : (0:ℝ) ≤ harmonic (Fintype.card ι) :=
      Rat.cast_nonneg.mpr (harmonic_pos Fintype.card_ne_zero).le
    calc thrRisk ∅ u A B ≤ thrObj A B t (nThr ∅ u t) := thrRisk_le hA.le hB.le ht hN
      _ ≤ (harmonic (Fintype.card ι) : ℝ) ^ 2 * persObj A B w M := hle
      _ ≤ (1 + Real.logb 2 (Fintype.card ι)) ^ 2 * persObj A B w M :=
          mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ hH0 (harmonic_le_one_add_logb _) 2) hf0
  · obtain ⟨v, hv, hle⟩ := direct_factor_m_sq u hu hA hB hf
    obtain ⟨i, -, rfl⟩ := mem_image.mp hv
    have hN : 0 < nThr ∅ u (u i) := card_pos.mpr ⟨i, by simp⟩
    exact (thrRisk_le hA.le hB.le (hu i) hN).trans hle

/-! ## Cor. `thm:two-level-factor-4` -/

/-- **Cor. `thm:two-level-factor-4`.**  With at most two distinct finite budgets,
`𝓡_thr(u; A, B) ≤ 4 𝓡_pers(u; A, B)` for every `A, B > 0`. -/
theorem two_level_factor_four [Nonempty ι] (u : ι → ℝ) (hu : ∀ i, 0 < u i)
    (h2 : #(univ.image u) ≤ 2) {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    thrRisk ∅ u A B ≤ 4 * persRisk ∅ u A B := by
  have hm : (#(univ.image u) : ℝ) ^ 2 ≤ 4 := by
    have : (#(univ.image u) : ℝ) ≤ 2 := by exact_mod_cast h2
    nlinarith [(Nat.cast_nonneg _ : (0:ℝ) ≤ #(univ.image u))]
  exact (upper_bound u hu hA hB).trans
    (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans hm) (persRisk_nonneg hA.le hB.le))

/-- **Prop. `prop:direct-four`.**  For every feasible `(w, M)`, the better of the
two thresholds — all `n` records at level `ε₁`, or the `n₂` records of group 2
at level `ε₂` — has objective at most 4 times the personalized objective. -/
theorem direct_factor_four
    (s₁ s₂ : Finset ι) (hdisj : Disjoint s₁ s₂) (hcover : s₁ ∪ s₂ = univ)
    (ε₁ ε₂ A B : ℝ) (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (hA : 0 < A) (hB : 0 < B)
    (hs₂ : s₂.Nonempty)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (M : ℝ) (hM₁ : ∀ i ∈ s₁, w i ≤ M * ε₁) (hM₂ : ∀ i ∈ s₂, w i ≤ M * ε₂) :
    min (thrObj A B ε₁ (Fintype.card ι)) (thrObj A B ε₂ s₂.card)
      ≤ 4 * persObj A B w M := by
  unfold thrObj persObj
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  set n₂ : ℝ := (s₂.card : ℝ) with hn₂
  have hn₂pos : 0 < n₂ := by rw [hn₂]; exact_mod_cast card_pos.mpr hs₂
  have hnpos : 0 < n := by
    rw [hn]; exact_mod_cast lt_of_lt_of_le (card_pos.mpr hs₂) (card_le_univ s₂)
  set S : ℝ := ∑ i, (w i) ^ 2 with hS
  have hsplit : (∑ i ∈ s₁, w i) + (∑ i ∈ s₂, w i) = 1 := by
    rw [← sum_union hdisj, hcover]
    simpa using hsum
  set W₁ : ℝ := ∑ i ∈ s₁, w i with hW₁
  set W₂ : ℝ := ∑ i ∈ s₂, w i with hW₂
  have hW₁nonneg : 0 ≤ W₁ := sum_nonneg fun i _ => hw i
  have hCS₂ : W₂ ^ 2 ≤ n₂ * ∑ i ∈ s₂, (w i) ^ 2 := sq_sum_le_card_mul_sum_sq
  have hS₂le : (∑ i ∈ s₂, (w i) ^ 2) ≤ S := by
    rw [hS, ← hcover, sum_union hdisj]
    have : (0:ℝ) ≤ ∑ i ∈ s₁, (w i) ^ 2 := sum_nonneg fun i _ => sq_nonneg _
    linarith
  have hCSall : 1 ≤ n * S := by
    have h : (∑ i, w i) ^ 2 ≤ n * S := sq_sum_le_card_mul_sum_sq
    rwa [hsum, one_pow] at h
  have hW₂raw : W₂ ≤ n₂ * (M * ε₂) := by
    have h1 : W₂ ≤ ∑ _i ∈ s₂, M * ε₂ := sum_le_sum hM₂
    rwa [sum_const, nsmul_eq_mul, ← hn₂] at h1
  by_cases hcase : (1:ℝ)/2 ≤ n * ε₁ * M
  · -- Case 1: the threshold at ε₁ (keep everything) is within factor 4
    refine le_trans (min_le_left _ _) ?_
    have goal₁ : A / n ≤ 4 * (A * S) := by
      rw [div_le_iff₀ hnpos]
      nlinarith [mul_le_mul_of_nonneg_left hCSall hA.le]
    have goal₂ : B / (ε₁ * n) ^ 2 ≤ 4 * (B * M ^ 2) := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : (1:ℝ) ≤ 4 * (n * ε₁ * M) ^ 2 := by
        nlinarith [sq_nonneg (2 * (n * ε₁ * M) - 1)]
      nlinarith [mul_le_mul_of_nonneg_left h1 hB.le]
    linarith
  · -- Case 2: the threshold at ε₂ (keep group 2) is within factor 4
    rw [not_le] at hcase
    refine le_trans (min_le_right _ _) ?_
    have hW₂half : (1:ℝ)/2 ≤ W₂ := by
      have h1 : W₁ ≤ (s₁.card : ℝ) * (M * ε₁) := by
        have := sum_le_sum hM₁
        rwa [sum_const, nsmul_eq_mul] at this
      have hcard : (s₁.card : ℝ) ≤ n := by rw [hn]; exact_mod_cast card_le_univ s₁
      rcases le_or_gt M 0 with hM0 | hM0
      · -- M ≤ 0 forces the group-1 weight to vanish
        have hMε : M * ε₁ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hM0 hε₁.le
        nlinarith [Nat.cast_nonneg (α := ℝ) s₁.card]
      · -- M > 0: the group-1 weight is at most n ε₁ M < 1/2
        have hMε : (0:ℝ) ≤ M * ε₁ := by positivity
        nlinarith
    have hM0 : 0 < M := by
      by_contra hMle
      rw [not_lt] at hMle
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hMle hε₂.le]
    have hW₂M : W₂ ≤ n₂ * ε₂ * M := by linarith
    have goal₁ : A / n₂ ≤ 4 * (A * S) := by
      rw [div_le_iff₀ hn₂pos]
      have h3 : W₂ ^ 2 ≤ n₂ * S := le_trans hCS₂ (mul_le_mul_of_nonneg_left hS₂le hn₂pos.le)
      have h4 : (1:ℝ) ≤ 4 * (n₂ * S) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h4 hA.le]
    have goal₂ : B / (ε₂ * n₂) ^ 2 ≤ 4 * (B * M ^ 2) := by
      rw [div_le_iff₀ (by positivity)]
      have h7 : (1:ℝ) ≤ 4 * (n₂ * ε₂ * M) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h7 hB.le]
    linarith

/-! ## Thm. `thm:lower-bound-general-m-levels`

The equal-revenue profile.  Records are pairs `⟨g, j⟩` with `g : Fin m` and
`j : Fin 2^g`: level `g` (paper index `i = g + 1`) has `2^g` records of budget
`√(B/(8A)) · 2^{-g}`, so `n = 2^m − 1`. -/

namespace LowerBound

/-- Records of the equal-revenue profile with `m` levels. -/
abbrev Rec (m : ℕ) := Σ g : Fin m, Fin (2 ^ (g : ℕ))

/-- Budgets of the equal-revenue profile, `uᵢ = 2^{-(i-1)} √(B/(8A))`. -/
noncomputable def budget (m : ℕ) (A B : ℝ) : Rec m → ℝ :=
  fun x => Real.sqrt (B / (8 * A)) * (1 / 2) ^ (x.1 : ℕ)

lemma card_rec (m : ℕ) : Fintype.card (Rec m) = 2 ^ m - 1 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun g => 2 ^ g) m, Nat.geomSum_eq le_rfl m]
  simp

/-- **Thm. `thm:lower-bound-general-m-levels`.**  For every `m ≥ 1` and every
`A, B > 0`, the equal-revenue profile satisfies
`𝓡_thr(u; A, B) ≥ (m²/5) · 𝓡_pers(u; A, B)`. -/
theorem lower_bound (m : ℕ) (hm : 0 < m) {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (m : ℝ) ^ 2 / 5 * persRisk ∅ (budget m A B) A B ≤ thrRisk ∅ (budget m A B) A B := by
  set c := Real.sqrt (B / (8 * A)) with hc_def
  have hc : 0 < c := Real.sqrt_pos.mpr (by positivity)
  have hc2 : c ^ 2 = B / (8 * A) := Real.sq_sqrt (by positivity)
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  -- the affine witness: weights `2^{-g}/m`, noise level `1/(m c)`
  have hpers : persRisk ∅ (budget m A B) A B ≤ 10 * A / m ^ 2 := by
    set w : Rec m → ℝ := fun x => (1 / 2) ^ (x.1 : ℕ) / m with hw
    have hlevel : ∀ g : Fin m, (2:ℝ) ^ (g : ℕ) * ((1 / 2) ^ (g : ℕ) / m) = 1 / m := by
      intro g
      rw [← mul_div_assoc, ← mul_pow]
      norm_num
    have hf : Feasible ∅ (budget m A B) w (1 / (m * c)) := by
      refine ⟨fun x => by positivity, ?_, by positivity, fun x _ => le_of_eq ?_⟩
      · rw [Fintype.sum_sigma]
        simp only [hw, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow,
          Nat.cast_ofNat, hlevel]
        field_simp
      · simp only [hw, budget, ← hc_def]
        field_simp
    have hgeom : ∑ g : Fin m, ((1:ℝ) / 2) ^ (g : ℕ) ≤ 2 := by
      rw [Fin.sum_univ_eq_sum_range (fun g => ((1:ℝ) / 2) ^ g) m]
      rw [geom_sum_eq (by norm_num : ((1:ℝ) / 2) ≠ 1) m,
        div_le_iff_of_neg (by norm_num : ((1:ℝ) / 2 - 1) < 0)]
      have hp : (0:ℝ) ≤ (1 / 2) ^ m := by positivity
      linarith
    have hsq : ∀ g : Fin m, (2:ℝ) ^ (g : ℕ) * ((1 / 2) ^ (g : ℕ) / m) ^ 2
        = (1 / 2) ^ (g : ℕ) * (1 / m ^ 2) := by
      intro g
      have h2a : (2:ℝ) ^ (g : ℕ) * (1 / 2) ^ (g : ℕ) = 1 := by rw [← mul_pow]; norm_num
      generalize (1 / 2 : ℝ) ^ (g : ℕ) = a at h2a ⊢
      rw [div_pow, show (2:ℝ) ^ (g : ℕ) * (a ^ 2 / m ^ 2) = 2 ^ (g : ℕ) * a * a / m ^ 2 by ring,
        h2a]
      ring
    calc persRisk ∅ (budget m A B) A B ≤ persObj A B w (1 / (m * c)) :=
          persRisk_le hA.le hB.le hf
      _ = A * ((∑ g : Fin m, ((1:ℝ) / 2) ^ (g : ℕ)) * (1 / m ^ 2)) + 8 * A / m ^ 2 := by
          unfold persObj
          rw [Fintype.sum_sigma]
          simp only [hw, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow,
            Nat.cast_ofNat, hsq, ← sum_mul]
          congr 1
          rw [div_pow, mul_pow, hc2]
          field_simp
      _ ≤ A * (2 * (1 / m ^ 2)) + 8 * A / m ^ 2 := by gcongr
      _ = 10 * A / m ^ 2 := by ring
  -- every admissible threshold has risk at least 2A
  have hthr : 2 * A ≤ thrRisk ∅ (budget m A B) A B := by
    apply le_thrRisk
    · refine ⟨c, hc, card_pos.mpr ⟨⟨⟨0, hm⟩, ⟨0, by positivity⟩⟩, ?_⟩⟩
      simp [budget, ← hc_def]
    · intro t ht hN
      set G : Finset (Fin m) := univ.filter fun g => t ≤ c * (1 / 2) ^ (g : ℕ) with hG
      have hfil : (univ.filter fun x : Rec m => x ∈ (∅ : Finset (Rec m)) ∨ t ≤ budget m A B x)
          = G.sigma fun _ => univ := by
        ext ⟨g, j⟩
        simp [hG, budget, ← hc_def]
      have hNG : nThr ∅ (budget m A B) t = ∑ g ∈ G, 2 ^ (g : ℕ) := by
        unfold nThr
        rw [hfil, card_sigma]
        simp
      have hGne : G.Nonempty := by
        rw [nonempty_iff_ne_empty]
        intro h
        rw [hNG, h, sum_empty] at hN
        exact lt_irrefl _ hN
      set g₀ := G.max' hGne
      have hg₀ : t ≤ c * (1 / 2) ^ (g₀ : ℕ) := (mem_filter.mp (G.max'_mem hGne)).2
      have hlt : ∑ g ∈ G, 2 ^ (g : ℕ) < 2 ^ ((g₀ : ℕ) + 1) := by
        have := Nat.geomSum_lt (m := 2) (s := G.map Fin.valEmbedding) (n := (g₀ : ℕ) + 1)
          le_rfl fun k hk => by
            obtain ⟨g, hg, rfl⟩ := mem_map.mp hk
            exact Nat.lt_succ_of_le (Fin.le_iff_val_le_val.mp (G.le_max' g hg))
        rwa [sum_map] at this
      have hNlt : (nThr ∅ (budget m A B) t : ℝ) < 2 * 2 ^ (g₀ : ℕ) := by
        rw [hNG, ← pow_succ']
        exact_mod_cast hlt
      have key : t * nThr ∅ (budget m A B) t < 2 * c :=
        calc t * nThr ∅ (budget m A B) t < t * (2 * 2 ^ (g₀ : ℕ)) :=
              mul_lt_mul_of_pos_left hNlt ht
          _ = 2 * (t * 2 ^ (g₀ : ℕ)) := by ring
          _ ≤ 2 * (c * (1 / 2) ^ (g₀ : ℕ) * 2 ^ (g₀ : ℕ)) := by gcongr
          _ = 2 * c := by rw [mul_assoc, ← mul_pow]; norm_num
      have hNpos : (0:ℝ) < nThr ∅ (budget m A B) t := Nat.cast_pos.mpr hN
      have h1 : B / (2 * c) ^ 2 < B / (t * nThr ∅ (budget m A B) t) ^ 2 :=
        div_lt_div_of_pos_left hB (by positivity)
          (pow_lt_pow_left₀ key (by positivity) two_ne_zero)
      have h2 : B / (2 * c) ^ 2 = 2 * A := by
        rw [mul_pow, hc2]
        field_simp
        ring
      have h3 : 0 ≤ A / (nThr ∅ (budget m A B) t : ℝ) := by positivity
      unfold thrObj
      linarith
  calc (m : ℝ) ^ 2 / 5 * persRisk ∅ (budget m A B) A B
      ≤ (m : ℝ) ^ 2 / 5 * (10 * A / m ^ 2) := mul_le_mul_of_nonneg_left hpers (by positivity)
    _ = 2 * A := by field_simp; ring
    _ ≤ thrRisk ∅ (budget m A B) A B := hthr

/-- The same separation in terms of `n = 2^m − 1`: `𝓡_thr ≥ (log₂(n+1))²/5 · 𝓡_pers`. -/
theorem lower_bound_log (m : ℕ) (hm : 0 < m) {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    Real.logb 2 (Fintype.card (Rec m) + 1) ^ 2 / 5 * persRisk ∅ (budget m A B) A B
      ≤ thrRisk ∅ (budget m A B) A B := by
  have hn : (Fintype.card (Rec m) : ℝ) + 1 = 2 ^ m := by
    rw [card_rec, Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    ring
  rw [hn, Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one]
  exact lower_bound m hm hA hB

end LowerBound

end Limites
