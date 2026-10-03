import Mathlib

/-!
# Personalized and threshold risks (Definition `def:generic-risks`)

Records are indexed by a fintype `ι`.  Public records (budget `+∞`) form a
finset `pub`; every other record `i` has a finite budget `u i`.

* `persRisk pub u A B` is `𝓡_pers(u; A, B)` of Eq. `eq:generic-pers`: the
  infimum of `A ∑ wᵢ² + B M²` over weights `w ≥ 0` with `∑ w = 1` and noise
  levels `M ≥ 0` with `wᵢ ≤ M uᵢ` for every non-public `i`.  This is the
  paper's infimum with `M = maxᵢ wᵢ/uᵢ` (the objective is increasing in `M`).
* `thrRisk pub u A B` is `𝓡_thr(u; A, B)` of Eq. `eq:generic-thr`: the
  infimum over thresholds `t > 0` with `n_t ≥ 1` of `A/n_t + B/(t n_t)²`, where
  `n_t` counts the public records and those with `uᵢ ≥ t`.

The mean-estimation risks `MSE_aff`, `MSE_thr` (Eqs. `eq:mseafftedious`,
`eq:msethr`) are the instance `A = 1/4`, `B = 2`; the DP-SGD oracle MSEs of
Section `sec:learning-formal` are the instance `A = V(θ)`, `B = 2dC²`.

The scaling lemmas `persRisk_scale`, `thrRisk_scale` are shared by Lemma
`lem:reduction` (Part 2) and Lemma `lem:budget-scaling`.
-/

open Finset Pointwise

namespace Limites

variable {ι : Type*} [Fintype ι]

/-- Personalized objective `A ∑ wᵢ² + B M²`. -/
noncomputable def persObj (A B : ℝ) (w : ι → ℝ) (M : ℝ) : ℝ :=
  A * ∑ i, w i ^ 2 + B * M ^ 2

/-- Threshold objective `A/N + B/(t N)²` at a threshold `t` retaining `N` records. -/
noncomputable def thrObj (A B t N : ℝ) : ℝ :=
  A / N + B / (t * N) ^ 2

/-- `(w, M)` is a feasible personalized mechanism for the budgets `u`. -/
def Feasible (pub : Finset ι) (u w : ι → ℝ) (M : ℝ) : Prop :=
  (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ 0 ≤ M ∧ ∀ i ∉ pub, w i ≤ M * u i

lemma persObj_nonneg {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (w : ι → ℝ) (M : ℝ) :
    0 ≤ persObj A B w M := by
  unfold persObj
  positivity

lemma thrObj_nonneg {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (t : ℝ) (N : ℕ) :
    0 ≤ thrObj A B t N := by
  unfold thrObj
  positivity

variable [DecidableEq ι]

/-- `n_t`: number of records retained by the threshold `t`. -/
noncomputable def nThr (pub : Finset ι) (u : ι → ℝ) (t : ℝ) : ℕ :=
  #{i | i ∈ pub ∨ t ≤ u i}

/-- Values of the personalized objective over feasible mechanisms. -/
def persSet (pub : Finset ι) (u : ι → ℝ) (A B : ℝ) : Set ℝ :=
  {r | ∃ w M, Feasible pub u w M ∧ persObj A B w M = r}

/-- Values of the threshold objective over admissible thresholds. -/
def thrSet (pub : Finset ι) (u : ι → ℝ) (A B : ℝ) : Set ℝ :=
  {r | ∃ t, 0 < t ∧ 0 < nThr pub u t ∧ thrObj A B t (nThr pub u t) = r}

/-- `𝓡_pers(u; A, B)`, Eq. `eq:generic-pers`. -/
noncomputable def persRisk (pub : Finset ι) (u : ι → ℝ) (A B : ℝ) : ℝ :=
  sInf (persSet pub u A B)

/-- `𝓡_thr(u; A, B)`, Eq. `eq:generic-thr`. -/
noncomputable def thrRisk (pub : Finset ι) (u : ι → ℝ) (A B : ℝ) : ℝ :=
  sInf (thrSet pub u A B)

/-! ## Basic facts about the infima -/

section Basic

variable {pub : Finset ι} {u : ι → ℝ} {A B : ℝ}

omit [DecidableEq ι] in
lemma persRisk_nonneg (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ persRisk pub u A B :=
  Real.sInf_nonneg (by rintro _ ⟨w, M, -, rfl⟩; exact persObj_nonneg hA hB w M)

omit [DecidableEq ι] in
lemma persRisk_le (hA : 0 ≤ A) (hB : 0 ≤ B) {w : ι → ℝ} {M : ℝ}
    (h : Feasible pub u w M) : persRisk pub u A B ≤ persObj A B w M :=
  csInf_le ⟨0, by rintro _ ⟨w, M, -, rfl⟩; exact persObj_nonneg hA hB w M⟩ ⟨w, M, h, rfl⟩

lemma thrRisk_le (hA : 0 ≤ A) (hB : 0 ≤ B) {t : ℝ} (ht : 0 < t)
    (hN : 0 < nThr pub u t) : thrRisk pub u A B ≤ thrObj A B t (nThr pub u t) :=
  csInf_le ⟨0, by rintro _ ⟨t, -, -, rfl⟩; exact thrObj_nonneg hA hB t _⟩ ⟨t, ht, hN, rfl⟩

lemma le_thrRisk {c : ℝ} (hne : ∃ t, 0 < t ∧ 0 < nThr pub u t)
    (h : ∀ t, 0 < t → 0 < nThr pub u t → c ≤ thrObj A B t (nThr pub u t)) :
    c ≤ thrRisk pub u A B := by
  obtain ⟨t, ht, hN⟩ := hne
  exact le_csInf ⟨_, t, ht, hN, rfl⟩ (by rintro _ ⟨t, ht, hN, rfl⟩; exact h t ht hN)

/-- To bound `𝓡_thr ≤ k 𝓡_pers` it suffices to bound `𝓡_thr` by `k` times the
objective of every feasible mechanism. -/
lemma thrRisk_le_mul_persRisk {k : ℝ} (hk : 0 < k) (hne : ∃ w M, Feasible pub u w M)
    (h : ∀ w M, Feasible pub u w M → thrRisk pub u A B ≤ k * persObj A B w M) :
    thrRisk pub u A B ≤ k * persRisk pub u A B := by
  obtain ⟨w, M, hf⟩ := hne
  rw [← div_le_iff₀' hk]
  exact le_csInf ⟨_, w, M, hf, rfl⟩
    (by rintro _ ⟨w, M, hf, rfl⟩; rw [div_le_iff₀' hk]; exact h w M hf)

omit [DecidableEq ι] in
/-- Uniform weights with a large enough noise level are feasible. -/
lemma feasible_nonempty [Nonempty ι] (hu : ∀ i ∉ pub, 0 < u i) :
    ∃ w M, Feasible pub u w M := by
  classical
  set n : ℝ := (Fintype.card ι : ℝ)
  have hn : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  have hterm : ∀ i ∈ univ.filter (· ∉ pub), 0 ≤ 1 / (n * u i) := fun i hi =>
    (one_div_pos.mpr (mul_pos hn (hu i (mem_filter.mp hi).2))).le
  refine ⟨fun _ => 1 / n, ∑ i ∈ univ.filter (· ∉ pub), 1 / (n * u i),
    fun _ => by positivity, ?_, sum_nonneg hterm, fun i hi => ?_⟩
  · rw [sum_const, card_univ, nsmul_eq_mul, mul_one_div_cancel hn.ne']
  · have hle := single_le_sum hterm (mem_filter.mpr ⟨mem_univ i, hi⟩)
    have hui := hu i hi
    calc 1 / n = 1 / (n * u i) * u i := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hle hui.le

end Basic

/-! ## Change of variables

Multiplying the budgets by `c > 0` and both constants by `k > 0`:
`𝓡(c u; kA, kB) = k 𝓡(u; A, B/c²)`, for both risks. -/

lemma nThr_mul (pub : Finset ι) (u : ι → ℝ) {c : ℝ} (hc : 0 < c) (t : ℝ) :
    nThr pub (fun i => c * u i) t = nThr pub u (t / c) := by
  unfold nThr
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, div_le_iff₀' hc]

omit [DecidableEq ι] in
theorem persRisk_scale (pub : Finset ι) (u : ι → ℝ) (A B : ℝ) {c k : ℝ}
    (hc : 0 < c) (hk : 0 < k) :
    persRisk pub (fun i => c * u i) (k * A) (k * B) = k * persRisk pub u A (B / c ^ 2) := by
  have hset : persSet pub (fun i => c * u i) (k * A) (k * B)
      = k • persSet pub u A (B / c ^ 2) := by
    ext r
    simp only [Set.mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨w, M, ⟨hw, hsum, hM0, hM⟩, rfl⟩
      refine ⟨persObj A (B / c ^ 2) w (c * M),
        ⟨w, c * M, ⟨hw, hsum, by positivity, fun i hi => ?_⟩, rfl⟩, ?_⟩
      · linarith [hM i hi, show M * (c * u i) = c * M * u i by ring]
      · unfold persObj; field_simp
    · rintro ⟨_, ⟨w, M, ⟨hw, hsum, hM0, hM⟩, rfl⟩, rfl⟩
      refine ⟨w, M / c, ⟨hw, hsum, by positivity, fun i hi => ?_⟩, ?_⟩
      · have : M / c * (c * u i) = M * u i := by field_simp
        linarith [hM i hi]
      · unfold persObj; field_simp
  rw [persRisk, hset, Real.sInf_smul_of_nonneg hk.le, smul_eq_mul, persRisk]

theorem thrRisk_scale (pub : Finset ι) (u : ι → ℝ) (A B : ℝ) {c k : ℝ}
    (hc : 0 < c) (hk : 0 < k) :
    thrRisk pub (fun i => c * u i) (k * A) (k * B) = k * thrRisk pub u A (B / c ^ 2) := by
  have hset : thrSet pub (fun i => c * u i) (k * A) (k * B)
      = k • thrSet pub u A (B / c ^ 2) := by
    ext r
    simp only [Set.mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨t, ht, hN, rfl⟩
      rw [nThr_mul pub u hc] at hN ⊢
      refine ⟨_, ⟨t / c, by positivity, hN, rfl⟩, ?_⟩
      have hN' : (0:ℝ) < nThr pub u (t / c) := Nat.cast_pos.mpr hN
      unfold thrObj; field_simp
    · rintro ⟨_, ⟨s, hs, hN, rfl⟩, rfl⟩
      have hcs : c * s / c = s := by field_simp
      refine ⟨c * s, by positivity, by rwa [nThr_mul pub u hc, hcs], ?_⟩
      rw [nThr_mul pub u hc, hcs]
      have hN' : (0:ℝ) < nThr pub u s := Nat.cast_pos.mpr hN
      unfold thrObj; field_simp
  rw [thrRisk, hset, Real.sInf_smul_of_nonneg hk.le, smul_eq_mul, thrRisk]

end Limites
