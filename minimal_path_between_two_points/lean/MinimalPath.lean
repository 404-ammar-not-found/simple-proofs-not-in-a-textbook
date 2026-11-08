/-
Lean 4 / Mathlib formalization of
"The Shortest Path Between Two Points Is a Straight Line, Over Any Ordered Field".

Mathlib's `Field F` + `LinearOrder F` + `IsStrictOrderedRing F` is exactly the paper's
ordered field (axioms F1–F5, O1–O4); Sections 2–3 of the paper are Mathlib lemmas.

A path is `p : ℕ → (Fin n → F)` with `k` steps, from `p 0` to `p k`;
step `i` is `p (i+1) - p i`, and `ℓ i` is its length.
-/
import Mathlib

open Finset

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] {n : ℕ}

/-- Dot product. -/
def dot (x y : Fin n → F) : F := ∑ i, x i * y i

/-- Squared length `‖x‖²` (Definition 3.3). -/
def nsq (x : Fin n → F) : F := dot x x

/-- `ℓ` is a length of `x` (Definition 4.2). -/
def IsLength (ℓ : F) (x : Fin n → F) : Prop := 0 ≤ ℓ ∧ ℓ ^ 2 = nsq x

/-- Point `i` lies on the segment between its neighbours (Definition 5.1). -/
def Redundant (p : ℕ → Fin n → F) (i : ℕ) : Prop :=
  ∃ μ : F, 0 ≤ μ ∧ μ ≤ 1 ∧ p i = p (i - 1) + μ • (p (i + 1) - p (i - 1))

/-! ### Lemma 3.4 -/

lemma nsq_nonneg (x : Fin n → F) : 0 ≤ nsq x :=
  show 0 ≤ ∑ i, x i * x i from sum_nonneg fun i _ => mul_self_nonneg (x i)

lemma nsq_eq_zero {x : Fin n → F} : nsq x = 0 ↔ x = 0 := by
  constructor
  · intro h
    change ∑ i, x i * x i = 0 at h
    funext i
    have := (sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg (x i)).1 h i (mem_univ _)
    simpa using this
  · rintro rfl
    simp [nsq, dot]

/-! ### Lemma 4.3: lengths are unique -/

lemma IsLength.unique {l m : F} {x : Fin n → F} (hl : IsLength l x) (hm : IsLength m x) :
    l = m := by
  have h := hl.2.trans hm.2.symm
  nlinarith [hl.1, hm.1]

/-! ### Equation (1) -/

lemma nsq_sum {ι : Type*} (s : Finset ι) (v : ι → Fin n → F) :
    nsq (∑ i ∈ s, v i) = ∑ i ∈ s, ∑ j ∈ s, dot (v i) (v j) := by
  simp only [nsq, dot, Finset.sum_apply, sum_mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_comm

/-! ### Lemma 4.4: Cauchy–Schwarz, without square roots -/

lemma nsq_combo (α β : F) (x y : Fin n → F) :
    nsq (β • x - α • y) = β ^ 2 * nsq x - 2 * α * β * dot x y + α ^ 2 * nsq y := by
  simp only [nsq, dot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sum,
    ← sum_sub_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun i _ => by ring

theorem cauchy_schwarz {α β : F} {x y : Fin n → F} (hx : IsLength α x) (hy : IsLength β y) :
    dot x y ≤ α * β ∧ (dot x y = α * β ↔ β • x = α • y) := by
  rcases hx.1.eq_or_lt with hα | hα
  · have : x = 0 := nsq_eq_zero.1 (by rw [← hx.2, ← hα]; ring)
    subst this
    simp [dot, ← hα]
  rcases hy.1.eq_or_lt with hβ | hβ
  · have : y = 0 := nsq_eq_zero.1 (by rw [← hy.2, ← hβ]; ring)
    subst this
    simp [dot, ← hβ]
  have key : nsq (β • x - α • y) = 2 * α * β * (α * β - dot x y) := by
    rw [nsq_combo, ← hx.2, ← hy.2]; ring
  have hpos : 0 < 2 * α * β := by positivity
  refine ⟨?_, ?_⟩
  · have := nsq_nonneg (β • x - α • y)
    rw [key] at this
    nlinarith
  · rw [← sub_eq_zero (a := β • x), ← nsq_eq_zero, key, mul_eq_zero, sub_eq_zero]
    simp [hpos.ne', eq_comm]

/-! ### Theorem 5.2 (main theorem) -/

section Main

variable {k : ℕ} {p : ℕ → Fin n → F} {ℓ : ℕ → F}

/-- Equation (2): the gap `L² - ‖b - a‖²` as a double sum. -/
lemma gap :
    (∑ i ∈ range k, ℓ i) ^ 2 - nsq (p k - p 0) =
      ∑ i ∈ range k, ∑ j ∈ range k, (ℓ i * ℓ j - dot (p (i + 1) - p i) (p (j + 1) - p j)) := by
  rw [← sum_range_sub p k, nsq_sum, sq, sum_mul_sum]
  simp only [← sum_sub_distrib]

lemma term_nonneg (hℓ : ∀ i < k, IsLength (ℓ i) (p (i + 1) - p i)) {i j : ℕ}
    (hi : i < k) (hj : j < k) :
    0 ≤ ℓ i * ℓ j - dot (p (i + 1) - p i) (p (j + 1) - p j) :=
  sub_nonneg.2 (cauchy_schwarz (hℓ i hi) (hℓ j hj)).1

lemma L_nonneg (hℓ : ∀ i < k, IsLength (ℓ i) (p (i + 1) - p i)) :
    0 ≤ ∑ i ∈ range k, ℓ i :=
  sum_nonneg fun i hi => (hℓ i (mem_range.1 hi)).1

/-- Theorem 5.2 (i), first part: `L² ≥ ‖b - a‖²`. -/
theorem main_i (hℓ : ∀ i < k, IsLength (ℓ i) (p (i + 1) - p i)) :
    nsq (p k - p 0) ≤ (∑ i ∈ range k, ℓ i) ^ 2 := by
  have : 0 ≤ (∑ i ∈ range k, ℓ i) ^ 2 - nsq (p k - p 0) := by
    rw [gap]
    exact sum_nonneg fun i hi => sum_nonneg fun j hj =>
      term_nonneg hℓ (mem_range.1 hi) (mem_range.1 hj)
  linarith

/-- Theorem 5.2 (i), second part: `L ≥ |b - a|` when `|b - a|` exists. -/
theorem main_i' (hℓ : ∀ i < k, IsLength (ℓ i) (p (i + 1) - p i)) {d : F}
    (hd : IsLength d (p k - p 0)) : d ≤ ∑ i ∈ range k, ℓ i := by
  have h1 := main_i hℓ
  have h2 := L_nonneg hℓ
  rw [← hd.2] at h1
  nlinarith [hd.1]

/-- Theorem 5.2 (ii): with no redundant points, `L² = ‖b - a‖²` iff `P = (a, b)`. -/
theorem main_ii (hk : 1 ≤ k) (hℓ : ∀ i < k, IsLength (ℓ i) (p (i + 1) - p i))
    (hnr : ∀ i, 0 < i → i < k → ¬ Redundant p i) :
    (∑ i ∈ range k, ℓ i) ^ 2 = nsq (p k - p 0) ↔ k = 1 := by
  constructor
  swap
  · rintro rfl
    simpa using (hℓ 0 one_pos).2
  intro hL
  by_contra hk1
  have hk2 : 2 ≤ k := by omega
  -- every term of the gap sum vanishes; in particular the (0, 1) term
  have hzero : (∑ i ∈ range k, ∑ j ∈ range k,
      (ℓ i * ℓ j - dot (p (i + 1) - p i) (p (j + 1) - p j))) = 0 := by
    rw [← gap, hL, sub_self]
  have h01 : ℓ 0 * ℓ 1 - dot (p 1 - p 0) (p 2 - p 1) = 0 := by
    have hrow := (sum_eq_zero_iff_of_nonneg fun i hi => sum_nonneg fun j hj =>
      term_nonneg hℓ (mem_range.1 hi) (mem_range.1 hj)).1 hzero 0 (mem_range.2 (by omega))
    exact (sum_eq_zero_iff_of_nonneg fun j hj =>
      term_nonneg hℓ (by omega) (mem_range.1 hj)).1 hrow 1 (mem_range.2 (by omega))
  have heq : ℓ 1 • (p 1 - p 0) = ℓ 0 • (p 2 - p 1) :=
    ((cauchy_schwarz (hℓ 0 (by omega)) (hℓ 1 (by omega))).2).1 (by linarith)
  -- so p 1 is redundant
  apply hnr 1 one_pos (by omega)
  have h0 := (hℓ 0 (by omega)).1
  have h1 := (hℓ 1 (by omega)).1
  rcases (add_nonneg h0 h1).eq_or_lt with hs | hs
  · -- ℓ 0 = ℓ 1 = 0, so p 1 = p 0
    have hl0 : ℓ 0 = 0 := by linarith
    have hv : p 1 - p 0 = 0 := nsq_eq_zero.1 (by
      have := (hℓ 0 (by omega)).2; simp only [zero_add] at this; rw [← this, hl0]; ring)
    refine ⟨0, le_rfl, zero_le_one, ?_⟩
    simpa [sub_eq_zero] using hv
  · refine ⟨ℓ 0 / (ℓ 0 + ℓ 1), div_nonneg h0 hs.le, by rw [div_le_iff₀ hs]; linarith, ?_⟩
    funext c
    have := congrFun heq c
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul] at this ⊢
    field_simp
    linear_combination this

/-- Consequence of Theorem 5.2: the straight line has length `|b - a|`, and every other
path with a length and no redundant points is strictly longer. -/
theorem main_consequence (hk : 1 ≤ k) (hℓ : ∀ i < k, IsLength (ℓ i) (p (i + 1) - p i))
    (hnr : ∀ i, 0 < i → i < k → ¬ Redundant p i) {d : F} (hd : IsLength d (p k - p 0)) :
    (k = 1 → ∑ i ∈ range k, ℓ i = d) ∧ (k ≠ 1 → d < ∑ i ∈ range k, ℓ i) := by
  refine ⟨?_, fun hk1 => lt_of_le_of_ne (main_i' hℓ hd) fun h => hk1 ?_⟩
  · rintro rfl
    simpa using (hℓ 0 one_pos).unique hd
  · exact (main_ii hk hℓ hnr).1 (by rw [← h, hd.2])

end Main

/-! ### Proposition 6.1: in ℚ² there is no shortest path from (0,0) to (1,1)

The paper's Step 4 uses Pell numbers to get rationals whose squares approach 2;
here we take them from the density of ℚ in ℝ instead. -/

theorem no_shortest {k : ℕ} {p : ℕ → Fin 2 → ℚ} {ℓ : ℕ → ℚ}
    (ha : p 0 = 0) (hb : p k = ![1, 1])
    (hℓ : ∀ i < k, IsLength (ℓ i) (p (i + 1) - p i)) :
    ∃ (k' : ℕ) (q : ℕ → Fin 2 → ℚ) (m : ℕ → ℚ),
      q 0 = 0 ∧ q k' = ![1, 1] ∧ (∀ i < k', IsLength (m i) (q (i + 1) - q i)) ∧
      ∑ i ∈ range k', m i < ∑ i ∈ range k, ℓ i := by
  set L := ∑ i ∈ range k, ℓ i
  have hL0 : 0 ≤ L := L_nonneg hℓ
  have hL2 : 2 ≤ L ^ 2 := by
    have := main_i hℓ
    rw [ha, hb] at this
    simpa [nsq, dot, Fin.sum_univ_two, one_add_one_eq_two] using this
  -- Step 1–2: L² ≠ 2, since √2 is irrational
  have hLne : L ^ 2 ≠ 2 := by
    intro h
    apply irrational_sqrt_two
    refine ⟨L, ?_⟩
    rw [← Real.sqrt_sq (by exact_mod_cast hL0 : (0 : ℝ) ≤ L)]
    congr 1
    exact_mod_cast h
  set ε := L ^ 2 - 2
  have hε : 0 < ε := by
    have := lt_of_le_of_ne hL2 (Ne.symm hLne)
    simp only [ε]; linarith
  -- Step 4 (replaced): a rational s with 2 < s² < 2 + min 1 (ε/2)
  set η : ℚ := min 1 (ε / 2)
  have hη : 0 < η := lt_min one_pos (by linarith)
  obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn
    (Real.sqrt_lt_sqrt (by norm_num) (by linarith [(by exact_mod_cast hη : (0 : ℝ) < η)]) :
      √(2 : ℝ) < √(2 + (η : ℝ)))
  have hs0 : (0 : ℝ) < s := lt_of_le_of_lt (Real.sqrt_nonneg _) hs1
  have hsq_lo : (2 : ℝ) < (s : ℝ) ^ 2 := (Real.sqrt_lt' hs0).1 hs1
  have hsq_hi : (s : ℝ) ^ 2 < 2 + η := (Real.lt_sqrt hs0.le).1 hs2
  have hlo : 2 < s ^ 2 := by exact_mod_cast hsq_lo
  have hhi : s ^ 2 < 2 + η := by exact_mod_cast hsq_hi
  have hspos : 0 < s := by exact_mod_cast hs0
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : η ≤ ε / 2 := min_le_right _ _
  -- Step 3: the two-step path through c
  set t := s - 1
  have ht0 : 0 < t := by simp only [t]; nlinarith
  have ht1 : t < 1 := by simp only [t]; nlinarith
  set D := 1 + 2 * t - t ^ 2
  have hD : 1 < D := by simp only [D]; nlinarith
  have hD0 : D ≠ 0 := by linarith
  set m := (1 + t ^ 2) / D
  have hm0 : 0 ≤ m := div_nonneg (by positivity) (by linarith)
  let c : Fin 2 → ℚ := ![(1 - t ^ 2) / D, 2 * t / D]
  let q : ℕ → Fin 2 → ℚ := fun i => if i = 0 then 0 else if i = 1 then c else ![1, 1]
  refine ⟨2, q, fun _ => m, rfl, rfl, ?_, ?_⟩
  · intro i hi
    refine ⟨hm0, ?_⟩
    interval_cases i <;>
      simp [q, c, m, nsq, dot, Fin.sum_univ_two] <;> field_simp <;> ring
  · -- (2m)² = 2 + 2u²/D² with u = s² - 2, and 2u²/D² ≤ 2u² ≤ 2u < ε
    simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_ofNat]
    set u := s ^ 2 - 2
    have hsq : (2 * m) ^ 2 = 2 + 2 * u ^ 2 / D ^ 2 := by
      simp only [m, u, t]; field_simp; ring
    have hdiv : 2 * u ^ 2 / D ^ 2 ≤ 2 * u ^ 2 :=
      div_le_self (by positivity) (by nlinarith)
    have hu0 : 0 < u := by simp only [u]; linarith
    have hu1 : u < η := by simp only [u]; linarith
    have : (2 * m) ^ 2 < L ^ 2 := by
      have : 2 * u ^ 2 ≤ 2 * u := by nlinarith
      simp only [ε] at hηε
      linarith
    nlinarith
