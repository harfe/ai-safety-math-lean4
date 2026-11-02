module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic

set_option linter.style.header false

/-!
# The five-test certificate: the real-arithmetic core

For the electorate of `Counterexample.lean`, with voter weights `(10, 10, 10, 1)`, the weighted
sum of five one-sided tests is `≤ -2` at every lottery `A`. This file proves that inequality as a
statement about real numbers (`certF_le`); `CounterexampleProfile.lean` connects it to
`netWinToward`.

* `tw x y p` is the one-sided comparison of a voter with utility `x` for `A` against utility `y`
  for `B`, where `B` moves an infinitesimal step towards a lottery with utility `p`: `1` if the
  voter prefers `A`, `-1` if they prefer `B⁺`, `0` if they are indifferent.
* A lottery is `A = (a, b, c)` on the candidates `(x, y, z)`. The voters
  `u₁ = (1, 0, 0)`, `u₂ = (1, 0, 1)`, `u₃ = (0, 1, ½)`, `u₄ = (0, 0, 1)` have expected
  utilities `a`, `a + c`, `b + c / 2`, `c`. `nwt` is `31 · netWinToward` with weights
  `(10, 10, 10, 1)`.
* The tests `(B, P)` and weights are those of `Counterexample.lean`: `z` towards
  itself (219), `z` towards `(⅓, ⅔, 0)` (12), `p = (½, 0, ½)` towards `z` (165),
  `c = (½, ½, 0)` towards `(0, ¼, ¾)` (17), `x` towards `z` (87).

The proof regroups `certF` by voter (`certF_eq`). Voter `k` contributes a nondecreasing step
function `S k` of their expected utility. Eight cases on `a` and `b` cover the simplex, and in
each one a bound on each `S k` gives `≤ -2`.
-/

@[expose] public section

namespace MaxLotLot.Counterexample

/-- One-sided comparison: utility `x` against `y` moved an infinitesimal step towards `p`. -/
noncomputable def tw (x y p : ℝ) : ℝ :=
  if y < x then 1 else if x < y then -1 else if p < y then 1 else if y < p then -1 else 0

lemma tw_of_gt {x y p : ℝ} (h : y < x) : tw x y p = 1 := by simp [tw, h]

lemma tw_of_lt {x y p : ℝ} (h : x < y) : tw x y p = -1 := by
  simp [tw, h, not_lt.2 h.le]

lemma tw_of_le {x y p : ℝ} (h : x ≤ y) (hp : y < p) : tw x y p = -1 := by
  rcases h.lt_or_eq with h | rfl
  · exact tw_of_lt h
  · simp [tw, hp, not_lt.2 hp.le]

lemma tw_of_ge {x y p : ℝ} (h : y ≤ x) (hp : p < y) : tw x y p = 1 := by
  rcases h.lt_or_eq with h | rfl
  · exact tw_of_gt h
  · simp [tw, hp]

lemma tw_self (y : ℝ) : tw y y y = 0 := by simp [tw]

lemma tw_le_one (x y p : ℝ) : tw x y p ≤ 1 := by
  unfold tw; split_ifs <;> norm_num

/-- `31 · netWinToward V A B P` for the counterexample, with `A = (a, b, c)`, `B = (a', b', c')` and
`P = (p, q, r)`. -/
noncomputable def nwt (a b c a' b' c' p q r : ℝ) : ℝ :=
  10 * tw a a' p + 10 * tw (a + c) (a' + c') (p + r) +
    10 * tw (b + c / 2) (b' + c' / 2) (q + r / 2) + tw c c' r

/-- The certificate `Σ_j q_j · 31 · netWinToward V A B_j P_j`. -/
noncomputable def certF (a b c : ℝ) : ℝ :=
  219 * nwt a b c 0 0 1 0 0 1 + 12 * nwt a b c 0 0 1 (1 / 3) (2 / 3) 0 +
    165 * nwt a b c (1 / 2) 0 (1 / 2) 0 0 1 + 17 * nwt a b c (1 / 2) (1 / 2) 0 0 (1 / 4) (3 / 4) +
    87 * nwt a b c 1 0 0 0 0 1

/-! ### The contribution of each voter -/

/-- Voter `u₁` (utility `a`). -/
noncomputable def S₁ (x : ℝ) : ℝ :=
  219 * tw x 0 0 + 12 * tw x 0 (1 / 3) + 165 * tw x (1 / 2) 0 + 17 * tw x (1 / 2) 0 +
    87 * tw x 1 0

/-- Voter `u₂` (utility `a + c`). -/
noncomputable def S₂ (x : ℝ) : ℝ :=
  219 * tw x 1 1 + 12 * tw x 1 (1 / 3) + 165 * tw x 1 1 + 17 * tw x (1 / 2) (3 / 4) +
    87 * tw x 1 1

/-- Voter `u₃` (utility `b + c / 2`). -/
noncomputable def S₃ (x : ℝ) : ℝ :=
  219 * tw x (1 / 2) (1 / 2) + 12 * tw x (1 / 2) (2 / 3) + 165 * tw x (1 / 4) (1 / 2) +
    17 * tw x (1 / 2) (5 / 8) + 87 * tw x 0 (1 / 2)

/-- Voter `u₄` (utility `c`). -/
noncomputable def S₄ (x : ℝ) : ℝ :=
  219 * tw x 1 1 + 12 * tw x 1 0 + 165 * tw x (1 / 2) 1 + 17 * tw x 0 (3 / 4) + 87 * tw x 0 1

lemma certF_eq (a b c : ℝ) :
    certF a b c = 10 * S₁ a + 10 * S₂ (a + c) + 10 * S₃ (b + c / 2) + S₄ c := by
  simp only [certF, nwt, S₁, S₂, S₃, S₄]
  norm_num
  ring

lemma S₁_zero : S₁ 0 = -281 := by
  rw [S₁, tw_self, tw_of_le le_rfl (by norm_num), tw_of_lt (by norm_num), tw_of_lt (by norm_num)]
  norm_num

lemma S₁_of_pos_of_lt {x : ℝ} (h0 : 0 < x) (h1 : x < 1 / 2) : S₁ x = -38 := by
  rw [S₁, tw_of_gt h0, tw_of_gt h0, tw_of_lt h1, tw_of_lt (by linarith)]
  norm_num

lemma S₁_of_le_of_lt {x : ℝ} (h0 : 1 / 2 ≤ x) (h1 : x < 1) : S₁ x = 326 := by
  rw [S₁, tw_of_gt (by linarith), tw_of_gt (by linarith), tw_of_ge h0 (by norm_num), tw_of_lt h1]
  norm_num

lemma S₁_le (x : ℝ) : S₁ x ≤ 500 := by
  have := tw_le_one x 0 0; have := tw_le_one x 0 (1 / 3); have := tw_le_one x (1 / 2) 0
  have := tw_le_one x 1 0
  rw [S₁]; linarith

lemma S₂_one : S₂ 1 = 29 := by
  rw [S₂, tw_self, tw_of_ge le_rfl (by norm_num), tw_of_gt (by norm_num)]
  norm_num

lemma S₂_of_le {x : ℝ} (h : x ≤ 1 / 2) : S₂ x = -500 := by
  rw [S₂, tw_of_lt (by linarith), tw_of_lt (by linarith), tw_of_le h (by norm_num)]
  norm_num

lemma S₂_of_lt {x : ℝ} (h : x < 1) : S₂ x ≤ -466 := by
  rcases le_or_gt x (1 / 2) with h' | h'
  · rw [S₂_of_le h']; norm_num
  · rw [S₂, tw_of_lt h, tw_of_lt h, tw_of_gt h']
    norm_num

lemma S₃_le (x : ℝ) : S₃ x ≤ 500 := by
  have := tw_le_one x (1 / 2) (1 / 2); have := tw_le_one x (1 / 2) (2 / 3)
  have := tw_le_one x (1 / 4) (1 / 2); have := tw_le_one x (1 / 2) (5 / 8)
  have := tw_le_one x 0 (1 / 2)
  rw [S₃]; linarith

lemma S₃_of_nonpos {x : ℝ} (h : x ≤ 0) : S₃ x = -500 := by
  rw [S₃, tw_of_lt (by linarith), tw_of_lt (by linarith), tw_of_lt (by linarith),
    tw_of_lt (by linarith), tw_of_le h (by norm_num)]
  norm_num

lemma S₃_of_le_quarter {x : ℝ} (h : x ≤ 1 / 4) : S₃ x ≤ -326 := by
  have := tw_le_one x 0 (1 / 2)
  rw [S₃, tw_of_lt (by linarith), tw_of_lt (by linarith), tw_of_le h (by norm_num),
    tw_of_lt (by linarith)]
  linarith

lemma S₃_of_lt_half {x : ℝ} (h : x < 1 / 2) : S₃ x ≤ 4 := by
  rcases le_or_gt x (1 / 4) with h' | h'
  · linarith [S₃_of_le_quarter h']
  · rw [S₃, tw_of_lt h, tw_of_lt h, tw_of_gt h', tw_of_lt h, tw_of_gt (by linarith)]
    norm_num

lemma S₃_half : S₃ (1 / 2) = 223 := by
  rw [S₃, tw_self, tw_of_le le_rfl (by norm_num), tw_of_gt (by norm_num),
    tw_of_le le_rfl (by norm_num), tw_of_gt (by norm_num)]
  norm_num

lemma S₄_le {x : ℝ} (h : x ≤ 1) : S₄ x ≤ 281 := by
  have := tw_le_one x (1 / 2) 1; have := tw_le_one x 0 (3 / 4); have := tw_le_one x 0 1
  rcases h.lt_or_eq with h | rfl
  · rw [S₄, tw_of_lt h, tw_of_lt h]; linarith
  · rw [S₄, tw_self, tw_of_ge le_rfl (by norm_num)]; linarith

lemma S₄_of_lt {x : ℝ} (h : x < 1) : S₄ x ≤ 38 := by
  have := tw_le_one x (1 / 2) 1; have := tw_le_one x 0 (3 / 4); have := tw_le_one x 0 1
  rw [S₄, tw_of_lt h, tw_of_lt h]; linarith

lemma S₄_of_le_half {x : ℝ} (h : x ≤ 1 / 2) : S₄ x ≤ -292 := by
  have := tw_le_one x 0 (3 / 4); have := tw_le_one x 0 1
  rw [S₄, tw_of_lt (by linarith), tw_of_lt (by linarith), tw_of_le h (by norm_num)]
  linarith

lemma S₄_of_nonpos {x : ℝ} (h : x ≤ 0) : S₄ x = -500 := by
  rw [S₄, tw_of_lt (by linarith), tw_of_lt (by linarith), tw_of_lt (by linarith),
    tw_of_le h (by norm_num), tw_of_le h (by norm_num)]
  norm_num

/-! ### The bound -/

/-- The certificate is `≤ -2` at every lottery `(a, b, c)`. -/
theorem certF_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a + b + c = 1) :
    certF a b c ≤ -2 := by
  rw [certF_eq]
  rcases hb.eq_or_lt with rfl | hb
  · -- `b = 0`: the edge `xz`, voter `u₂` gets utility `1`
    have h2 : a + c = 1 := by linarith
    rw [h2, S₂_one]
    rcases ha.eq_or_lt with rfl | ha
    · -- `A = z`
      obtain rfl : c = 1 := by linarith
      have h3 : (0 : ℝ) + 1 / 2 = 1 / 2 := by norm_num
      rw [S₁_zero, h3, S₃_half]; linarith [S₄_le le_rfl]
    rcases lt_or_ge a (1 / 2) with ha' | ha'
    · rw [S₁_of_pos_of_lt ha ha']
      linarith [S₃_of_lt_half (x := 0 + c / 2) (by linarith), S₄_of_lt (x := c) (by linarith)]
    rcases lt_or_ge a 1 with ha'' | ha''
    · rw [S₁_of_le_of_lt ha' ha'']
      linarith [S₃_of_le_quarter (x := 0 + c / 2) (by linarith),
        S₄_of_le_half (x := c) (by linarith)]
    · -- `A = x`
      linarith [S₁_le a, S₃_of_nonpos (x := 0 + c / 2) (by linarith),
        S₄_of_nonpos (x := c) (by linarith)]
  · -- `b > 0`: voter `u₂` gets utility `< 1`
    have h2 := S₂_of_lt (x := a + c) (by linarith)
    rcases ha.eq_or_lt with rfl | ha
    · linarith [S₁_zero, S₃_le (b + c / 2), S₄_le (x := c) (by linarith)]
    rcases lt_or_ge a (1 / 2) with ha' | ha'
    · rw [S₁_of_pos_of_lt ha ha']
      linarith [S₃_le (b + c / 2), S₄_of_lt (x := c) (by linarith)]
    rw [S₁_of_le_of_lt ha' (by linarith)]
    rcases lt_or_ge b a with hba | hab
    · linarith [S₃_of_lt_half (x := b + c / 2) (by linarith),
        S₄_of_le_half (x := c) (by linarith)]
    · -- `A = (½, ½, 0)`
      obtain rfl : c = 0 := by linarith
      obtain rfl : a = 1 / 2 := by linarith
      obtain rfl : b = 1 / 2 := by linarith
      have h3 : (1 / 2 : ℝ) + 0 / 2 = 1 / 2 := by norm_num
      rw [add_zero, S₂_of_le le_rfl, h3, S₃_half, S₄_of_nonpos le_rfl]
      norm_num

end MaxLotLot.Counterexample
