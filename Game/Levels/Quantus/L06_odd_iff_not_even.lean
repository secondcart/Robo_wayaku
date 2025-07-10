import Game.Metadata

World "Quantus"
Level 6

Title ""

Introduction "すぐに次の葉が現れます。
今回は彼らが妥協点を見つけたようです。"

open Nat

Statement (i : ℕ): (-1 : ℤ)^i  + (-1 : ℤ)^(i+1) = 0 := by
  Hint (hidden := true) "
    **あなた**:  iが偶数か奇数かで場合分けしたいと思います。

    **Roboット**:  それではやってみてください。例えば`by_cases h : Even i`で。
  "
  Branch
    by_cases h : Odd i
    swap  -- TODO: check whether this triggers in the correct moment
    Hint "
      **Roboット**:  `odd_iff_not_even`を使えば, `¬Odd`を`Even`に変換できます。
      "
    rw [← even_iff_not_odd] at h
  by_cases h : Even i
  · rw [Even.neg_pow]
    rw [Odd.neg_pow]
    ring
    · obtain ⟨r, hr⟩ := h
      use r
      rw [hr]
      ring
    · assumption
  · Hint "
      **Roboット**:  `odd_iff_not_even`を使えば, `¬Even`を`Odd`に変換できます。
    "
    rw [← odd_iff_not_even] at h
    rw [Odd.neg_pow]
    rw [Even.neg_pow]
    ring
    · obtain ⟨r, hr⟩ := h
      use r+1
      rw [hr]
      ring
    · assumption

/---/
TheoremDoc Nat.even_iff_not_odd as "even_iff_not_odd" in "ℕ"
#check  Nat.even_iff_not_odd

/---/
TheoremDoc Nat.odd_iff_not_even as "odd_iff_not_even" in "ℕ"
-- It seems this has been renamed into `Nat.not_even_iff_odd` in newer versions of mathlib,
-- and is now a simp lemma.

NewTheorem Nat.even_iff_not_odd Nat.odd_iff_not_even

Conclusion "今回はフォルマロソフィストたちを感心させたようです。彼らは感心して頷いています。

そしてまた囁き声が聞こえてきます。"
