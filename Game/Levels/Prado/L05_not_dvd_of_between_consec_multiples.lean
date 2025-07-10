import Game.Metadata
import Game.Levels.Prado.L04_99


World "Prado"
Level 5

Title ""

Introduction
"**あなた** *(ロボに向かって)*: もっと面白いものをちょうだい！

**ロボ**: これはどうかな？
"

/---/
TheoremDoc Nat.not_dvd_of_between_consec_multiples as "not_dvd_of_between_consec_multiples" in "ℕ"

namespace Nat
Statement not_dvd_of_between_consec_multiples {m n k : ℕ} (h1 : n * k < m) (h2 : m < n * (k + 1)) : ¬n ∣ m := by
  Hint "
  **あなた**: `by_contra`を使う？

  **ロボ**: それでいけるかもしれないね。
  おそらく`lt_of_mul_lt_mul_left`という補題が必要になるだろう。
  `a b c : ℕ`に対して、仮定`a * b < a * c`から`b < c`を導くものだ。
  "
  by_contra h_dvd
  obtain ⟨a, ha⟩ := h_dvd
  rw [ha] at h1 h2
  apply lt_of_mul_lt_mul_left at h1  -- needs to be supplied as a hint
  apply lt_of_mul_lt_mul_left at h2  -- Note: Nat. is necessary here!
  omega

/---/
TheoremDoc lt_of_mul_lt_mul_left as "lt_of_mul_lt_mul_left" in "≤"
/---/
TheoremDoc lt_of_mul_lt_mul_right as "lt_of_mul_lt_mul_right" in "≤"
NewTheorem lt_of_mul_lt_mul_left lt_of_mul_lt_mul_right

TheoremTab "ℕ"
