import Game.Metadata
import Game.Levels.Prado.L06_Prime_Specialize__prime_def


World "Prado"
Level 7

Title ""

Introduction  "
  **ロボ**: ここにもう一つ小さな素数問題があります。
  補題`Prime.dvd_mul`は、素数が積を割り切るのは、その素数のいずれかの因数を割り切るときだけだと言っています。ここではそれを適用するだけです。
  "

namespace Nat

Statement (a b : ℕ) : 5 ∣ (a * b) ↔  5 ∣ a ∨ 5 ∣ b := by
  rw [Prime.dvd_mul]
  decide

/---/
TheoremDoc Nat.Prime.dvd_mul as "Prime.dvd_mul" in "ℕ"
NewTheorem Nat.Prime.dvd_mul

TheoremTab "ℕ"

Conclusion "**あなた**: 本当に非常に簡単な問題ばかり出しますね。"
