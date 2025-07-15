import Game.Metadata

World "Saturn"
Level 2

Title ""

Introduction "次の無線信号は少し違って見える. "

namespace MvPolynomial

Statement (x y : ℚ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  Hint "**あなた** ここは匿名の学校数学の場ですか?
  項を並べ替えて計算するだけです.
  `binomi`と返信する必要があるのでしょうか?

  **Robo** いいえ, この宇宙ではこの等式は当然`add_pow_two`と呼ばれます.
  式には最初に「+」, 次に「^2」が来るからです.
  ですから`rw [add_pow_two]`を使うことができます.
  その後, 左辺は右辺と完全に同じに見え, 完了です. "
  Branch
    ring
  rw [add_pow_two]

Conclusion "
  👍が返ってきました.

  **Robo** ただし, 単に`ring`と言うこともできたでしょう.
  "

NewTactic ring

/---/
TheoremDoc add_pow_two as "add_pow_two" in "+ *"

NewTheorem add_pow_two
