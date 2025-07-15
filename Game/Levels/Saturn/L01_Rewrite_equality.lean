import Game.Metadata

World "Saturn"
Level 1

Title ""

Introduction "突然, 無線通信が届いた. "

Statement (a b c d : ℝ) (h₁ : c = d) (h₂ : a = b) (h₃ : a = d) : b = c := by
  Hint "**あなた**: これ, 前に見たことがあるような気がする.

  **Robo** そうだね! これは*Implis*で解いた問題に似ているよ.
  ただ, 今回は「ならば」の代わりに数値の等式があるだけだ!
  でも根本的には何も変わらない.
  `=`と`↔`は`rw`でほぼ同じように扱えるよ. "

  Hint (hidden := true) "**あなた** つまり`rw [hₓ]`や`rw [← hₓ]`も使える?

  **Robo** 試してみたらどうかな. "
  rw [h₁]
  Hint (hidden := true) "**あなた** 逆向きの書き換えはどうするんだっけ?

  **Robo** `←`は`\\l`だよ. そして`rw [← hₓ]`と書くんだ"
  rw [←h₂]
  assumption

Conclusion "
  👍が返ってきた.
  "
