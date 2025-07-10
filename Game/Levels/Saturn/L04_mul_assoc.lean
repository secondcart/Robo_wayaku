import Game.Metadata

World "Saturn"
Level 4

Title ""

Introduction "また無線信号が届いた。"

namespace MvPolynomial

Statement (a b c : MvPolynomial (Fin 4) ℕ ) : a * b * c = a * (b * c) := by
  Hint "**ロボ** ここでは `mul_assoc` を使うといいよ。あるいは *また* `ring` でも…"
  ring

Conclusion "
  またまた 👍 だ。

  **あなた**: でも待って, 今回は係数が `ℕ` だったよね！
  これは環じゃないし, `ℕ` を係数とする多項式も環を成さないよ。

  **ロボ**: そうかもね。でも `ring` は半環と呼ばれるものでも使えるんだ。

  **あなた**: へえ…

  匿名のファンカーは, エンドゲームの準備ができているか, 
  それとも彼の惑星を何周か回りたいか知りたがっている。

  「準備OK」とロボが返信した。
"

NewTactic ring

/---/
TheoremDoc mul_assoc as "mul_assoc" in "+ *"

-- The following theorems are only added for symmetry/completeness:

/---/
TheoremDoc add_comm as "add_comm" in "+ *"

/---/
TheoremDoc add_assoc as "add_assoc" in "+ *"

/---/
TheoremDoc mul_add as "mul_add" in "+ *"

/---/
TheoremDoc add_mul as "add_mul" in "+ *"

NewTheorem mul_assoc add_comm add_assoc mul_add add_mul
