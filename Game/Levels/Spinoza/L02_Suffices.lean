import Game.Metadata


World "Spinoza"
Level 2

Title ""

Introduction
"
**Benedictus** もちろん, 最初に主結果を証明してから中間結果を証明することもできたでしょう. この問題で試してみてください, とても似ていますよ.
"

Statement
    (A B : Prop) (h : A → ¬ B) (k₁ : A) (k₂ : B) : False := by
  Hint "
    **Robo** 彼の言っていることがわかります!  `have`の代わりに`suffices`を使うこともできます.
    同じように機能しますが, 2つの証明目標が入れ替わります.

    **あなた** つまり, `suffices g : ¬B`の後, まず`g`を使って証明を完了する方法を示し,
    その後で`g`を証明するのですか?

    **Robo** その通りです! "
  suffices g : ¬ B
  Hint "**Robo** ここでは, `{g}`が真であると仮定して証明を完了します. "
  contradiction
  Hint "**Robo** そしてここで中間結果を証明します. "
  apply h
  assumption

Conclusion
"
**Benedictus** まさにその通りです. 今後`have`と`suffices`のどちらを使うかは
完全に好みの問題です. 重要なのは, 遠い目標を小さなステップで達成する方法を知っていることです.
"

NewTactic «suffices»
DisabledTactic «have» tauto
