import Game.Metadata

World "Logo"
Level 12

Title "Oder"

Introduction
"
次の方どうぞ…
"

Statement (A B : Prop) (hA : A) : A ∨ (¬ B) := by
  Hint "
    **あなた** また証明目標を分解しなきゃいけないの？

    **ロボ** いいえ、もっと簡単です。ORの命題を証明するときは、左側か右側のどちらかを証明すればいいんです。

    **あなた** それで、フォルマロソフにどっちを証明したいかどう説明すれば？もちろん`{A}`を証明したいんだけど！

    **ロボ** `left`か`right`で。道理でしょ？"
  Branch
    right
    Hint "**ロボ** 左右が苦手だなんて知らなかったわ。もう一度試してみて。"
  left
  assumption

Conclusion
"
このフォルマロソフも満足して去っていきました。
"

NewDefinition Or
NewTactic left right
DisabledTactic tauto
