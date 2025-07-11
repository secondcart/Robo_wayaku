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
    **あなた** また証明目標を分解しなきゃいけないの?

    **Robo** いいえ, もっと簡単です. ORの命題を証明するときは, 左側か右側のどちらかを証明すればいいんです.

    **あなた** それで, Formalosophenにどっちを証明したいかどう説明すれば? もちろん`{A}`を証明したいんだけど!

    **Robo** `left`か`right`で. わかりやすいでしょ? "
  Branch
    right
    Hint "**Robo** 左右が苦手だなんて知らなかったわ. もう一度試してみて. "
  left
  assumption

Conclusion
"
このFormalosophenも満足して去っていきました.
"

NewDefinition Or
NewTactic left right
DisabledTactic tauto
