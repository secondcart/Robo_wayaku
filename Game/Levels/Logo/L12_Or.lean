import Game.Metadata

World "Logo"
Level 12

Title "または"

Introduction
"
次の方どうぞ…
"

Statement (A B : Prop) (hA : A) : A ∨ (¬ B) := by
  Hint "
    **あなた** また証明目標を分解しなきゃいけないの?

    **Robo** いいえ, もっと簡単です. ORの命題を証明するときは, 左側か右側のどちらかを証明すればいいんです.

    **あなた** それで, Formalosophにどっちを証明したいかどう説明すれば? もちろん`{A}`を証明したいんだけど!

    **Robo** `left`か`right`で. わかりやすいでしょ? "
  Branch
    right
    Hint "**Robo** 左右が苦手だなんて知らなかった. もう一度試してみて. "
  left
  assumption

Conclusion
"
このFormalosophも満足して去っていきました.

# 今回学んだこと

## Tactics
### left
- 証明目標が `A ∨ B` の場合, `left` で左側を示すことを選択します.
### right
- 証明目標が `A ∨ B` の場合, `right` で右側を示すことを選択します.

## Definitions
### ∨
- `A ∨ B` は `A` または `B` の少なくとも一方が真である命題.
"

NewDefinition Or
NewTactic left right
DisabledTactic tauto
