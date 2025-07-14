import Game.Metadata

World "Logo"
Level 10

Title "かつ"

Introduction
"
次に並んでいるFormalosophが, すでに質問を用意して待っていました.
彼はそれを私たちに提示し, 座って編み物を始めます.
"
/--  -/
Statement (A B : Prop) (hA : A) (hB : B) : A ∧ B := by
  Hint "
    **あなた** ええと, 私たちには2つの前提があります.
    `{A}`が成り立ち, `{B}`も成り立つ. そして証明すべきは
    `{A} かつ {B}`が成り立つことです.
    このFormalosophたちには本当にうんざりする.

    **Robo** 今回は, 証明目標を2つの部分に分ける必要があります.
    `constructor`を試してみてください.

    **あなた** `destructor`ではなく??

    **Robo** いいえ, `constructor`です. 混乱するのはわかりますが,
    ここでは複数の部分から主張を構築できるのでこう呼ばれています. "
  constructor
  -- gleicher Hint wie unten!
  assumption
  Hint (hidden := true) "
    **Robo** 見てください, これは魔法の紙です.
    突然, 2つの証明目標ができました.
    ここにあるのは`{B}`という目標です.
    それぞれの目標を達成する方法はもうわかっていると思います.
    目標はそれぞれ*仮定*の中に書かれています. "
  assumption

Conclusion
"
**Robo** 素晴らしい!

彼はこれらの質問を楽しんでいるようです.

# 今回学んだこと

## Tactics
### constructor
- `constructor`は証明目標を構成要素に分割します.

| 前          | 後                  |
|:------------|:-------------------|
| `⊢ A ∧ B`   | `⊢ A`と`⊢ B`       |
| `⊢ A ↔ B`   | `⊢ A → B`と`⊢ B → A` |

## Definitions
### ∧
- `A ∧ B` は `A` と `B` がともに真である命題.
"

NewDefinition And
NewTactic constructor
DisabledTactic tauto
