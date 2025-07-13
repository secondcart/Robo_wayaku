import Game.Metadata


World "Logo"
Level 1

Title "Logisinde女王からの問い"

Introduction
"
今あなたは女王**Logisinde**の惑星にいます. 彼女は前置きなしに本題に入ります.

**Logisinde** 異世界からの尊き客人よ, ひとつ質問をさせてください. なぜ…ということが成り立つのでしょう?

そして彼女は紙切れに何かを走り書きします. 上部にいくつかの仮定, 下部に結論.
その間にあなたは証明を記入する必要があるようです.
あなたはRoboを困った様子で見ます.
"

/--  -/
Statement (A B C : Prop) :
    ¬((¬B ∨ ¬ C) ∨ (A → B)) → (¬A ∨ B) ∧ ¬ (B ∧ C) := by
  Hint "
  **Robo** これはとても簡単です. 最初の`{A} {B} {C} : Prop`というのは,
    `{A}`, `{B}`, `{C}`は任意の命題(*propositions*)という意味です.
    そして`→`は`⇒`, つまり「ならば」を意味します. 他の記号は知ってるよね?

    **あなた** えーと, はい. でもそれでもちょっと考えないと.

    **Robo** (小声で) これはトートロジーだと言っちゃえばいいよ.

    **あなた** 本当に?

    **Robo** はい. ただ`tauto`と書くだけ.

    **Robo** さあやってみて…"
  tauto

Conclusion
"
**Logisinde** (少し当惑して) ええ, 確かに正しいです.
でも*この*惑星ではそれでうまくいくと思わないでください!
私の家臣は`tauto`を理解しません. もっと努力が必要ですよ.

# 今回学んだこと

## Tactics
### tauto
- トートロジーを証明する.

## Definition
### Prop
- 命題
"

NewDefinition «Prop»

TheoremTab "Logic"
NewTactic tauto
