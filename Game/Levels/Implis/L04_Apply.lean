import Game.Metadata

World "Implis"
Level 4

Title "Implikation"

Introduction
"
**作戦責任者**: これはまたローカルな問題になりました。
"

Statement (A B C : Prop) (f : A → B) (g : B → C) : A → C := by
  Hint "
    **あなた**: 含意 $A \\Rightarrow B \\Rightarrow C$ を $A \\Rightarrow C$ に結合する必要がある？

    **Robo**: また `intro` から始めてみたら？"
  intro h
  Hint "
    **作戦責任者**: 私はこの時点でまず `have hB : B` と記録しておくね。

    **Robo**: 私の好みから言うと少し余計だな。
    まあ, やってもいいけど。

    **Robo** *(あなたへ)*: さあ, やってみて！
  "
  have hB : B := by
    Hint "
    **Robo**: まずは `B` を証明できるね…
  "
    apply f
    assumption
  Hint "
      **Robo**: …それができたら, `{hB} : {B}` が仮定として使えるよ。
  "
  apply g
  assumption

Conclusion "**作戦責任者**: 君たちは本当にすごい！"

NewTactic «have»  -- introduced here already so that Luna becomes independent of Spinoza
DisabledTactic tauto
